# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The native search core, held to the plan's Tier 1 and Tier 2 criteria.

**Tier 1 (never negotiable):** verdicts match the brute-force oracle and the
Python solver; every SAT answer's model satisfies the formula.

**Tier 2 (while the port is intentionally faithful):** conflict counts are
*identical* to the Python solver, not merely similar. That is a bit-exact
comparison, and it is what catches the class of bug verdict agreement hides —
a mis-ordered watch list, a different heap tie-break, an off-by-one in an LBD.
When a design change from `PLAN.md` §7 lands, the affected expectations get
retired deliberately, in the same commit, with the reason recorded.

Skipped wholesale when the native module is not built, so the dependency-free
path stays green.
"""

from __future__ import annotations

import random
import unittest

from cdclkit import native
from cdclkit.brute import exhaustive_solve
from dratify.cnf import CNF
from dratify.lits import mk_lit
from cdclkit.solver import Config, Solver
from tests.util import random_cnf, fuzz_seed

requires_native = unittest.skipUnless(
    native.available(), "native engine not built for this interpreter")


def php(holes: int) -> CNF:
    pigeons = holes + 1
    f = CNF()
    x = [[f.new_var() for _ in range(holes)] for _ in range(pigeons)]
    for i in range(pigeons):
        f.add([mk_lit(x[i][j]) for j in range(holes)])
    for j in range(holes):
        for i in range(pigeons):
            for k in range(i + 1, pigeons):
                f.add([mk_lit(x[i][j], True), mk_lit(x[k][j], True)])
    return f


def native_solver(f: CNF, cfg: Config | None = None):
    """Build a native solver mirroring a Python `Config`, and load `f`."""
    n = native.require()
    cfg = cfg or Config()
    s = n.Solver(
        f.nvars,
        restart=cfg.restart, ccmin=cfg.ccmin,
        phase_saving=cfg.phase_saving, init_phase=cfg.init_phase,
        var_decay=cfg.var_decay, var_decay_max=cfg.var_decay_max,
        cla_decay=cfg.cla_decay, luby_base=float(cfg.luby_base),
        first_reduce=cfg.first_reduce, reduce_inc=cfg.reduce_inc,
        glue_keep=cfg.glue_keep, block_restart=cfg.block_restart,
    )
    ok = True
    for c in f.clauses:
        if not s.add_clause(list(c)):
            ok = False
            break
    return s, ok


@requires_native
class TestTier1Correctness(unittest.TestCase):
    def test_verdicts_match_brute_force(self):
        rng = random.Random(fuzz_seed(4242))
        sat = unsat = 0
        for _ in range(150):
            f = random_cnf(rng, max_vars=10, ratio=4.6)
            ref = exhaustive_solve(f)
            s, ok = native_solver(f)
            got = s.solve() if ok else False
            self.assertEqual(bool(got), ref is not None, f.to_dimacs())
            if got:
                sat += 1
                self.assertTrue(f.is_satisfied_by(s.model), "invalid model")
            else:
                unsat += 1
        self.assertGreater(sat, 20)
        self.assertGreater(unsat, 20)

    def test_models_cover_every_variable(self):
        f = CNF(8)
        f.add([mk_lit(0), mk_lit(1)])
        s, _ = native_solver(f)
        self.assertTrue(s.solve())
        self.assertEqual(len(s.model), f.nvars)

    def test_watch_invariant_holds_after_solving(self):
        for holes in (4, 5, 6):
            f = php(holes)
            s, ok = native_solver(f)
            self.assertFalse(s.solve() if ok else False)
            self.assertEqual(s.check_watch_invariant(), [])

    def test_trivial_contradiction(self):
        f = CNF(1)
        f.add([mk_lit(0)])
        f.add([mk_lit(0, True)])
        s, ok = native_solver(f)
        self.assertFalse(s.solve() if ok else False)

    def test_empty_formula_is_satisfiable(self):
        s, ok = native_solver(CNF(3))
        self.assertTrue(ok)
        self.assertTrue(s.solve())

    def test_conflict_budget_returns_none(self):
        f = php(9)
        s, ok = native_solver(f)
        self.assertTrue(ok)
        self.assertIsNone(s.solve(max_conflicts=20))


@requires_native
class TestDefaultsAgree(unittest.TestCase):
    """The no-argument constructors of the two engines must be the same solver.

    The same defaults live in three places -- `Config()` in cdclkit/solver.py,
    `Config::default()` in native/src/solver.rs, and the `#[pyo3(signature)]`
    on the binding -- and nothing in either type system ties them together.

    This is not hypothetical. When the default changed to Luby restarts with
    target phases, the pyo3 signature kept the old values, so every caller that
    omitted an argument got a different search than the one the project ships.
    The Tier 2 test below caught it only because it happens to compare against
    Python; this asserts the property directly.
    """

    def test_native_defaults_match_python_defaults(self):
        from cdclkit.solver import Solver as PySolver

        n = native.require()
        # an instance with enough search to expose a policy difference
        f = php(6)

        py = PySolver(f.nvars, config=Config())
        py.add_cnf(f)
        py_res = py.solve()

        rs = n.Solver(f.nvars)  # deliberately no keyword arguments
        for c in f.clauses:
            rs.add_clause(list(c))
        rs_res = rs.solve(None)

        self.assertEqual(bool(py_res), bool(rs_res))
        self.assertEqual(
            py.stats.conflicts, rs.conflicts,
            "the native engine's argument-free defaults do not reproduce "
            "Config() from cdclkit/solver.py -- the pyo3 signature has drifted "
            "from Config::default() or from the Python default"
        )
        self.assertEqual(py.stats.decisions, rs.decisions)
        self.assertEqual(py.stats.propagations, rs.propagations)


def rand3(n: int, ratio: float, seed: int) -> CNF:
    """Uniform random 3-SAT, generated here so the instance is reproducible."""
    import random

    rng = random.Random(seed)
    f = CNF()
    f.new_vars(n)
    for _ in range(int(n * ratio)):
        vs = rng.sample(range(1, n + 1), 3)
        f.add_dimacs([v if rng.random() < 0.5 else -v for v in vs])
    return f


@requires_native
class TestAgreementWhereItWasNeverChecked(unittest.TestCase):
    """The engines must still agree once the expensive machinery switches on.

    Every other bit-exactness test here runs instances that peak around 748
    conflicts. The defaults turn clause-database reduction on at 2,000
    conflicts, local-search rephasing at 5,000, and restart blocking at
    10,000 -- so none of that code was ever compared between the two engines,
    despite being the part where a divergence is most likely and hardest to
    spot.

    This instance crosses all three. It costs a couple of seconds, which is
    the price of the claim meaning anything.
    """

    #: n=205 at ratio 4.35, seed 6: unsatisfiable, ~13,000 conflicts, and the
    #: cheapest instance found that exercises reduction, rephasing and
    #: blocking together.
    N, RATIO, SEED = 205, 4.35, 6

    @classmethod
    def setUpClass(cls):
        from cdclkit.solver import Solver as PySolver

        cls.f = rand3(cls.N, cls.RATIO, cls.SEED)
        d = Config()
        py = PySolver(cls.f.nvars, config=d)
        py.add_cnf(cls.f)
        cls.py_sat = py.solve()
        cls.py = py.stats

        n = native.require()
        rs = n.Solver(
            cls.f.nvars, restart=d.restart, ccmin=d.ccmin,
            phase_saving=d.phase_saving, init_phase=d.init_phase,
            target_phase=d.target_phase, target_reset=d.target_reset,
            walk_flips=d.walk_flips, walk_interval=d.walk_interval,
            walk_patience=d.walk_patience,
            walk_min_conflicts=d.walk_min_conflicts,
            var_decay=d.var_decay, var_decay_max=d.var_decay_max,
            cla_decay=d.cla_decay, luby_base=float(d.luby_base),
            first_reduce=d.first_reduce, reduce_inc=d.reduce_inc,
            glue_keep=d.glue_keep, block_restart=d.block_restart,
            rnd_freq=d.rnd_freq, rnd_seed=d.rnd_seed)
        for c in cls.f.clauses:
            rs.add_clause(list(c))
        cls.rs_sat = rs.solve(None)
        cls.rs = rs

    def test_the_instance_really_crosses_every_threshold(self):
        """Otherwise this whole class could pass while testing nothing.

        If a default moves and the instance stops reaching one of these, the
        suite must say so rather than quietly going back to covering only the
        easy path.
        """
        d = Config()
        self.assertGreater(self.py.conflicts, 10_000)
        self.assertGreater(self.py.conflicts, d.first_reduce)
        self.assertGreater(self.py.conflicts, d.walk_min_conflicts)
        self.assertGreater(self.py.reductions, 0, "clause reduction never ran")
        self.assertGreater(self.py.walks, 0, "rephasing never ran")
        self.assertGreater(self.py.blocked_restarts, 0,
                           "restart blocking never engaged")

    def test_verdicts_agree(self):
        self.assertEqual(bool(self.py_sat), bool(self.rs_sat))

    def test_every_exposed_counter_agrees(self):
        for name in ("conflicts", "decisions", "propagations", "restarts",
                     "learned", "minimized_lits", "reductions",
                     "blocked_restarts", "learned_lits", "deleted",
                     "max_trail"):
            with self.subTest(counter=name):
                self.assertEqual(getattr(self.py, name), getattr(self.rs, name),
                                 f"{name} diverged once reduction, rephasing "
                                 f"and blocking were all active")


@requires_native
class TestRandomBranchingAgrees(unittest.TestCase):
    """`rnd_freq` and `rnd_seed` must reach the native engine and match.

    These two knobs had no Rust counterpart at all: the native side accepted
    the rest of the configuration and silently dropped these, so a Python run
    at rnd_freq=0.02 took 4,987 conflicts where the native one took 3,171.

    That was not a cosmetic gap. `portfolio.py` builds worker diversity from
    exactly these two fields, and sets a per-worker seed specifically "so
    duplicated recipes still diverge" -- which on the native path they did not,
    because every worker got the same search. Duplicate recipes became
    bit-identical duplicate workers doing the same work in parallel.

    The existing bit-exactness tests could not have caught this: none of them
    set either knob.
    """

    def _native(self, f, rnd_freq, rnd_seed):
        n = native.require()
        d = Config()
        rs = n.Solver(
            f.nvars, restart=d.restart, ccmin=d.ccmin,
            phase_saving=d.phase_saving, init_phase=d.init_phase,
            target_phase=d.target_phase, target_reset=d.target_reset,
            walk_flips=d.walk_flips, walk_interval=d.walk_interval,
            walk_patience=d.walk_patience,
            walk_min_conflicts=d.walk_min_conflicts,
            var_decay=d.var_decay, var_decay_max=d.var_decay_max,
            cla_decay=d.cla_decay, luby_base=float(d.luby_base),
            first_reduce=d.first_reduce, reduce_inc=d.reduce_inc,
            glue_keep=d.glue_keep, block_restart=d.block_restart,
            rnd_freq=rnd_freq, rnd_seed=rnd_seed)
        for c in f.clauses:
            rs.add_clause(list(c))
        rs.solve(None)
        return rs.conflicts, rs.decisions, rs.propagations

    def _python(self, f, rnd_freq, rnd_seed):
        from cdclkit.solver import Solver as PySolver

        cfg = Config()
        cfg.rnd_freq = rnd_freq
        cfg.rnd_seed = rnd_seed
        py = PySolver(f.nvars, config=cfg)
        py.add_cnf(f)
        py.solve()
        return py.stats.conflicts, py.stats.decisions, py.stats.propagations

    def test_engines_agree_across_frequencies_and_seeds(self):
        f = php(6)
        for freq, seed in [(0.0, 91648253), (0.02, 91648253), (0.02, 12345),
                           (0.10, 7), (0.05, 999983)]:
            with self.subTest(rnd_freq=freq, rnd_seed=seed):
                self.assertEqual(
                    self._python(f, freq, seed), self._native(f, freq, seed),
                    f"engines diverge at rnd_freq={freq}, rnd_seed={seed}")

    def test_a_zero_frequency_does_not_touch_the_random_stream(self):
        """The short-circuit is load-bearing, not an optimisation.

        Python tests `rnd_freq > 0.0` before drawing, so the default
        configuration never advances the PRNG. If the native side drew first,
        the walk -- which shares the stream -- would desynchronise and the two
        engines would diverge on instances long enough to reach it.
        """
        f = php(6)
        self.assertEqual(self._python(f, 0.0, 91648253),
                         self._native(f, 0.0, 91648253))

    def test_the_seed_actually_changes_the_search(self):
        """A knob that is wired up but inert would pass the tests above."""
        f = php(6)
        runs = {self._native(f, 0.05, seed) for seed in (1, 7, 12345, 999983)}
        self.assertGreater(len(runs), 1,
                           "every seed produced an identical search, so the "
                           "seed is not reaching the engine")


@requires_native
class TestTier2Faithfulness(unittest.TestCase):
    """Bit-exact agreement with the Python solver."""

    CONFIGS = {
        "default": Config(),
        "luby": Config(restart="luby"),
        "no-restart": Config(restart="none"),
        "no-ccmin": Config(ccmin="none"),
        "no-phase": Config(phase_saving=False),
    }

    def _compare(self, f: CNF, cfg: Config, label: str):
        p = Solver(f.nvars, config=cfg)
        p.add_cnf(f)
        py = p.solve()

        s, ok = native_solver(f, cfg)
        rs = s.solve() if ok else False

        self.assertEqual(bool(py), bool(rs), f"{label}: verdicts differ")
        self.assertEqual(
            p.stats.conflicts, s.conflicts,
            f"{label}: conflicts differ (python {p.stats.conflicts}, "
            f"native {s.conflicts}) -- the port is no longer faithful",
        )
        return p.stats.conflicts

    def test_identical_conflicts_across_every_configuration(self):
        from cdclkit.cli import gen_php, gen_random_ksat

        instances = [
            ("php(6)", gen_php(7, 6)),
            ("rand3(150)", gen_random_ksat(150, 639, 3, 1)),
        ]
        for label, f in instances:
            for name, cfg in self.CONFIGS.items():
                with self.subTest(instance=label, config=name):
                    self._compare(f, cfg, f"{label}/{name}")

    def test_identical_conflicts_on_random_instances(self):
        rng = random.Random(fuzz_seed(31337))
        compared = 0
        for _ in range(40):
            f = random_cnf(rng, max_vars=14, ratio=4.4)
            self._compare(f, Config(), "random")
            compared += 1
        self.assertGreater(compared, 20)

    def test_decisions_and_propagations_also_match(self):
        """Conflicts matching while decisions do not would mean the two are
        taking different paths to the same count -- coincidence, not
        faithfulness."""
        from cdclkit.cli import gen_random_ksat

        f = gen_random_ksat(150, 639, 3, 1)
        p = Solver(f.nvars)
        p.add_cnf(f)
        p.solve()
        s, _ = native_solver(f)
        s.solve()
        self.assertEqual(p.stats.conflicts, s.conflicts)
        self.assertEqual(p.stats.decisions, s.decisions)
        self.assertEqual(p.stats.propagations, s.propagations)
        self.assertEqual(p.stats.restarts, s.restarts)

    def test_root_simplification_is_reproduced(self):
        """A formula with many root units exercises `simplify`, which was the
        last source of divergence: without it the counts differ on any
        instance that restarts."""
        f = CNF(40)
        for v in range(20):
            f.add([mk_lit(v)])
        rng = random.Random(fuzz_seed(4))
        for _ in range(200):
            vs = rng.sample(range(40), 3)
            f.add([mk_lit(v, rng.random() < 0.5) for v in vs])
        self._compare(f, Config(), "root-units")


@requires_native
class TestProofEmission(unittest.TestCase):
    """Tier 1: every UNSAT answer must come with a checkable proof.

    An engine that answers UNSAT and offers no certificate fails the property
    this whole project exists to demonstrate, so the native engine is held to
    the same standard as the Python one -- and checked by the *same* Python
    checker, which shares no code with it.
    """

    def _proof(self, f: CNF):
        """Solve with proof logging on.  It must be enabled before any clause
        is added, so this cannot reuse `native_solver`."""
        from dratify.lits import from_dimacs

        n = native.require()
        s = n.Solver(f.nvars)
        s.enable_proof()
        loaded = True
        for c in f.clauses:
            if not s.add_clause(list(c)):
                loaded = False
                break
        res = s.solve() if loaded else False
        steps = [(k, tuple(from_dimacs(d) for d in lits))
                 for k, lits in s.proof_steps()]
        return res, steps

    def test_pigeonhole_proofs_verify(self):
        from dratify.proof import check_proof

        for holes in (4, 5, 6):
            with self.subTest(holes=holes):
                f = php(holes)
                res, steps = self._proof(f)
                self.assertFalse(res)
                self.assertGreater(len(steps), 0)
                r = check_proof(f, steps)
                self.assertTrue(r.ok, r.report())

    def test_random_unsat_proofs_verify(self):
        from dratify.proof import check_proof

        rng = random.Random(fuzz_seed(99))
        checked = 0
        for _ in range(80):
            f = random_cnf(rng, max_vars=10, ratio=5.2)
            if exhaustive_solve(f) is not None:
                continue
            res, steps = self._proof(f)
            self.assertFalse(res)
            r = check_proof(f, steps)
            self.assertTrue(r.ok, r.report() + "\n" + f.to_dimacs())
            checked += 1
        self.assertGreater(checked, 10)

    def test_proof_step_count_matches_python(self):
        """More faithfulness evidence: the two engines learn and delete the
        same clauses in the same order, so their proofs are the same length."""
        from dratify.proof import MemoryProof

        f = php(6)
        proof = MemoryProof()
        p = Solver(f.nvars, proof=proof)
        p.add_cnf(f)
        self.assertFalse(p.solve())

        _, steps = self._proof(f)
        self.assertEqual(len(steps), len(proof.steps))

    def test_enable_proof_after_solving_is_rejected(self):
        f = php(3)
        s, _ = native_solver(f)
        s.solve()
        with self.assertRaises(ValueError):
            s.enable_proof()

    def test_no_proof_collected_when_disabled(self):
        f = php(4)
        s, ok = native_solver(f)
        self.assertFalse(s.solve() if ok else False)
        self.assertEqual(s.proof_steps(), [])


@requires_native
class TestPerformance(unittest.TestCase):
    def test_native_is_substantially_faster(self):
        """A loose floor, not a benchmark: this only has to catch a build that
        accidentally ships the debug profile."""
        import time

        from cdclkit.cli import gen_php

        f = gen_php(8, 7)
        p = Solver(f.nvars)
        p.add_cnf(f)
        t0 = time.perf_counter()
        p.solve()
        py = time.perf_counter() - t0

        s, _ = native_solver(f)
        t0 = time.perf_counter()
        s.solve()
        rs = time.perf_counter() - t0

        self.assertLess(rs, py, "native must not be slower than Python")
        self.assertGreater(py / rs, 3.0, f"only {py/rs:.1f}x -- debug build?")


if __name__ == "__main__":
    unittest.main()
