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
from tests.util import random_cnf

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
        rng = random.Random(4242)
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
        rng = random.Random(31337)
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
        rng = random.Random(4)
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

        rng = random.Random(99)
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
