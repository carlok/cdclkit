# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Parallel portfolio: correctness, safety, and the properties that let it be
trusted while nobody is watching.

Three classes of test here, and the middle one is the reason this file is
longer than the feature deserves:

1. **Answers.** The portfolio must agree with the sequential solver and with
   the brute-force oracle, its models must satisfy the formula, and the
   winner's DRAT proof must verify standalone.
2. **Process safety.** Multiprocessing failure modes are hangs and process
   explosions, not exceptions. Both were hit while building this. They get
   regression tests.
3. **Non-interference.** Adding a parallel path must not change the default
   sequential behaviour that the rest of the suite and `bench/baseline.json`
   depend on.
"""

from __future__ import annotations

import os
import random
import unittest

from cdclkit.brute import exhaustive_solve
from dratify.cnf import CNF
from dratify.lits import mk_lit
from cdclkit.portfolio import (
    PortfolioResult,
    default_configs,
    in_worker,
    performance_cores,
    solve_portfolio,
    usable_start_method,
)
from dratify.proof import check_proof
from cdclkit.solver import Config, Solver
from tests.util import random_cnf, fuzz_seed


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


class TestAnswers(unittest.TestCase):
    def test_agrees_with_brute_force(self):
        rng = random.Random(fuzz_seed(5))
        sat = unsat = 0
        for _ in range(12):
            f = random_cnf(rng, max_vars=9, ratio=4.5)
            ref = exhaustive_solve(f)
            r = solve_portfolio(f, jobs=2)
            self.assertTrue(r.finished)
            self.assertEqual(r.sat, ref is not None, f.to_dimacs())
            if r.sat:
                sat += 1
                self.assertTrue(f.is_satisfied_by(r.model), "invalid model")
            else:
                unsat += 1
        self.assertGreater(sat, 1)
        self.assertGreater(unsat, 1)

    def test_winner_proof_verifies_standalone(self):
        """No clause sharing means the winner's proof is a complete refutation
        of the original formula on its own -- the property that would be lost
        if workers exchanged learnt clauses."""
        f = php(5)
        r = solve_portfolio(f, jobs=3, want_proof=True)
        self.assertFalse(r.sat)
        self.assertIsNotNone(r.proof_steps)
        res = check_proof(f, r.proof_steps)
        self.assertTrue(res.ok, res.report())

    def test_model_covers_every_variable(self):
        f = CNF(6)
        f.add([mk_lit(0), mk_lit(1)])
        f.add([mk_lit(2)])
        r = solve_portfolio(f, jobs=2)
        self.assertTrue(r.sat)
        self.assertEqual(len(r.model), f.nvars)

    def test_trivially_unsat_formula(self):
        f = CNF(1)
        f.add([mk_lit(0)])
        f.add([mk_lit(0, True)])
        r = solve_portfolio(f, jobs=2)
        self.assertFalse(r.sat)


class TestProcessSafety(unittest.TestCase):
    """Regressions for the two failure modes hit while building this."""

    def test_worker_reentry_collapses_to_sequential(self):
        """A process already marked as a worker must never fan out again.

        Without this, a caller who omits `if __name__ == "__main__":` gets
        their script re-executed in every spawned child, each of which starts
        its own portfolio: a fork bomb rather than an error.
        """
        f = CNF(4)
        f.add([mk_lit(0), mk_lit(1)])
        previous = os.environ.get("CDCLKIT_PORTFOLIO_WORKER")
        os.environ["CDCLKIT_PORTFOLIO_WORKER"] = "1"
        try:
            self.assertTrue(in_worker())
            r = solve_portfolio(f, jobs=8)
            self.assertEqual(r.jobs, 1, "a worker must not spawn more workers")
            self.assertTrue(r.finished)
        finally:
            if previous is None:
                os.environ.pop("CDCLKIT_PORTFOLIO_WORKER", None)
            else:
                os.environ["CDCLKIT_PORTFOLIO_WORKER"] = previous
        self.assertFalse(in_worker(), "the marker must not leak into the parent")

    def test_start_method_is_chosen_not_assumed(self):
        """`spawn` re-imports `__main__`; when that is not importable every
        child dies at startup.  The selector must notice rather than let a
        pool respawn corpses forever."""
        method = usable_start_method()
        self.assertIn(method, ("spawn", "fork", "forkserver", None))

    def test_no_processes_leak(self):
        """Every worker must be reaped, win or lose."""
        import multiprocessing

        before = len(multiprocessing.active_children())
        solve_portfolio(php(4), jobs=4)
        after = len(multiprocessing.active_children())
        self.assertEqual(after, before, "portfolio leaked live children")

    def test_repeated_runs_do_not_accumulate(self):
        import multiprocessing

        for _ in range(3):
            solve_portfolio(php(3), jobs=2)
        self.assertEqual(len(multiprocessing.active_children()), 0)


class TestEngineSelection(unittest.TestCase):
    """The portfolio can run native workers; correctness must not depend on it."""

    def test_python_and_native_engines_agree(self):
        rng = random.Random(fuzz_seed(13))
        for _ in range(15):
            f = random_cnf(rng, max_vars=9, ratio=4.8)
            a = solve_portfolio(f, jobs=2, engine="python")
            b = solve_portfolio(f, jobs=2, engine="native")
            self.assertEqual(a.sat, b.sat, f.to_dimacs())
            for r in (a, b):
                if r.sat:
                    self.assertTrue(f.is_satisfied_by(r.model))

    def test_unknown_engine_is_rejected(self):
        with self.assertRaises(ValueError):
            solve_portfolio(php(3), jobs=2, engine="quantum")

    def test_native_engine_falls_back_when_absent(self):
        """Asking for native on an interpreter without the module must work."""
        from cdclkit import native

        f = php(4)
        r = solve_portfolio(f, jobs=2, engine="native")
        self.assertTrue(r.finished)
        self.assertFalse(r.sat)
        self.assertIn(r.engine, ("native", "native-threads", "python"))
        if native.available():
            self.assertEqual(
                r.engine, "native-threads",
                "with the module present the threaded path should be taken: "
                "processes cost ~60 ms of startup that threads do not")
        else:
            self.assertEqual(r.engine, "python")

    def test_threaded_path_produces_a_verifiable_proof(self):
        """The fastest configuration must also be a certifying one.

        Each thread carries its own DRAT buffer and the winner's is returned.
        Because threads share no clauses that buffer is already a complete
        standalone refutation -- which is what the no-sharing decision bought.
        """
        from cdclkit import native

        for holes in (4, 5):
            f = php(holes)
            r = solve_portfolio(f, jobs=3, want_proof=True)
            self.assertFalse(r.sat)
            self.assertIsNotNone(r.proof_steps,
                                 "an UNSAT answer must carry a proof")
            self.assertTrue(check_proof(f, r.proof_steps).ok,
                            "the winning thread's proof must verify standalone")
            if native.available():
                self.assertEqual(r.engine, "native-threads")

    def test_proof_runs_use_plain_configurations(self):
        """A preprocessing thread solves the reduced formula, so its proof
        would refute that rather than what the caller passed in. Proof runs
        must therefore not use preprocessing threads, whichever path is taken."""
        f = php(5)
        r = solve_portfolio(f, jobs=4, want_proof=True, preprocess_workers=3)
        self.assertFalse(r.sat)
        self.assertTrue(check_proof(f, r.proof_steps).ok,
                        "the proof must refute the ORIGINAL formula")

    def test_threaded_preprocessing_reconstructs_models(self):
        """A thread solving the preprocessed copy returns a model of the
        *reduced* formula; the caller must reconstruct before handing it back."""
        from cdclkit import native

        if not native.available():
            self.skipTest("native engine not built")
        rng = random.Random(fuzz_seed(77))
        checked = 0
        for _ in range(20):
            f = random_cnf(rng, max_vars=10, ratio=4.5)
            r = solve_portfolio(f, jobs=4, engine="native", preprocess_workers=2)
            self.assertTrue(r.finished)
            if r.sat:
                checked += 1
                self.assertEqual(len(r.model), f.nvars)
                self.assertTrue(
                    f.is_satisfied_by(r.model),
                    "a preprocessing thread returned an unreconstructed model\n"
                    + f.to_dimacs())
        self.assertGreater(checked, 3)

    def test_preprocessing_workers_produce_valid_models(self):
        """A preprocessing worker solves a *reduced* formula, so it has to
        reconstruct before returning -- otherwise it hands back a model with
        eliminated variables missing or wrong."""
        rng = random.Random(fuzz_seed(21))
        checked = 0
        for _ in range(15):
            f = random_cnf(rng, max_vars=10, ratio=4.5)
            r = solve_portfolio(f, jobs=3, engine="python", preprocess_workers=2)
            self.assertTrue(r.finished)
            if r.sat:
                checked += 1
                self.assertEqual(len(r.model), f.nvars)
                self.assertTrue(
                    f.is_satisfied_by(r.model),
                    "a preprocessing worker returned a model of the reduced "
                    f"formula rather than the original\n{f.to_dimacs()}")
        self.assertGreater(checked, 2)

    def test_proof_runs_disable_preprocessing_workers(self):
        """A preprocessing worker cannot produce a self-contained proof of the
        original formula, so asking for a proof must silently fall back to
        plain configurations rather than returning an unverifiable one."""
        from dratify.proof import check_proof

        f = php(5)
        r = solve_portfolio(f, jobs=3, want_proof=True, preprocess_workers=2)
        self.assertFalse(r.sat)
        self.assertIsNotNone(r.proof_steps)
        self.assertTrue(check_proof(f, r.proof_steps).ok)


class TestNonInterference(unittest.TestCase):
    def test_jobs_1_is_the_sequential_solver(self):
        """jobs=1 runs in-process with the default Config, so it must match a
        plain Solver exactly -- conflicts included.  This is what keeps
        bench/baseline.json meaningful."""
        f = php(5)
        r = solve_portfolio(f, jobs=1)

        s = Solver(f.nvars)
        s.add_cnf(f)
        sequential = s.solve()

        self.assertEqual(r.sat, bool(sequential))
        self.assertEqual(r.stats["conflicts"], s.stats.conflicts)
        self.assertEqual(r.stats["decisions"], s.stats.decisions)
        self.assertEqual(r.stats["propagations"], s.stats.propagations)

    def test_jobs_1_uses_no_multiprocessing(self):
        import multiprocessing

        solve_portfolio(php(3), jobs=1)
        self.assertEqual(len(multiprocessing.active_children()), 0)

    def test_first_config_is_the_plain_default(self):
        cfgs = default_configs(4)
        default = Config()
        for key in ("restart", "ccmin", "phase_saving", "var_decay"):
            self.assertEqual(getattr(cfgs[0], key), getattr(default, key))


class TestConfiguration(unittest.TestCase):
    def test_configs_are_actually_distinct(self):
        """Diversity is the entire mechanism; duplicated configurations would
        make extra workers pure overhead."""
        cfgs = default_configs(8)
        signatures = {
            (c.restart, c.ccmin, c.phase_saving, c.init_phase,
             round(c.var_decay, 3), round(c.rnd_freq, 3), c.luby_base)
            for c in cfgs
        }
        self.assertGreaterEqual(len(signatures), 6, "too many near-duplicates")
        self.assertEqual(len({c.rnd_seed for c in cfgs}), 8, "seeds must differ")

    def test_more_configs_than_recipes_still_works(self):
        cfgs = default_configs(30)
        self.assertEqual(len(cfgs), 30)
        self.assertEqual(len({c.rnd_seed for c in cfgs}), 30)

    def test_performance_cores_is_sane(self):
        n = performance_cores()
        self.assertGreaterEqual(n, 1)
        self.assertLessEqual(n, (os.cpu_count() or 1))

    def test_explicit_configs_are_respected(self):
        f = php(4)
        r = solve_portfolio(f, configs=[Config(restart="luby")], jobs=1)
        self.assertEqual(r.jobs, 1)
        self.assertEqual(r.winner_config.restart, "luby")

    def test_result_report_is_readable(self):
        r = solve_portfolio(php(3), jobs=2)
        text = r.report()
        self.assertIn("portfolio", text)
        self.assertIn("UNSATISFIABLE", text)


if __name__ == "__main__":
    unittest.main()
