# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The adaptive preprocess-or-not policy.

The properties that matter are correctness ones -- preprocessing changes the
model space, so a pipeline that preprocesses must reconstruct correctly or it
will confidently return an assignment that does not satisfy the user's formula.
Performance is measured in `bench/`, not asserted here; the only timing-shaped
test is that the policy actually *decides* rather than always doing the same
thing.
"""

from __future__ import annotations

import random
import unittest

from cdclkit import native
from cdclkit.brute import exhaustive_solve
from dratify.cnf import CNF
from dratify.lits import mk_lit
from cdclkit.pipeline import DEFAULT_PROBE, solve_adaptive
from tests.util import random_cnf, fuzz_seed

ENGINES = ["python"] + (["native"] if native.available() else [])


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


class TestCorrectness(unittest.TestCase):
    def test_matches_brute_force_under_every_policy(self):
        rng = random.Random(fuzz_seed(11))
        sat = unsat = 0
        for _ in range(60):
            f = random_cnf(rng, max_vars=9, ratio=4.8)
            ref = exhaustive_solve(f)
            for engine in ENGINES:
                for kw in ({}, {"always_preprocess": True}, {"never_preprocess": True}):
                    r = solve_adaptive(f, engine=engine, probe=5, **kw)
                    self.assertEqual(
                        bool(r.sat), ref is not None,
                        f"engine={engine} {kw}\n{f.to_dimacs()}")
                    if r.sat:
                        self.assertTrue(
                            f.is_satisfied_by(r.model),
                            f"engine={engine} {kw}: model does not satisfy the "
                            f"ORIGINAL formula -- reconstruction is wrong\n"
                            f"{f.to_dimacs()}")
            if ref is not None:
                sat += 1
            else:
                unsat += 1
        self.assertGreater(sat, 5)
        self.assertGreater(unsat, 5)

    def test_reconstructed_model_covers_eliminated_variables(self):
        """The failure this guards against: preprocessing eliminates a
        variable, the reduced formula's model says nothing about it, and the
        pipeline returns a short or wrong assignment."""
        f = CNF(6)
        f.add([mk_lit(0), mk_lit(1)])
        f.add([mk_lit(0), mk_lit(2, True)])
        f.add([mk_lit(3), mk_lit(4)])
        f.add([mk_lit(5)])
        for engine in ENGINES:
            r = solve_adaptive(f, engine=engine, always_preprocess=True)
            self.assertTrue(r.sat)
            self.assertEqual(len(r.model), f.nvars)
            self.assertTrue(f.is_satisfied_by(r.model))

    def test_unsat_detected_during_preprocessing(self):
        f = CNF(2)
        f.add([mk_lit(0)])
        f.add([mk_lit(0, True)])
        for engine in ENGINES:
            r = solve_adaptive(f, engine=engine, always_preprocess=True)
            self.assertFalse(r.sat)

    def test_pigeonhole_stays_unsat_under_the_policy(self):
        f = php(5)
        for engine in ENGINES:
            for kw in ({}, {"always_preprocess": True}, {"never_preprocess": True}):
                r = solve_adaptive(f, engine=engine, probe=10, **kw)
                self.assertFalse(r.sat, f"{engine} {kw}")


class TestPolicy(unittest.TestCase):
    def test_easy_instance_never_reaches_preprocessing(self):
        """queens is solved by propagation, so the probe finishes it and the
        preprocessing cost is never paid."""
        from cdclkit.cli import gen_queens

        f = gen_queens(20)
        r = solve_adaptive(f, probe=DEFAULT_PROBE)
        self.assertTrue(r.sat)
        self.assertFalse(r.preprocessed, "an instance solved in 0 conflicts "
                                         "must not trigger preprocessing")

    def test_hard_instance_does_reach_preprocessing(self):
        f = php(7)  # needs thousands of conflicts
        r = solve_adaptive(f, probe=50)
        self.assertFalse(r.sat)
        self.assertTrue(r.preprocessed, "an instance that exhausts the probe "
                                        "must be preprocessed")
        self.assertGreaterEqual(r.probe_conflicts, 50)

    def test_forced_policies_are_respected(self):
        f = php(5)
        self.assertTrue(solve_adaptive(f, always_preprocess=True).preprocessed)
        self.assertFalse(solve_adaptive(f, never_preprocess=True).preprocessed)

    def test_report_describes_the_decision(self):
        from cdclkit.cli import gen_queens

        easy = solve_adaptive(gen_queens(12))
        self.assertIn("skipped", easy.report())
        hard = solve_adaptive(php(6), probe=20)
        self.assertIn("preprocessed", hard.report())

    def test_falls_back_to_python_without_the_native_module(self):
        """Asking for the native engine when it is absent must work, not raise."""
        f = php(4)
        r = solve_adaptive(f, engine="native", probe=10)
        self.assertFalse(r.sat)

    def test_clause_counts_are_reported(self):
        f = php(6)
        r = solve_adaptive(f, always_preprocess=True)
        self.assertEqual(r.clauses_before, f.nclauses)
        self.assertGreater(r.clauses_before, 0)
        self.assertGreater(r.clauses_after, 0)


@unittest.skipUnless(native.available(), "native engine not built")
class TestNativePreprocessorAgreesWithPython(unittest.TestCase):
    def test_same_verdict_and_valid_models(self):
        rng = random.Random(fuzz_seed(29))
        for _ in range(40):
            f = random_cnf(rng, max_vars=11, ratio=5.0)
            py = solve_adaptive(f, engine="python", always_preprocess=True)
            rs = solve_adaptive(f, engine="native", always_preprocess=True)
            self.assertEqual(bool(py.sat), bool(rs.sat), f.to_dimacs())
            if rs.sat:
                self.assertTrue(f.is_satisfied_by(rs.model))
                self.assertTrue(f.is_satisfied_by(py.model))

    def test_native_preprocessing_proof_verifies(self):
        """Combined preprocessing + search proof, checked against the ORIGINAL
        formula by the Python checker."""
        from dratify.lits import from_dimacs
        from dratify.proof import check_proof

        n = native.require()
        f = php(5)
        p = n.Preprocessor(f.nvars, with_proof=True)
        for c in f.clauses:
            p.add_clause(list(c))
        p.run(3)
        steps = [(k, tuple(from_dimacs(d) for d in lits))
                 for k, lits in p.proof_steps()]

        if not p.unsat:
            s = n.Solver(f.nvars)
            s.enable_proof()
            ok = all(s.add_clause(list(c)) for c in p.reduced())
            self.assertFalse(s.solve() if ok else False)
            steps += [(k, tuple(from_dimacs(d) for d in lits))
                      for k, lits in s.proof_steps()]

        res = check_proof(f, steps)
        self.assertTrue(res.ok, res.report())


if __name__ == "__main__":
    unittest.main()
