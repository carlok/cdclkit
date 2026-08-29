# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Preprocessing: equisatisfiability, model reconstruction, and proof soundness.

Preprocessing is the one place in the toolkit where the transformed formula is
*not* logically equivalent to the input, so it gets the most paranoid tests:

1. reduced formula satisfiable  <=>  original satisfiable  (vs brute force);
2. every reconstructed model satisfies the **original** formula;
3. the combined preprocessing + solving proof verifies against the **original**
   formula, which is the only way to know that the eliminations were sound
   inferences and not just convenient deletions.
"""

from __future__ import annotations

import random
import unittest

from cdclkit.brute import exhaustive_solve
from dratify.cnf import CNF
from dratify.lits import mk_lit, neg
from cdclkit.preprocess import Preprocessor, preprocess
from dratify.proof import MemoryProof, check_proof
from cdclkit.solver import Solver
from tests.util import random_cnf, fuzz_seed


class TestPreprocessing(unittest.TestCase):
    def test_equisatisfiable_and_reconstructable(self):
        rng = random.Random(fuzz_seed(23))
        sat = unsat = 0
        for _ in range(200):
            f = random_cnf(rng, max_vars=10, ratio=5.0)
            ref = exhaustive_solve(f)
            pre = Preprocessor(f)
            red = pre.run()
            s = Solver(red.nvars)
            ok = s.add_cnf(red)
            got = bool(s.solve()) if ok else False
            self.assertEqual(got, ref is not None, f.to_dimacs())
            if got:
                sat += 1
                full = pre.reconstruct(s.model)
                self.assertTrue(
                    f.is_satisfied_by(full),
                    "reconstructed model does not satisfy the original:\n"
                    + f.to_dimacs(),
                )
            else:
                unsat += 1
        self.assertGreater(sat, 30)
        self.assertGreater(unsat, 30)

    def test_end_to_end_proof_verifies_against_the_original(self):
        rng = random.Random(fuzz_seed(77))
        checked = 0
        for _ in range(120):
            f = random_cnf(rng, max_vars=10, ratio=5.5)
            proof = MemoryProof()
            pre = Preprocessor(f, proof=proof)
            red = pre.run()
            s = Solver(red.nvars, proof=proof)
            ok = s.add_cnf(red)
            if ok and s.solve():
                continue
            checked += 1
            res = check_proof(f, proof)
            self.assertTrue(res.ok, res.report() + "\n" + f.to_dimacs())
        self.assertGreater(checked, 20)

    def test_frozen_variables_survive(self):
        f = CNF(4)
        a, b, c, d = (mk_lit(i) for i in range(4))
        f.add([a, b])
        f.add([neg(a), c])
        f.add([neg(b), d])
        pre = Preprocessor(f)
        pre.freeze([0])
        red = pre.run()
        self.assertNotIn(0, [v for v, _ in pre.eliminated])

    def test_unit_propagation_reduces_the_formula(self):
        f = CNF(3)
        a, b, c = mk_lit(0), mk_lit(1), mk_lit(2)
        f.add([a])
        f.add([neg(a), b])
        f.add([neg(b), c])
        pre = Preprocessor(f)
        red = pre.run()
        self.assertEqual(red.nclauses, 0, "everything should propagate away")
        self.assertEqual(pre.value, {0: True, 1: True, 2: True})
        model = pre.reconstruct([False] * 3)
        self.assertTrue(f.is_satisfied_by(model))

    def test_contradiction_is_detected(self):
        f = CNF(1)
        f.add([mk_lit(0)])
        f.add([neg(mk_lit(0))])
        pre = Preprocessor(f)
        red = pre.run()
        self.assertTrue(pre.unsat)
        self.assertIn((), red.clauses)

    def test_subsumption_removes_the_weaker_clause(self):
        f = CNF(3)
        a, b, c = mk_lit(0), mk_lit(1), mk_lit(2)
        f.add([a, b])
        f.add([a, b, c])
        pre = Preprocessor(f, do_bve=False, do_bce=False)
        pre.run()
        # (a v b) subsumes (a v b v c); pure-literal elimination then clears
        # what is left, so the observable evidence is the counter
        self.assertEqual(pre.stats.subsumed, 1)

    def test_self_subsuming_resolution_strengthens(self):
        f = CNF(3)
        a, b, c = mk_lit(0), mk_lit(1), mk_lit(2)
        f.add([a, b])
        f.add([neg(a), b, c])  # resolving on a gives (b v c), which subsumes it
        pre = Preprocessor(f, do_bve=False, do_bce=False)
        pre.run()
        self.assertGreaterEqual(pre.stats.strengthened, 1)

    def test_pure_literal_elimination(self):
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([a, b])
        f.add([a, neg(b)])
        pre = Preprocessor(f, do_bve=False, do_bce=False)
        red = pre.run()
        self.assertEqual(red.nclauses, 0)
        model = pre.reconstruct([False, False])
        self.assertTrue(f.is_satisfied_by(model))

    def test_bve_does_not_grow_the_formula(self):
        rng = random.Random(fuzz_seed(5))
        for _ in range(40):
            f = random_cnf(rng, max_vars=12, ratio=4.0)
            red, pre = preprocess(f)
            if pre.unsat:
                continue
            self.assertLessEqual(
                red.nclauses,
                f.nclauses + pre.stats.resolvents,
                "preprocessing produced more clauses than it added",
            )

    def test_preprocessing_is_idempotent_enough(self):
        """Running the preprocessor on its own output must not find much left."""
        rng = random.Random(fuzz_seed(9))
        for _ in range(20):
            f = random_cnf(rng, max_vars=12, ratio=4.0)
            red1, pre1 = preprocess(f)
            if pre1.unsat:
                continue
            red2, pre2 = preprocess(red1)
            self.assertLessEqual(red2.nclauses, red1.nclauses)

    def test_reconstruction_raises_on_a_corrupt_stack(self):
        """The invariant check must actually fire when the stack is wrong."""
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([a, b])
        pre = Preprocessor(f)
        pre.run()
        pre.eliminated.append((0, [(a,), (neg(a),)]))
        with self.assertRaises(AssertionError):
            pre.reconstruct([False, False])


if __name__ == "__main__":
    unittest.main()
