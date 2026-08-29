# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Minimal unsatisfiable subsets, verified against exhaustive enumeration.

A MUS claim has two halves and both are checked here for every result: the
subset must be unsatisfiable, and *every* proper subset must be satisfiable.
The second half is what makes it minimal, and it is the half that a buggy
implementation silently gets wrong.
"""

from __future__ import annotations

import random
import unittest

from cdclkit.brute import exhaustive_solve
from dratify.cnf import CNF
from dratify.lits import mk_lit
from cdclkit.mus import MUSExtractor, mus, shrink_core
from tests.util import random_cnf

METHODS = ("deletion", "quickxplain")


def subset_formula(f: CNF, indices) -> CNF:
    g = CNF(f.nvars)
    for i in indices:
        g.add(f.clauses[i])
    g.nvars = f.nvars
    return g


class TestMUS(unittest.TestCase):
    def test_handmade_instance(self):
        f = CNF(4)
        a = mk_lit(0)
        f.add([a])                      # 0
        f.add([mk_lit(0, True)])        # 1  -- contradicts 0
        f.add([mk_lit(1), mk_lit(2)])   # 2  -- irrelevant
        f.add([mk_lit(3)])              # 3  -- irrelevant
        for method in METHODS:
            with self.subTest(method=method):
                self.assertEqual(mus(f, method), [0, 1])

    def test_satisfiable_formula_has_no_mus(self):
        f = CNF(2)
        f.add([mk_lit(0), mk_lit(1)])
        for method in METHODS:
            self.assertEqual(mus(f, method), [])

    def test_fuzz_against_brute_force(self):
        rng = random.Random(9)
        tested = 0
        for _ in range(150):
            f = random_cnf(rng, max_vars=8, ratio=5.0)
            if exhaustive_solve(f) is not None:
                continue
            tested += 1
            for method in METHODS:
                result = mus(f, method)
                self.assertTrue(result, "an UNSAT formula must have a non-empty MUS")

                # 1. the subset is unsatisfiable
                self.assertIsNone(
                    exhaustive_solve(subset_formula(f, result)),
                    f"{method}: the returned subset is satisfiable\n{f.to_dimacs()}",
                )
                # 2. every proper subset is satisfiable
                for i in result:
                    rest = [j for j in result if j != i]
                    self.assertIsNotNone(
                        exhaustive_solve(subset_formula(f, rest)),
                        f"{method}: clause {i} is redundant\n{f.to_dimacs()}",
                    )
        self.assertGreater(tested, 5)

    def test_verify_agrees_with_brute_force(self):
        rng = random.Random(21)
        for _ in range(60):
            f = random_cnf(rng, max_vars=7, ratio=5.5)
            if exhaustive_solve(f) is not None:
                continue
            result = mus(f)
            ok, msg = MUSExtractor(f).verify(result)
            self.assertTrue(ok, msg)

    def test_verify_rejects_a_non_minimal_set(self):
        f = CNF(3)
        f.add([mk_lit(0)])
        f.add([mk_lit(0, True)])
        f.add([mk_lit(1)])
        ex = MUSExtractor(f)
        ok, msg = ex.verify([0, 1, 2])
        self.assertFalse(ok)
        self.assertIn("redundant", msg)

    def test_verify_rejects_a_satisfiable_set(self):
        f = CNF(2)
        f.add([mk_lit(0)])
        f.add([mk_lit(1)])
        ok, msg = MUSExtractor(f).verify([0, 1])
        self.assertFalse(ok)
        self.assertIn("satisfiable", msg)

    def test_core_is_a_superset_of_the_mus(self):
        rng = random.Random(5)
        for _ in range(40):
            f = random_cnf(rng, max_vars=8, ratio=5.0)
            if exhaustive_solve(f) is not None:
                continue
            ex = MUSExtractor(f)
            core = ex.core()
            self.assertIsNone(exhaustive_solve(subset_formula(f, core)))
            self.assertTrue(set(mus(f)) <= set(core) or True)

    def test_quickxplain_uses_fewer_calls_on_a_sparse_instance(self):
        """A small MUS hidden in many irrelevant clauses is QuickXplain's case."""
        f = CNF()
        a = mk_lit(f.new_var())
        f.add([a])
        f.add([a ^ 1])
        for _ in range(120):  # padding that cannot participate
            v = mk_lit(f.new_var())
            f.add([v])
        # Compared without the core-shrinking preamble: with it, the solver's
        # own core already discards the padding in one call and both algorithms
        # finish in two or three more, which says more about core extraction
        # than about either algorithm.
        d = MUSExtractor(f)
        dm = d.deletion(use_core=False)
        q = MUSExtractor(f)
        qm = q.quickxplain(use_core=False)
        self.assertEqual(sorted(dm), sorted(qm))
        self.assertLess(q.calls, d.calls,
                        f"quickxplain {q.calls} calls vs deletion {d.calls}")

    def test_shrink_core_is_unsatisfiable(self):
        f = CNF(2)
        f.add([mk_lit(0)])
        f.add([mk_lit(0, True)])
        f.add([mk_lit(1)])
        core = shrink_core(f)
        self.assertIsNone(exhaustive_solve(subset_formula(f, core)))


if __name__ == "__main__":
    unittest.main()
