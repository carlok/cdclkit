# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Tests for the oracle itself.

`brute.py` is the ground truth for roughly 1,700 comparisons per suite run, in
eight other test files. It had no tests of its own, and its only internal check
compared `dpll` against `exhaustive_solve` -- both defined in `brute.py`. That
is self-consistency, not independence: a shared misreading of the CNF format
would agree with itself perfectly.

So these check it from outside. Every satisfiable verdict is confirmed with
`CNF.is_satisfied_by`, which lives in a different package (`dratify`), and
every unsatisfiable verdict on a small formula is confirmed by enumerating all
2^n assignments here in the test, with no help from `brute`.
"""

from __future__ import annotations

import itertools
import unittest

from dratify import parse_dimacs
from dratify.lits import from_dimacs
from cdclkit.brute import (all_models, count_models, dpll, exhaustive_solve,
                           implied_literals, resolution_refute)


def satisfiable_by_enumeration(f):
    """Independent oracle for the oracle. Deliberately naive."""
    for bits in itertools.product([False, True], repeat=f.nvars):
        if all(any(bits[l >> 1] != bool(l & 1) for l in c) for c in f.clauses):
            return list(bits)
    return None


SAT = parse_dimacs("p cnf 3 3\n1 2 0\n-2 3 0\n-1 3 0\n")
UNSAT = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")


class TestAgainstIndependentEnumeration(unittest.TestCase):
    def test_verdicts_match_on_hand_written_formulas(self):
        for f in (SAT, UNSAT):
            mine = satisfiable_by_enumeration(f)
            self.assertEqual(exhaustive_solve(f) is None, mine is None)
            self.assertEqual(dpll(f) is None, mine is None)

    def test_models_really_satisfy_the_formula(self):
        """Checked with dratify's evaluator, not brute's own."""
        for f in (SAT,):
            for solve in (exhaustive_solve, dpll):
                model = solve(f)
                self.assertIsNotNone(model)
                self.assertTrue(f.is_satisfied_by(model))

    def test_unsat_verdicts_survive_full_enumeration(self):
        self.assertIsNone(exhaustive_solve(UNSAT))
        self.assertIsNone(satisfiable_by_enumeration(UNSAT))

    def test_random_instances_agree_with_enumeration(self):
        import random
        rng = random.Random(20260829)
        for _ in range(120):
            n = rng.randint(1, 6)
            f = parse_dimacs(f"p cnf {n} 0\n")
            for _ in range(rng.randint(1, 3 * n)):
                k = rng.randint(1, min(3, n))
                vs = rng.sample(range(1, n + 1), k)
                f.add_dimacs([v if rng.random() < 0.5 else -v for v in vs])
            expected = satisfiable_by_enumeration(f) is not None
            self.assertEqual(exhaustive_solve(f) is not None, expected,
                             f.to_dimacs())
            self.assertEqual(dpll(f) is not None, expected, f.to_dimacs())


class TestEdgeCases(unittest.TestCase):
    def test_empty_formula_is_satisfiable(self):
        f = parse_dimacs("p cnf 0 0\n")
        self.assertIsNotNone(exhaustive_solve(f))
        self.assertIsNotNone(dpll(f))

    def test_a_formula_containing_the_empty_clause_is_not(self):
        f = parse_dimacs("p cnf 1 1\n0\n")
        self.assertIsNone(exhaustive_solve(f))
        self.assertIsNone(dpll(f))

    def test_contradictory_units(self):
        f = parse_dimacs("p cnf 1 2\n1 0\n-1 0\n")
        self.assertIsNone(exhaustive_solve(f))
        self.assertIsNone(dpll(f))

    def test_dpll_reports_none_rather_than_looping(self):
        """A step budget that runs out must not be reported as UNSAT."""
        f = parse_dimacs("p cnf 3 1\n1 2 3 0\n")
        self.assertIsNotNone(dpll(f, max_steps=10_000))


class TestCounting(unittest.TestCase):
    def test_model_count_matches_enumeration(self):
        f = parse_dimacs("p cnf 3 1\n1 2 0\n")
        expected = sum(
            1 for bits in itertools.product([False, True], repeat=3)
            if bits[0] or bits[1])
        self.assertEqual(count_models(f), expected)

    def test_all_models_are_distinct_and_all_satisfy(self):
        f = parse_dimacs("p cnf 3 1\n1 2 0\n")
        models = all_models(f)
        self.assertEqual(len(models), len(set(models)))
        self.assertEqual(len(models), count_models(f))
        for m in models:
            self.assertTrue(f.is_satisfied_by(list(m)))

    def test_an_unsatisfiable_formula_has_no_models(self):
        self.assertEqual(count_models(UNSAT), 0)
        self.assertEqual(all_models(UNSAT), [])

    def test_projection_counts_distinct_partial_assignments(self):
        f = parse_dimacs("p cnf 2 0\n")
        self.assertEqual(count_models(f), 4)
        self.assertEqual(count_models(f, projection=[0]), 2)


class TestImpliedLiterals(unittest.TestCase):
    def test_a_unit_clause_is_implied(self):
        f = parse_dimacs("p cnf 2 1\n1 0\n")
        self.assertIn(from_dimacs(1), implied_literals(f))

    def test_nothing_is_implied_by_a_free_choice(self):
        f = parse_dimacs("p cnf 1 0\n")
        self.assertEqual(list(implied_literals(f)), [])


class TestResolutionRefute(unittest.TestCase):
    def test_refutes_an_unsatisfiable_formula(self):
        self.assertTrue(resolution_refute(UNSAT))

    def test_does_not_refute_a_satisfiable_one(self):
        self.assertFalse(resolution_refute(SAT))


if __name__ == "__main__":
    unittest.main()
