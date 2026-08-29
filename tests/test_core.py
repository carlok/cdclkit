# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Literal algebra, the activity heap, DIMACS I/O, and the reference solvers."""

from __future__ import annotations

import random
import unittest

from cdclkit.brute import (
    all_models,
    count_models,
    dpll,
    exhaustive_solve,
    implied_literals,
    resolution_refute,
)
from dratify.cnf import CNF, parse_dimacs
from cdclkit.heap import ActivityHeap
from dratify.lits import (
    F,
    T,
    U,
    flip,
    from_dimacs,
    is_neg,
    mk_lit,
    neg,
    to_dimacs,
    var_of,
)
from cdclkit.solver import Solver, luby
from tests.util import random_cnf, fuzz_seed


class TestLiterals(unittest.TestCase):
    def test_encoding_round_trip(self):
        for v in range(50):
            for negated in (False, True):
                l = mk_lit(v, negated)
                self.assertEqual(var_of(l), v)
                self.assertEqual(is_neg(l), negated)
                self.assertEqual(neg(neg(l)), l)
                self.assertNotEqual(neg(l), l)

    def test_dimacs_round_trip(self):
        for d in list(range(1, 40)) + [-x for x in range(1, 40)]:
            self.assertEqual(to_dimacs(from_dimacs(d)), d)
        with self.assertRaises(ValueError):
            from_dimacs(0)

    def test_three_valued_logic(self):
        self.assertEqual(flip(T), F)
        self.assertEqual(flip(F), T)
        self.assertEqual(flip(U), U)

    def test_negation_is_a_single_xor(self):
        for l in range(64):
            self.assertEqual(neg(l), l ^ 1)


class TestHeap(unittest.TestCase):
    def test_random_operation_sequences_preserve_invariants(self):
        rng = random.Random(fuzz_seed(1))
        n = 60
        act = [0.0] * n
        h = ActivityHeap(act, n)
        for v in range(n):
            h.insert(v)
        self.assertTrue(h.check_invariant())
        popped = []
        for step in range(2000):
            op = rng.random()
            if op < 0.4 and len(h):
                popped.append(h.pop_max())
            elif op < 0.7:
                v = rng.randrange(n)
                act[v] += rng.random() * 10
                h.bump(v)
            elif op < 0.9:
                h.insert(rng.randrange(n))
            else:
                h.remove(rng.randrange(n))
            self.assertTrue(h.check_invariant(), f"broken after step {step}")

    def test_pop_order_is_by_activity(self):
        n = 30
        act = [float(i) for i in range(n)]
        h = ActivityHeap(act, n)
        for v in range(n):
            h.insert(v)
        order = [h.pop_max() for _ in range(n)]
        self.assertEqual(order, list(range(n - 1, -1, -1)))

    def test_ties_break_deterministically(self):
        n = 10
        act = [1.0] * n
        h = ActivityHeap(act, n)
        for v in reversed(range(n)):
            h.insert(v)
        self.assertEqual([h.pop_max() for _ in range(n)], list(range(n)))

    def test_no_duplicate_insertion(self):
        act = [0.0] * 5
        h = ActivityHeap(act, 5)
        for _ in range(10):
            h.insert(3)
        self.assertEqual(len(h), 1)


class TestDimacs(unittest.TestCase):
    def test_parse_and_write_round_trip(self):
        text = "c a comment\np cnf 3 2\n1 -2 0\n2 3 0\n"
        f = parse_dimacs(text)
        self.assertEqual(f.nvars, 3)
        self.assertEqual(f.nclauses, 2)
        again = parse_dimacs(f.to_dimacs())
        self.assertEqual(again.clauses, f.clauses)
        self.assertEqual(again.nvars, f.nvars)

    def test_clause_spanning_multiple_lines(self):
        f = parse_dimacs("p cnf 4 1\n1 2\n3 4\n0\n")
        self.assertEqual(f.nclauses, 1)
        self.assertEqual(len(f.clauses[0]), 4)

    def test_missing_header_is_tolerated(self):
        f = parse_dimacs("1 -2 0\n-1 3 0\n")
        self.assertEqual(f.nvars, 3)
        self.assertEqual(f.nclauses, 2)

    def test_satlib_percent_terminator(self):
        f = parse_dimacs("p cnf 2 1\n1 2 0\n%\n0\n")
        self.assertEqual(f.nclauses, 1)

    def test_strict_mode_rejects_a_wrong_header(self):
        with self.assertRaises(ValueError):
            parse_dimacs("p cnf 9 9\n1 0\n", strict=True)

    def test_tautologies_are_dropped_and_duplicates_collapsed(self):
        f = CNF()
        self.assertFalse(f.add([mk_lit(0), neg(mk_lit(0))]))
        self.assertEqual(f.nclauses, 0)
        f.add([mk_lit(1), mk_lit(1), mk_lit(2)])
        self.assertEqual(len(f.clauses[0]), 2)

    def test_internal_literals_must_be_non_negative(self):
        f = CNF()
        with self.assertRaises(ValueError):
            f.add([-3])

    def test_stats(self):
        f = parse_dimacs("p cnf 3 3\n1 0\n1 2 0\n1 2 3 0\n")
        st = f.stats()
        self.assertEqual((st["unit"], st["binary"], st["ternary"]), (1, 1, 1))
        self.assertAlmostEqual(st["avg_len"], 2.0)


class TestReferenceSolvers(unittest.TestCase):
    def test_dpll_agrees_with_exhaustive(self):
        rng = random.Random(fuzz_seed(99))
        for _ in range(120):
            f = random_cnf(rng, max_vars=9)
            a = exhaustive_solve(f)
            b = dpll(f)
            self.assertEqual(a is None, b is None, f.to_dimacs())
            if b is not None:
                self.assertTrue(f.is_satisfied_by(b))

    def test_cdcl_agrees_with_both_references(self):
        rng = random.Random(fuzz_seed(1234))
        sat = unsat = 0
        for _ in range(200):
            f = random_cnf(rng, max_vars=10)
            ref = exhaustive_solve(f)
            s = Solver(f.nvars)
            ok = s.add_cnf(f)
            got = bool(s.solve()) if ok else False
            self.assertEqual(got, ref is not None, f.to_dimacs())
            if got:
                sat += 1
                self.assertTrue(f.is_satisfied_by(s.model))
            else:
                unsat += 1
        self.assertGreater(sat, 20)
        self.assertGreater(unsat, 20)

    def test_resolution_refutes_what_the_solver_refutes(self):
        rng = random.Random(fuzz_seed(31337))
        tested = 0
        for _ in range(60):
            f = random_cnf(rng, max_vars=6, ratio=6.0)
            if exhaustive_solve(f) is not None:
                continue
            tested += 1
            derivation = resolution_refute(f)
            self.assertIsNotNone(derivation, "UNSAT formula has no refutation?")
        self.assertGreater(tested, 5)

    def test_model_counting_matches_enumeration(self):
        rng = random.Random(fuzz_seed(5))
        for _ in range(30):
            f = random_cnf(rng, max_vars=7)
            expected = count_models(f)
            s = Solver(f.nvars)
            if not s.add_cnf(f):
                self.assertEqual(expected, 0)
                continue
            got = sum(1 for _ in s.enumerate_models())
            self.assertEqual(got, expected, f.to_dimacs())

    def test_backbone_literals_are_really_implied(self):
        rng = random.Random(fuzz_seed(17))
        for _ in range(30):
            f = random_cnf(rng, max_vars=7)
            models = all_models(f)
            if not models:
                continue
            for l in implied_literals(f):
                for m in models:
                    self.assertTrue(m[l >> 1] != bool(l & 1))


class TestLuby(unittest.TestCase):
    def test_prefix_of_the_sequence(self):
        expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]
        got = [luby(2.0, i) for i in range(len(expected))]
        self.assertEqual(got, [float(x) for x in expected])

    def test_sequence_is_non_decreasing_in_its_maxima(self):
        best = 0.0
        for i in range(200):
            best = max(best, luby(2.0, i))
        self.assertGreaterEqual(best, 64.0)


if __name__ == "__main__":
    unittest.main()
