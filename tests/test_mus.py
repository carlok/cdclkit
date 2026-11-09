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
import signal
import sys
import unittest
from unittest import mock

from cdclkit.brute import exhaustive_solve
from cdclkit.cli import gen_php
from cdclkit.model import Model
from cdclkit.solver import Solver
from dratify.cnf import CNF
from dratify.lits import mk_lit
from cdclkit.mus import MUSExtractor, mus, shrink_core
from tests.util import random_cnf, fuzz_seed

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
        rng = random.Random(fuzz_seed(9))
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
        rng = random.Random(fuzz_seed(21))
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
        rng = random.Random(fuzz_seed(5))
        for _ in range(40):
            f = random_cnf(rng, max_vars=8, ratio=5.0)
            if exhaustive_solve(f) is not None:
                continue
            ex = MUSExtractor(f)
            core = ex.core()
            self.assertIsNone(exhaustive_solve(subset_formula(f, core)))
            # `or True` used to disable this, so the test's own name went
            # unchecked. Verified over 457 unsatisfiable instances across 25
            # seeds before enabling it: no violations.
            self.assertLessEqual(set(mus(f)), set(core),
                                 "a MUS must sit inside the core it came from")

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


def _from_dimacs(clauses, nvars=0):
    f = CNF(nvars)
    for c in clauses:
        f.add_dimacs(c)
    return f


def _interrupt_after(obj, method, k, exc=KeyboardInterrupt):
    """Raise from `method` on its k-th call: where a timer's signal could land,
    but in the same place every run."""
    real = getattr(obj, method)
    calls = [0]

    def wrapper(*args, **kw):
        calls[0] += 1
        if calls[0] == k:
            raise exc()
        return real(*args, **kw)

    return mock.patch.object(obj, method, wrapper)


#: Internal steps of the search, each one holding state half-changed.
_STEPS = ("_lbd", "_analyze", "_propagate", "_assign", "_record", "_cancel_until",
          "_lit_redundant", "_bump_var", "_pick_branch_lit")


class TestRepeatedIndices(unittest.TestCase):
    """A repeated assumption opened a level with no variable of its own, and
    `_lbd` indexed a per-variable array by level. That was the crash. The exception
    then skipped the line clearing `seen`, and that was the wrong answer."""

    FOUR = [[1, 2], [-1, 2], [1, -2], [-1, -2]]

    def test_a_repeated_index_is_the_same_clause(self):
        ex = MUSExtractor(_from_dimacs([[1, 2], [1, -2]]))
        self.assertFalse(ex.is_unsat([0, 0, 1]))
        self.assertEqual(ex.core([0, 0, 1]), [])
        self.assertEqual(ex.deletion([0, 0, 1]), [])
        self.assertEqual(ex.quickxplain([0, 0, 1]), [])

    def test_a_repeated_index_gives_each_clause_once(self):
        ex = MUSExtractor(_from_dimacs(self.FOUR))
        repeats = [0, 0, 0, 1, 1, 2, 3, 3]
        for use_core in (True, False):
            self.assertEqual(ex.deletion(repeats, use_core=use_core), [0, 1, 2, 3])
            self.assertEqual(ex.quickxplain(repeats, use_core=use_core), [0, 1, 2, 3])
        self.assertEqual(ex.core(repeats), [0, 1, 2, 3])
        self.assertEqual(ex.verify(repeats)[0], True)
        self.assertIn("all 4 clauses", ex.verify(repeats)[1])

    def test_a_repeated_assumption_in_the_solver(self):
        s = Solver(3)
        for c in ([-3, 1, 2], [-3, -1, 2], [-3, 1, -2], [-3, -1, -2]):
            s.add_clause_dimacs(c)
        self.assertIs(s.solve([mk_lit(2)] * 3), False)
        self.assertEqual(s.conflict, [mk_lit(2)])

    def test_repeats_do_not_poison_the_extractor(self):
        ex = MUSExtractor(_from_dimacs(self.FOUR))
        self.assertTrue(ex.is_unsat([0, 0, 0, 0, 1, 2, 3]))
        self.assertFalse(ex.is_unsat([0, 0, 0, 0, 2]))
        self.assertEqual(ex.deletion(), [0, 1, 2, 3])

    def test_an_index_out_of_range_still_raises_and_harms_nothing(self):
        ex = MUSExtractor(_from_dimacs(self.FOUR))
        with self.assertRaises(IndexError):
            ex.is_unsat([99])
        self.assertFalse(ex.solver.broken)
        self.assertEqual(ex.deletion(), [0, 1, 2, 3])


class TestAnInterruptedCallCannotPoisonALaterOne(unittest.TestCase):
    """An exception from the middle of the search can leave any of its state half
    changed, not only `seen`. A timer's KeyboardInterrupt got a satisfiable set out
    of `deletion()` and an endorsement of it out of `verify()`, on a formula with no
    repeats at all. Cleaning up one field at a time cannot cover that, so a solver
    that was interrupted refuses to answer, and the extractor builds another."""

    def _php(self):
        return gen_php(4, 3)

    def _assert_is_a_mus(self, f, ex):
        result = ex.deletion()
        self.assertTrue(result, "php is unsatisfiable, so it has a MUS")
        self.assertIsNone(exhaustive_solve(subset_formula(f, result)),
                          f"{result} is satisfiable")
        for i in result:
            rest = subset_formula(f, [j for j in result if j != i])
            self.assertIsNotNone(exhaustive_solve(rest), f"{i} is redundant")
        self.assertTrue(ex.verify(result)[0])

    def test_the_extractor_recovers_from_a_step_interrupted_anywhere(self):
        for step in _STEPS:
            for k in (1, 2, 5, 17):
                with self.subTest(step=step, k=k):
                    f = self._php()
                    ex = MUSExtractor(f)
                    with _interrupt_after(ex.solver, step, k):
                        try:
                            ex.is_unsat(list(range(f.nclauses)))
                            continue  # the search never made k such calls
                        except KeyboardInterrupt:
                            pass
                    self._assert_is_a_mus(f, ex)

    def test_any_exception_counts(self):
        f = self._php()
        ex = MUSExtractor(f)
        with _interrupt_after(ex.solver, "_lbd", 1, exc=MemoryError):
            with self.assertRaises(MemoryError):
                ex.is_unsat(list(range(f.nclauses)))
        self._assert_is_a_mus(f, ex)

    def test_a_real_timer(self):
        """The verifier's reproducer. Delivery is not deterministic, so this asks
        only that every outcome is right, however many it interrupts."""
        if not hasattr(signal, "setitimer"):
            self.skipTest("no interval timer on this platform")
        if sys.gettrace() is not None:
            # An interrupt landing inside a trace function unsets it for good, so
            # under tests/coverage_report.py every later test went unmeasured.
            self.skipTest("a signal would switch the tracer off")

        def handler(signum, frame):
            raise KeyboardInterrupt

        f = gen_php(6, 5)
        old = signal.signal(signal.SIGALRM, handler)
        self.addCleanup(signal.signal, signal.SIGALRM, old)
        for i in range(12):
            ex = MUSExtractor(f)
            signal.setitimer(signal.ITIMER_REAL, 0.0005 * (1 + i))
            try:
                ex.is_unsat(list(range(f.nclauses)))
            except KeyboardInterrupt:
                pass
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
            r = ex.deletion()
            self.assertEqual(ex.verify(r)[0], True, r)
            # by a solver that shares nothing with `ex`
            s = Solver(f.nvars)
            s.add_cnf(subset_formula(f, r))
            self.assertIs(s.solve(), False, f"{r} is satisfiable")

    def test_verify_does_not_ask_the_solver_it_is_checking(self):
        """Even a solver in a state nobody foresaw cannot talk it round."""
        f = _from_dimacs([[1, 2], [-1, 2], [1, -2], [-1, -2]])
        ex = MUSExtractor(f)
        with mock.patch.object(ex.solver, "solve", return_value=False):
            ok, why = ex.verify([1, 3])
        self.assertFalse(ok)
        self.assertIn("satisfiable", why)

    def test_a_plain_solver_refuses_to_answer(self):
        """There is no formula to rebuild from here, so the answer is to say so.
        The wrong UNSAT this replaces at least failed its replay; no answer is
        better than one that needs catching."""
        f = self._php()
        s = Solver(f.nvars)
        s.add_cnf(f)
        with _interrupt_after(s, "_lbd", 1):
            with self.assertRaises(KeyboardInterrupt):
                s.solve()
        self.assertTrue(s.broken)
        with self.assertRaises(RuntimeError) as cm:
            s.solve()
        self.assertIn("interrupted", str(cm.exception))
        with self.assertRaises(RuntimeError):
            s.add_clause([0])
        with self.assertRaises(RuntimeError):
            s.new_var()

    def test_an_interrupted_add_clause_counts(self):
        s = Solver(2)
        with _interrupt_after(s, "_attach", 1):
            with self.assertRaises(KeyboardInterrupt):
                s.add_clause([0, 2])
        self.assertTrue(s.broken)

    def test_ordinary_endings_leave_the_solver_whole(self):
        f = gen_php(7, 6)
        s = Solver(f.nvars)
        s.add_cnf(f)
        self.assertIsNone(s.solve(max_conflicts=1))
        self.assertFalse(s.broken)
        self.assertIsNone(s.solve(deadline=0.0))
        self.assertFalse(s.broken)
        self.assertIs(s.solve(), False)
        self.assertFalse(s.broken)

    def test_a_bad_literal_harms_nothing(self):
        s = Solver(2)
        with self.assertRaises(ValueError):
            s.add_clause_dimacs([0])
        self.assertFalse(s.broken)
        self.assertIs(s.solve(), True)

    def test_the_model_builds_another_solver(self):
        m = Model()
        a = m.bool_var("a")
        m.add_clause([a])
        s = m.build_solver()
        with _interrupt_after(s, "_pick_branch_lit", 1):
            with self.assertRaises(KeyboardInterrupt):
                m.solve()
        sol = m.solve()
        self.assertIs(sol[a], True)
        self.assertIsNot(m.solver, s)


if __name__ == "__main__":
    unittest.main()
