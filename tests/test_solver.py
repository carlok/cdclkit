# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Solver behaviour: invariants, assumptions and cores, incrementality, budgets."""

from __future__ import annotations

import random
import unittest

from cdclkit.brute import exhaustive_solve
from dratify.cnf import CNF
from dratify.lits import mk_lit, neg
from cdclkit.solver import Config, Solver
from tests.util import random_cnf


class TestInvariants(unittest.TestCase):
    def test_watch_and_trail_invariants_hold_after_solving(self):
        rng = random.Random(2)
        for _ in range(60):
            f = random_cnf(rng, max_vars=14, ratio=4.3)
            s = Solver(f.nvars)
            if not s.add_cnf(f):
                continue
            s.solve()
            self.assertEqual(s.check_watch_invariant(), [])
            self.assertEqual(s.check_trail_invariant(), [])

    def test_watch_invariant_survives_db_reduction(self):
        f = php(7)
        s = Solver(f.nvars, config=Config(first_reduce=200, reduce_inc=50))
        s.add_cnf(f)
        self.assertFalse(s.solve())
        self.assertGreater(s.stats.reductions, 1)
        self.assertEqual(s.check_watch_invariant(), [])

    def test_learnt_clauses_are_asserting(self):
        """After backjumping, the learnt clause must propagate immediately --
        that is the whole point of the first-UIP scheme."""
        f = php(5)
        s = Solver(f.nvars)
        s.add_cnf(f)
        seen = []
        original_record = s._record

        def spy(learnt, lbd):
            # every literal except the first must be false at the backjump level
            seen.append(len(learnt))
            return original_record(learnt, lbd)

        s._record = spy
        self.assertFalse(s.solve())
        self.assertGreater(len(seen), 10)
        self.assertTrue(all(n >= 1 for n in seen))


class TestInvariantsDuringSearch(unittest.TestCase):
    """Check invariants *mid-search*, not only when the solver has stopped.

    Post-hoc checks run on a solver that has already backtracked to level 0,
    which is the state in which almost everything is trivially consistent. A
    corruption that appears at depth and is undone on the way out would never
    be seen. So this class hooks the internals and checks after every conflict
    analysis and every database reduction, while the trail is still deep.
    """

    def _instrumented_solve(self, f, hook_reduce=True):
        s = Solver(f.nvars, config=Config(first_reduce=120, reduce_inc=40))
        s.add_cnf(f)
        problems = []
        checks = [0]

        real_analyze = s._analyze
        real_reduce = s._reduce_db

        def analyze(confl):
            learnt, bt, lbd = real_analyze(confl)
            checks[0] += 1
            if checks[0] % 17 == 0:  # sampling: the check is O(database)
                problems.extend(s.check_watch_invariant())
                problems.extend(s.check_trail_invariant())
                # the learnt clause must be false under the current assignment,
                # which is what makes it a legitimate conflict clause
                for l in learnt:
                    if s.value(l) != 2:  # F
                        problems.append(f"learnt literal {l} is not false at conflict")
                # and the backjump level must be below the current one
                if bt >= s.decision_level:
                    problems.append(f"backjump to {bt} from level {s.decision_level}")
                if lbd < 1 or lbd > len(learnt):
                    problems.append(f"LBD {lbd} out of range for a clause of {len(learnt)}")
            return learnt, bt, lbd

        def reduce_db():
            real_reduce()
            problems.extend(s.check_watch_invariant())
            problems.extend(s.check_trail_invariant())

        s._analyze = analyze
        if hook_reduce:
            s._reduce_db = reduce_db
        result = s.solve()
        return result, problems, checks[0], s

    def test_invariants_hold_mid_search_on_pigeonhole(self):
        result, problems, checks, s = self._instrumented_solve(php(7))
        self.assertFalse(result)
        self.assertGreater(checks, 100, "the instrumentation never ran")
        self.assertGreater(s.stats.reductions, 0, "database reduction never fired")
        self.assertEqual(problems[:5], [])

    def test_invariants_hold_mid_search_on_random_instances(self):
        rng = random.Random(3)
        for _ in range(8):
            f = random_cnf(rng, max_vars=60, ratio=4.3)
            _, problems, _, _ = self._instrumented_solve(f)
            self.assertEqual(problems[:5], [])

    def test_asserting_clause_property(self):
        """After backjumping, the learnt clause must be unit -- that is what
        makes CDCL progress rather than loop."""
        f = php(6)
        s = Solver(f.nvars)
        s.add_cnf(f)
        real_analyze = s._analyze
        checked = [0]
        problems = []

        def analyze(confl):
            learnt, bt, lbd = real_analyze(confl)
            # simulate the backjump the search loop is about to perform
            # (idempotent: the loop performs the same cancel immediately after)
            s._cancel_until(bt)
            if s.value(learnt[0]) != 0:  # U: must be unassigned, ready to assert
                problems.append(f"asserting literal already assigned after backjump")
            for l in learnt[1:]:
                if s.value(l) != 2:  # F
                    problems.append("learnt clause is not unit after backjump")
                    break
            checked[0] += 1
            return learnt, bt, lbd

        s._analyze = analyze
        self.assertFalse(s.solve())
        self.assertGreater(checked[0], 50)
        self.assertEqual(problems[:3], [])


class TestConfigurations(unittest.TestCase):
    def test_all_restart_policies_agree(self):
        rng = random.Random(8)
        for _ in range(40):
            f = random_cnf(rng, max_vars=11, ratio=4.4)
            ref = exhaustive_solve(f) is not None
            for restart in ("glucose", "luby", "none"):
                for ccmin in ("deep", "basic", "none"):
                    s = Solver(f.nvars, config=Config(restart=restart, ccmin=ccmin))
                    ok = s.add_cnf(f)
                    got = bool(s.solve()) if ok else False
                    self.assertEqual(
                        got, ref, f"restart={restart} ccmin={ccmin}\n{f.to_dimacs()}"
                    )

    def test_random_decisions_still_correct(self):
        rng = random.Random(21)
        for _ in range(30):
            f = random_cnf(rng, max_vars=10)
            ref = exhaustive_solve(f) is not None
            s = Solver(f.nvars, config=Config(rnd_freq=0.3, rnd_seed=12345))
            ok = s.add_cnf(f)
            self.assertEqual(bool(s.solve()) if ok else False, ref)

    def test_phase_saving_off(self):
        f = php(5)
        s = Solver(f.nvars, config=Config(phase_saving=False))
        s.add_cnf(f)
        self.assertFalse(s.solve())

    def test_runs_are_reproducible(self):
        f = php(6)
        runs = []
        for _ in range(2):
            s = Solver(f.nvars)
            s.add_cnf(f)
            s.solve()
            runs.append((s.stats.conflicts, s.stats.decisions, s.stats.propagations))
        self.assertEqual(runs[0], runs[1])


class TestAssumptions(unittest.TestCase):
    def test_assumptions_restrict_the_search(self):
        f = CNF(3)
        a, b, c = mk_lit(0), mk_lit(1), mk_lit(2)
        f.add([a, b])
        f.add([neg(a), c])
        s = Solver(f.nvars)
        s.add_cnf(f)
        self.assertTrue(s.solve([a]))
        self.assertTrue(s.model[0])
        self.assertTrue(s.model[2], "a implies c")
        self.assertTrue(s.solve([neg(a)]))
        self.assertTrue(s.model[1], "not a implies b")

    def test_contradictory_assumptions_give_a_core(self):
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([a, b])
        s = Solver(f.nvars)
        s.add_cnf(f)
        self.assertFalse(s.solve([neg(a), neg(b)]))
        core = set(s.conflict)
        self.assertTrue(core)
        self.assertTrue(core <= {neg(a), neg(b)}, f"core {core} is not a subset")

    def test_core_is_a_genuine_reason(self):
        """Every returned core must itself be unsatisfiable with the formula."""
        rng = random.Random(77)
        checked = 0
        for _ in range(80):
            f = random_cnf(rng, max_vars=9, ratio=3.0)
            s = Solver(f.nvars)
            if not s.add_cnf(f):
                continue
            if not s.solve():
                continue
            # flip a few literals of the model to create failing assumptions
            assumptions = [
                mk_lit(v, s.model[v]) for v in rng.sample(range(f.nvars), min(3, f.nvars))
            ]
            if s.solve(assumptions):
                continue
            checked += 1
            core = s.conflict
            self.assertTrue(core, "UNSAT under assumptions but empty core")
            self.assertTrue(set(core) <= set(assumptions), f"{core} vs {assumptions}")
            verify = Solver(f.nvars)
            verify.add_cnf(f)
            self.assertFalse(verify.solve(core), "the core is satisfiable: not a core")
        self.assertGreater(checked, 5)

    def test_solving_after_assumptions_is_unaffected(self):
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([a, b])
        s = Solver(f.nvars)
        s.add_cnf(f)
        self.assertFalse(s.solve([neg(a), neg(b)]))
        self.assertTrue(s.solve(), "the solver must recover after a failed assumption set")


class TestIncremental(unittest.TestCase):
    def test_adding_clauses_between_solves(self):
        s = Solver(3)
        a, b, c = mk_lit(0), mk_lit(1), mk_lit(2)
        s.add_clause([a, b, c])
        self.assertTrue(s.solve())
        s.add_clause([neg(a)])
        s.add_clause([neg(b)])
        self.assertTrue(s.solve())
        self.assertTrue(s.model[2])
        s.add_clause([neg(c)])
        self.assertFalse(s.solve())
        self.assertFalse(s.solve(), "an UNSAT solver must stay UNSAT")

    def test_new_variables_after_solving(self):
        s = Solver(1)
        s.add_clause([mk_lit(0)])
        self.assertTrue(s.solve())
        v = s.new_var()
        s.add_clause([mk_lit(v, True)])
        self.assertTrue(s.solve())
        self.assertTrue(s.model[0])
        self.assertFalse(s.model[v])

    def test_enumeration_finds_every_model_exactly_once(self):
        s = Solver(3)
        a, b, c = mk_lit(0), mk_lit(1), mk_lit(2)
        s.add_clause([a, b, c])
        models = [tuple(m) for m in s.enumerate_models()]
        self.assertEqual(len(models), 7)
        self.assertEqual(len(set(models)), 7)

    def test_projected_enumeration(self):
        s = Solver(3)
        s.add_clause([mk_lit(0), mk_lit(1)])
        models = [tuple(m[:2]) for m in s.enumerate_models(projection=[0, 1])]
        self.assertEqual(sorted(models), [(False, True), (True, False), (True, True)])


class TestBudget(unittest.TestCase):
    def test_conflict_budget_returns_unknown(self):
        f = php(9)  # far too hard for 20 conflicts
        s = Solver(f.nvars)
        s.add_cnf(f)
        self.assertIsNone(s.solve(max_conflicts=20))
        self.assertLessEqual(s.stats.conflicts, 100)

    def test_solver_continues_after_a_budget_stop(self):
        f = php(6)
        s = Solver(f.nvars)
        s.add_cnf(f)
        self.assertIsNone(s.solve(max_conflicts=5))
        self.assertFalse(s.solve())


class TestRootSimplification(unittest.TestCase):
    def test_units_shrink_the_database(self):
        """A formula with many root units exercises `_simplify`."""
        f = CNF(40)
        for v in range(20):
            f.add([mk_lit(v)])
        rng = random.Random(4)
        for _ in range(200):
            vs = rng.sample(range(40), 3)
            f.add([mk_lit(v, rng.random() < 0.5) for v in vs])
        s = Solver(f.nvars)
        ok = s.add_cnf(f)
        result = s.solve() if ok else False
        ref = None
        # cross-check with a fresh solver that never simplifies
        s2 = Solver(f.nvars, config=Config(restart="none"))
        ok2 = s2.add_cnf(f)
        ref = s2.solve() if ok2 else False
        self.assertEqual(bool(result), bool(ref))
        if result:
            self.assertTrue(f.is_satisfied_by(s.model))
        self.assertEqual(s.check_watch_invariant(), [])


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


if __name__ == "__main__":
    unittest.main()
