# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The oracle on cases worked out by hand, and on the theorems it must respect.

Run from the repository root: python -m unittest campaign.test_oracle
"""

from __future__ import annotations

import itertools
import random
import unittest

try:
    from campaign import oracle
except ImportError:            # run from inside campaign/
    import oracle

SQUARE = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
# PHP(3,2): 3 pigeons, 2 holes; variable 2p + h - 2 for pigeon p, hole h
PHP32 = [[1, 2], [3, 4], [5, 6], [-1, -3], [-1, -5], [-3, -5], [-2, -4], [-2, -6], [-4, -6]]


def by_plain_loop(formula):
    """The same question, one assignment at a time, sharing nothing with _masks."""
    variables = sorted({abs(l) for c in formula for l in c})
    for values in itertools.product((False, True), repeat=len(variables)):
        value = dict(zip(variables, values))
        if all(any(value[abs(l)] == (l > 0) for l in c) for c in formula):
            return True
    return False


def random_formula(rng, nvars, nclauses, maxlen=4):
    return [[rng.choice((1, -1)) * rng.randint(1, nvars)
             for _ in range(rng.randint(0 if rng.random() < .02 else 1, maxlen))]
            for _ in range(nclauses)]


class TestSatisfiable(unittest.TestCase):
    def test_known_answers(self):
        self.assertTrue(oracle.satisfiable([]))
        self.assertFalse(oracle.satisfiable([[]]))
        self.assertFalse(oracle.satisfiable([[1, 2], []]))
        self.assertTrue(oracle.satisfiable([[1]]))
        self.assertFalse(oracle.satisfiable([[1], [-1]]))
        self.assertFalse(oracle.satisfiable(SQUARE))
        self.assertTrue(oracle.satisfiable(SQUARE[:3]))
        self.assertFalse(oracle.satisfiable(PHP32))
        self.assertTrue(oracle.satisfiable([[1, -1]]))
        self.assertTrue(oracle.satisfiable([[1, 1], [2, 2, 2]]))

    def test_gaps_in_the_numbering_do_not_matter(self):
        self.assertFalse(oracle.satisfiable([[7, 900], [7, -900], [-7, 900], [-7, -900]]))
        self.assertTrue(oracle.satisfiable([[7, 900], [7, -900], [-7, 900]]))

    def test_the_limit_counts_mentioned_variables_and_refuses(self):
        at_limit = [[v] for v in range(1, 17)]
        self.assertTrue(oracle.satisfiable(at_limit))
        self.assertFalse(oracle.satisfiable([*at_limit, [-16]]))
        with self.assertRaises(ValueError):
            oracle.satisfiable([*at_limit, [17]])
        # only the mentioned ones count: these are two variables
        self.assertTrue(oracle.satisfiable([[1000], [2000]]))

    def test_a_single_satisfying_assignment_is_found_at_the_limit(self):
        # exactly one model of 2**16; the masks must not lose the top bits
        for model in (0, 0xFFFF, 0x8001, 0x1234):
            units = [[v if model >> (v - 1) & 1 else -v] for v in range(1, 17)]
            self.assertTrue(oracle.satisfiable(units))
            flip = [[-c[0]] for c in units]
            self.assertFalse(oracle.satisfiable([*units, *flip[:1]]))

    def test_agrees_with_a_plain_loop(self):
        rng = random.Random(20261108)
        answers = set()
        for _ in range(3000):
            f = random_formula(rng, rng.randint(1, 7), rng.randint(0, 24))
            answer = oracle.satisfiable(f)
            self.assertEqual(answer, by_plain_loop(f), f)
            answers.add(answer)
        self.assertEqual(answers, {True, False})

    def test_refuses_what_is_not_a_literal(self):
        for bad in ([0], [True], ["1"], [1.0]):
            with self.assertRaises(ValueError):
                oracle.satisfiable([bad])


class TestImpliesAndPreserves(unittest.TestCase):
    def test_implies(self):
        self.assertTrue(oracle.implies(SQUARE, [1]))
        self.assertTrue(oracle.implies(SQUARE, []))     # unsat implies everything
        self.assertTrue(oracle.implies([[1, 2]], [1, 2]))
        self.assertTrue(oracle.implies([[1, 2]], [1, 2, 3]))
        self.assertFalse(oracle.implies([[1, 2]], [1]))
        self.assertFalse(oracle.implies([[1, 2]], []))
        self.assertTrue(oracle.implies([], [1, -1]))    # a tautology always follows
        self.assertFalse(oracle.implies([], [1]))

    def test_preserves_sat(self):
        self.assertTrue(oracle.preserves_sat([[1, 2]], [-1]))   # not implied, still fine
        self.assertFalse(oracle.implies([[1, 2]], [-1]))
        self.assertFalse(oracle.preserves_sat([[1, 2], [-1, 2]], [-2]))
        self.assertFalse(oracle.preserves_sat([[1]], []))
        self.assertTrue(oracle.preserves_sat(SQUARE, []))       # F already unsat
        self.assertTrue(oracle.preserves_sat(SQUARE, [3]))


class TestPropagate(unittest.TestCase):
    def test_a_chain(self):
        conflict, a = oracle.propagate([[1], [-1, 2], [-2, 3]])
        self.assertFalse(conflict)
        self.assertEqual(a, {1, 2, 3})

    def test_order_of_clauses_does_not_matter(self):
        conflict, a = oracle.propagate([[-2, 3], [-1, 2], [1]])
        self.assertFalse(conflict)
        self.assertEqual(a, {1, 2, 3})

    def test_conflict(self):
        self.assertTrue(oracle.propagate([[1], [-1]])[0])
        self.assertTrue(oracle.propagate([[]])[0])
        self.assertTrue(oracle.propagate([[1, 2]], [-1, -2])[0])
        self.assertTrue(oracle.propagate([], [1, -1])[0])

    def test_a_repeat_is_one_literal_and_a_tautology_is_inert(self):
        self.assertEqual(oracle.propagate([[1, 1]]), (False, frozenset({1})))
        self.assertEqual(oracle.propagate([[1, -1]]), (False, frozenset()))
        self.assertEqual(oracle.propagate([[1, -1, 2]], [-2]), (False, frozenset({-2})))
        # with 1 false, -1 is true and the tautology is satisfied, not a conflict
        self.assertEqual(oracle.propagate([[1, -1]], [-1]), (False, frozenset({-1})))

    def test_does_not_search(self):
        self.assertEqual(oracle.propagate(SQUARE), (False, frozenset()))


class TestRup(unittest.TestCase):
    def test_known_answers(self):
        self.assertTrue(oracle.rup(SQUARE, [1]))
        self.assertTrue(oracle.rup(SQUARE, [-2]))
        self.assertFalse(oracle.rup(SQUARE, []))
        self.assertTrue(oracle.rup([*SQUARE, [1]], []))
        self.assertTrue(oracle.rup([[1, 2]], [1, 2]))   # a copy of a clause
        self.assertTrue(oracle.rup([[1, 2]], [2, 1, 3]))
        self.assertTrue(oracle.rup([], [1, -1]))        # tautology
        self.assertFalse(oracle.rup([], [1]))
        self.assertTrue(oracle.rup([[]], [1]))          # the input has the empty clause

    def test_implied_is_not_enough(self):
        # (1) follows, but with 1 false what is left has no unit to propagate
        f = [[1, 2, 3], [1, 2, -3], [1, -2, 3], [1, -2, -3]]
        self.assertTrue(oracle.implies(f, [1]))
        self.assertFalse(oracle.rup(f, [1]))

    def test_a_repeat_changes_nothing(self):
        for lemma in ([1], [1, 1], [1, 1, 1]):
            self.assertTrue(oracle.rup(SQUARE, lemma))


class TestRat(unittest.TestCase):
    def test_vacuous_when_nothing_contains_the_negated_pivot(self):
        self.assertTrue(oracle.rat([[2, 3]], [1], 1))
        self.assertTrue(oracle.rat([], [1], 1))

    def test_the_pivot_decides(self):
        # F = (-1 2)(2 3). Lemma (1 -2) is not RUP.
        # On 1: the only candidate is (-1 2); the resolvent (1 -2 2) is a tautology.
        # On -2: (-1 2) gives (1 -2 -1), a tautology, but (2 3) gives (1 -2 3).
        # Assuming -1, 2, -3 satisfies both clauses, so that one is not RUP.
        f = [[-1, 2], [2, 3]]
        self.assertFalse(oracle.rup(f, [1, -2]))
        self.assertTrue(oracle.rat(f, [1, -2], 1))
        self.assertFalse(oracle.rat(f, [1, -2], -2))

    def test_the_pivot_must_be_in_the_clause(self):
        with self.assertRaises(ValueError):
            oracle.rat([[1]], [2], 1)
        with self.assertRaises(ValueError):
            oracle.rat([[1]], [], 1)

    def test_extended_resolution_is_rat_step_by_step(self):
        # define 3 as 1 AND 2
        f = [[1, 2]]
        for lemma in ([-3, 1], [-3, 2], [3, -1, -2]):
            self.assertFalse(oracle.rup(f, lemma))
            self.assertTrue(oracle.rat(f, lemma, lemma[0]), lemma)
            f.append(lemma)

    def test_a_clause_that_loses_models_for_good_is_not_rat(self):
        f = [[1, 2], [-1, 2]]
        self.assertFalse(oracle.preserves_sat(f, [-2]))
        self.assertFalse(oracle.rat(f, [-2], -2))

    def test_deletion_can_turn_a_step_into_rat(self):
        # With (2 3) present, (-2) is not RAT. Without it, it is vacuous.
        self.assertFalse(oracle.rat([[2, 3]], [-2], -2))
        self.assertTrue(oracle.rat([], [-2], -2))

    def test_every_copy_is_a_candidate_and_the_answer_is_the_same(self):
        self.assertEqual(oracle.rat([[2, 3], [2, 3]], [-2], -2), oracle.rat([[2, 3]], [-2], -2))


class TestTheorems(unittest.TestCase):
    """What the definitions guarantee, over random tiny formulas."""

    def test_rup_is_implied_and_rat_preserves_satisfiability(self):
        rng = random.Random(1729)
        counts = {"rup": 0, "rat": 0, "neither": 0}
        for _ in range(6000):
            nvars = rng.randint(1, 6)
            f = random_formula(rng, nvars, rng.randint(0, 14), maxlen=3)
            c = [rng.choice((1, -1)) * rng.randint(1, nvars + 1)
                 for _ in range(rng.randint(0, 3))]
            if oracle.rup(f, c):
                counts["rup"] += 1
                self.assertTrue(oracle.implies(f, c), (f, c))
                # AT implies RAT on any literal: each resolvent contains C
                for l in c:
                    self.assertTrue(oracle.rat(f, c, l), (f, c, l))
            elif c and oracle.rat(f, c, c[0]):
                counts["rat"] += 1
                self.assertTrue(oracle.preserves_sat(f, c), (f, c))
            else:
                counts["neither"] += 1
        self.assertTrue(all(counts.values()), counts)


class TestPseudoUnit(unittest.TestCase):
    def test_known_answers(self):
        f = [[1], [-1, 2], [3, 4]]
        self.assertTrue(oracle.is_pseudo_unit(f, [1]))
        self.assertTrue(oracle.is_pseudo_unit(f, [-1, 2]))
        self.assertFalse(oracle.is_pseudo_unit(f, [3, 4]))
        self.assertTrue(oracle.is_pseudo_unit(f, [2, -1, -1]))


class TestReplay(unittest.TestCase):
    def test_a_refutation(self):
        steps, final = oracle.replay(SQUARE, [("a", [1]), ("a", [])])
        self.assertEqual([s.rup for s in steps], [True, True])
        self.assertEqual(final[-1], [])

    def test_stops_at_a_bad_step_unless_told_not_to(self):
        bad = [("a", [-2]), ("a", [])]
        f = [[1, 2], [-1, 2]]
        steps, _ = oracle.replay(f, bad)
        self.assertEqual(len(steps), 1)
        self.assertFalse(steps[0].acceptable)
        steps, _ = oracle.replay(f, bad, stop_at_unacceptable=False)
        self.assertEqual(len(steps), 2)

    def test_multiset_deletion(self):
        f = [[1, 2], [2, 1]]
        steps, final = oracle.replay(f, [("d", [1, 2])])
        self.assertTrue(steps[0].applied)
        self.assertEqual(len(final), 1)
        steps, final = oracle.replay(f, [("d", [1, 2]), ("d", [2, 1]), ("d", [1, 2])])
        self.assertEqual([s.applied for s in steps], [True, True, False])
        self.assertEqual([s.present for s in steps], [True, True, False])
        self.assertEqual(final, [])

    def test_the_flavours_differ_exactly_where_they_should(self):
        f = [[1], [-1, 2], [3, 4]]
        expected = {
            # deleting the unit, the reason clause, and an unrelated clause
            "specified": [True, True, True],
            "operational": [False, False, True],
            "length-one": [False, True, True],
        }
        proof = [("d", [1]), ("d", [-1, 2]), ("d", [3, 4])]
        for flavour, applied in expected.items():
            steps, _ = oracle.replay(f, proof, flavour)
            self.assertEqual([s.applied for s in steps], applied, flavour)

    def test_a_step_that_rat_needs_a_deletion_for(self):
        # Specified: with the reason clause gone, (-2) is vacuously RAT and the
        # result is satisfiable, so nothing refutes the formula.
        f = [[1], [-1, 2]]
        proof = [("d", [-1, 2]), ("a", [-2]), ("a", [])]
        steps, _ = oracle.replay(f, proof, "specified")
        self.assertTrue(steps[1].rat_on_first)
        self.assertTrue(steps[1].preserves_sat)
        self.assertFalse(steps[2].acceptable)
        # Operational: the deletion is ignored, so (-2) is not RAT.
        steps, _ = oracle.replay(f, proof, "operational")
        self.assertFalse(steps[0].applied)
        self.assertFalse(steps[1].acceptable)

    def test_operational_does_not_depend_on_clause_order_after_a_conflict(self):
        # Found in review: the partial assignment at a conflict depends on the
        # order of the clauses, and it used to decide whether a deletion ran.
        proof = [("d", [-1]), ("a", [])]
        for f in ([[1], [-1]], [[-1], [1]]):
            steps, final = oracle.replay(f, proof, "operational")
            self.assertFalse(steps[0].applied, f)
            self.assertTrue(steps[1].acceptable, f)
            self.assertEqual(len(final), 3, f)

    def test_operational_keeps_a_conflict_a_lemma_reached(self):
        f = [[1, 2], [1, -2], [-1, 3], [-1, -3]]
        for victim in ([-1, 3], [-1, -3]):
            proof = [("a", [1]), ("d", victim), ("a", [])]
            steps, _ = oracle.replay(f, proof, "operational")
            self.assertFalse(steps[1].applied, victim)
            self.assertTrue(steps[2].acceptable, victim)

    def test_preserves_sat_applies_the_limit_whatever_the_answer(self):
        unsat = [[1], [-1]]
        with self.assertRaises(ValueError):
            oracle.preserves_sat(unsat, list(range(2, 19)))

    def test_refuses_a_flavour_it_does_not_know(self):
        with self.assertRaises(ValueError):
            oracle.replay([], [], "backward")


if __name__ == "__main__":
    unittest.main()
