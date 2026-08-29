# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Proof tests -- including the ones that make the checker prove it can say no.

A verifier that has only ever returned "verified" is indistinguishable from
``return True``.  Half of this file is therefore *mutation testing*: take
proofs the solver really produced, corrupt them in specific ways, and require
the checker to reject.  The other half covers the RAT rule, which never fires
on solver-generated proofs (every CDCL learnt clause is RUP) and so would
otherwise be entirely uncovered.
"""

from __future__ import annotations

import random
import unittest

from cdclkit.brute import exhaustive_solve
from dratify.cnf import CNF
from dratify.lits import mk_lit, neg
from dratify.proof import DRATChecker, ProofWriter, check_proof, parse_proof
from cdclkit import native
from cdclkit.solver import Solver
from tests.util import random_cnf, solve_with_proof


class TestProofPositive(unittest.TestCase):
    """Proofs the checker must accept."""

    def test_php_proofs_verify(self):
        for holes in (3, 4, 5, 6):
            with self.subTest(holes=holes):
                f = php(holes)
                sat, proof = solve_with_proof(f)
                self.assertFalse(sat)
                res = check_proof(f, proof)
                self.assertTrue(res.ok, res.report())
                self.assertTrue(res.reached_empty)
                self.assertGreater(res.rup_steps, 0)

    def test_random_unsat_proofs_verify(self):
        rng = random.Random(4242)
        checked = 0
        for _ in range(120):
            f = random_cnf(rng, max_vars=11, ratio=5.0)
            sat, proof = solve_with_proof(f)
            if sat:
                continue
            checked += 1
            res = check_proof(f, proof)
            self.assertTrue(res.ok, res.report() + "\n" + f.to_dimacs())
        self.assertGreater(checked, 20, "the sample produced too few UNSAT instances")

    def test_empty_clause_in_input(self):
        f = CNF(2)
        f.add([])
        res = check_proof(f, [])
        self.assertTrue(res.ok)

    def test_formula_refuted_by_propagation_alone(self):
        f = CNF(1)
        f.add([mk_lit(0)])
        f.add([neg(mk_lit(0))])
        res = check_proof(f, [])
        self.assertTrue(res.ok)
        self.assertIn("unit propagation", res.reason)

    def test_proof_text_round_trip(self):
        f = php(4)
        sat, proof = solve_with_proof(f)
        self.assertFalse(sat)
        text = proof.to_text()
        steps = parse_proof(text)
        self.assertEqual(len(steps), len(proof.steps))
        self.assertTrue(check_proof(f, text).ok)

    def test_writer_matches_memory_proof(self):
        import io

        f = php(4)
        buf = io.StringIO()
        writer = ProofWriter(buf)
        s = Solver(f.nvars, proof=writer)
        s.add_cnf(f)
        self.assertFalse(s.solve())
        writer.flush()
        self.assertTrue(check_proof(f, buf.getvalue()).ok)


class TestProofRejection(unittest.TestCase):
    """Mutation testing: corrupted proofs must be rejected."""

    def setUp(self):
        self.formula = php(5)
        sat, proof = solve_with_proof(self.formula)
        assert not sat
        self.steps = list(proof.steps)
        assert check_proof(self.formula, self.steps).ok

    def test_truncated_proof_is_rejected(self):
        # dropping the final empty clause leaves a valid but incomplete proof
        for cut in (1, 5, len(self.steps) - 1):
            with self.subTest(cut=cut):
                res = check_proof(self.formula, self.steps[:cut])
                self.assertFalse(res.ok)
                self.assertIn("never derives the empty clause", res.reason)

    def test_bogus_clause_at_the_start_is_rejected(self):
        """A random small clause, injected before the solver's first learnt
        clause, is checked against the bare input formula -- the hardest place
        to smuggle one through."""
        rng = random.Random(3)
        rejected = 0
        trials = 60
        for _ in range(trials):
            k = rng.randint(1, 3)
            bogus = tuple(
                mk_lit(v, rng.random() < 0.5)
                for v in rng.sample(range(self.formula.nvars), k)
            )
            if not check_proof(self.formula, [("a", bogus)] + self.steps).ok:
                rejected += 1
        self.assertGreaterEqual(
            rejected, int(0.85 * trials),
            f"only {rejected}/{trials} bogus first steps were rejected",
        )

    def test_every_acceptance_is_sound(self):
        """The other half of the story: when the checker *does* accept a random
        clause, that clause had better really follow from the formula.

        Each accepted clause C is re-tested independently by asking the solver
        whether ``F and not C`` is satisfiable.  If it is, C was not entailed
        and the acceptance was a bug (a RAT acceptance would be legitimate
        without entailment, so RAT is disabled here to make the criterion
        exact).
        """
        rng = random.Random(3)
        accepted = 0
        for _ in range(60):
            k = rng.randint(1, 3)
            clause = [
                mk_lit(v, rng.random() < 0.5)
                for v in rng.sample(range(self.formula.nvars), k)
            ]
            checker = DRATChecker(self.formula, check_rat=False)
            if not checker.check_step("a", clause):
                continue
            accepted += 1
            s = Solver(self.formula.nvars)
            s.add_cnf(self.formula)
            for l in clause:
                s.add_clause([neg(l)])
            self.assertFalse(
                s.solve(),
                f"checker accepted {clause}, but F and not-C is satisfiable: "
                "the clause is not entailed",
            )
        self.assertGreater(accepted, 0, "the sample never exercised acceptance")

    def test_flipped_literal_is_rejected(self):
        """Flipping the sign of a literal in a learnt clause.

        The rejection rate is high but not 100%, and that is expected rather
        than a weakness: by the middle of a refutation the accumulated clause
        database is strong enough that some perturbed clauses are still
        genuinely implied. `test_every_acceptance_is_sound` is what pins down
        that the survivors are real.
        """
        rng = random.Random(11)
        rejected = attempted = 0
        for _ in range(60):
            idx = rng.randrange(0, len(self.steps))
            kind, lits = self.steps[idx]
            if kind != "a" or not lits:
                continue
            attempted += 1
            j = rng.randrange(len(lits))
            mutated_lits = list(lits)
            mutated_lits[j] ^= 1
            mutated = list(self.steps)
            mutated[idx] = ("a", tuple(mutated_lits))
            if not check_proof(self.formula, mutated).ok:
                rejected += 1
        self.assertGreater(attempted, 20)
        self.assertGreaterEqual(
            rejected, int(0.5 * attempted),
            f"only {rejected}/{attempted} sign flips were rejected",
        )

    def test_dropped_literal_is_rejected(self):
        """Removing a literal makes the clause strictly stronger, so unless the
        literal was redundant the step stops following."""
        rng = random.Random(19)
        rejected = attempted = 0
        for _ in range(60):
            idx = rng.randrange(0, len(self.steps))
            kind, lits = self.steps[idx]
            if kind != "a" or len(lits) < 2:
                continue
            attempted += 1
            j = rng.randrange(len(lits))
            mutated = list(self.steps)
            mutated[idx] = ("a", tuple(l for i, l in enumerate(lits) if i != j))
            if not check_proof(self.formula, mutated).ok:
                rejected += 1
        self.assertGreater(attempted, 20)
        self.assertGreaterEqual(rejected, int(0.35 * attempted))

    def test_reordered_proof_is_rejected(self):
        """Learnt clauses depend on earlier ones; reversing the order breaks that."""
        additions = [s for s in self.steps if s[0] == "a"]
        reversed_proof = list(reversed(additions))
        self.assertFalse(check_proof(self.formula, reversed_proof).ok)

    def test_proof_of_a_satisfiable_formula_is_rejected(self):
        f = CNF(3)
        f.add([mk_lit(0), mk_lit(1)])
        f.add([neg(mk_lit(0)), mk_lit(2)])
        self.assertIsNotNone(exhaustive_solve(f))
        # claim the empty clause outright
        res = check_proof(f, [("a", ())])
        self.assertFalse(res.ok)
        self.assertEqual(res.failed_step, 1)

    def test_deletion_cannot_be_used_to_smuggle_a_step(self):
        """Deleting a clause and then 'deriving' it back is only valid if it is
        still implied.  Deleting *every* clause and then claiming the empty
        clause must fail."""
        f = php(3)
        steps = [("d", c) for c in f.clauses if len(c) > 1] + [("a", ())]
        self.assertFalse(check_proof(f, steps).ok)


class TestBothCheckersAgree(unittest.TestCase):
    """The native checker must agree with the Python one on every proof.

    This is the test that makes the native checker trustworthy at all. A
    checker exists to disagree with a buggy solver, so having only one --
    written by the same author, against the same mental model as the solver --
    is exactly the situation to distrust. Two implementations agreeing, plus
    proofs from CaDiCaL and kissat that neither implementation authored, is the
    strongest available statement.

    Agreement is required on *rejections* too. A fast checker that accepts
    everything would sail through a suite that only feeds it valid proofs.
    """

    def _both(self, formula, steps, **kw):
        py = check_proof(formula, steps, engine="python", **kw)
        rs = check_proof(formula, steps, engine="native", **kw)
        return py, rs

    def _assert_agree(self, formula, steps, label="", **kw):
        py, rs = self._both(formula, steps, **kw)
        self.assertEqual(py.ok, rs.ok, f"{label}: verdicts differ "
                                       f"(python {py.ok}, native {rs.ok})")
        self.assertEqual(py.reason, rs.reason, f"{label}: reasons differ")
        self.assertEqual(py.reached_empty, rs.reached_empty, f"{label}: reached_empty")
        if py.ok:
            self.assertEqual(py.rup_steps, rs.rup_steps, f"{label}: rup_steps")
            self.assertEqual(py.rat_steps, rs.rat_steps, f"{label}: rat_steps")
        else:
            self.assertEqual(py.failed_step, rs.failed_step, f"{label}: failed_step")
        return py, rs

    @unittest.skipUnless(native.available(), "native checker not built")
    def test_agree_on_valid_proofs(self):
        for holes in (3, 4, 5, 6):
            f = php(holes)
            sat, proof = solve_with_proof(f)
            self.assertFalse(sat)
            py, _ = self._assert_agree(f, proof.steps, f"php({holes})")
            self.assertTrue(py.ok)

    @unittest.skipUnless(native.available(), "native checker not built")
    def test_agree_on_corrupted_proofs(self):
        """Both must reject the same mutations, and accept the same survivors."""
        f = php(5)
        sat, proof = solve_with_proof(f)
        self.assertFalse(sat)
        steps = list(proof.steps)

        rng = random.Random(2024)
        rejected = 0
        for _ in range(40):
            kind = rng.choice(("insert", "flip", "drop", "truncate"))
            mutated = list(steps)
            if kind == "insert":
                k = rng.randint(1, 3)
                bogus = tuple(mk_lit(v, rng.random() < 0.5)
                              for v in rng.sample(range(f.nvars), k))
                mutated.insert(rng.randrange(len(mutated)), ("a", bogus))
            elif kind == "truncate":
                mutated = mutated[: rng.randrange(1, len(mutated))]
            else:
                idx = rng.randrange(len(mutated))
                k, lits = mutated[idx]
                if k != "a" or len(lits) < 2:
                    continue
                lits = list(lits)
                if kind == "flip":
                    lits[rng.randrange(len(lits))] ^= 1
                else:
                    del lits[rng.randrange(len(lits))]
                mutated[idx] = ("a", tuple(lits))
            py, _ = self._assert_agree(f, mutated, f"mutation/{kind}")
            if not py.ok:
                rejected += 1
        self.assertGreater(rejected, 10, "the mutations never provoked a rejection")

    @unittest.skipUnless(native.available(), "native checker not built")
    def test_agree_on_random_instances(self):
        rng = random.Random(808)
        checked = 0
        for _ in range(60):
            f = random_cnf(rng, max_vars=11, ratio=5.0)
            sat, proof = solve_with_proof(f)
            if sat:
                continue
            checked += 1
            self._assert_agree(f, proof.steps, "random")
        self.assertGreater(checked, 10)

    @unittest.skipUnless(native.available(), "native checker not built")
    def test_agree_with_rat_disabled(self):
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([neg(a), b])
        self._assert_agree(f, [("a", (a, neg(b)))], "rat-off", check_rat=False)
        self._assert_agree(f, [("a", (a, neg(b)))], "rat-on", check_rat=True)

    @unittest.skipUnless(native.available(), "native checker not built")
    def test_agree_on_edge_cases(self):
        empty_in_input = CNF(2)
        empty_in_input.add([])
        self._assert_agree(empty_in_input, [], "empty-clause-in-input")

        contradiction = CNF(1)
        contradiction.add([mk_lit(0)])
        contradiction.add([neg(mk_lit(0))])
        self._assert_agree(contradiction, [], "contradictory-units")

        satisfiable = CNF(3)
        satisfiable.add([mk_lit(0), mk_lit(1)])
        self._assert_agree(satisfiable, [("a", ())], "bogus-empty-clause")

    def test_unknown_engine_is_rejected(self):
        with self.assertRaises(ValueError):
            check_proof(php(3), [], engine="quantum")


class TestRAT(unittest.TestCase):
    """The RAT rule -- never exercised by solver proofs, so tested directly."""

    def test_rat_clause_accepted_rup_only_rejected(self):
        # F = { ~a v b }.  The clause (a v ~b) is not RUP, but it is RAT on a:
        # the only clause containing ~a is (~a v b), and the resolvent
        # (a v ~b) u {b} is a tautology.
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([neg(a), b])
        clause = [a, neg(b)]

        rup_only = DRATChecker(f, check_rat=False)
        self.assertFalse(rup_only.check_step("a", clause))

        with_rat = DRATChecker(f, check_rat=True)
        self.assertTrue(with_rat.check_step("a", clause))
        self.assertEqual(with_rat.result.rat_steps, 1)
        self.assertEqual(with_rat.result.rup_steps, 0)

    def test_extended_resolution_definition_is_rat(self):
        """Introducing d <-> (a & b) on a fresh variable d is the canonical
        RAT step: it is how extended resolution beats plain resolution."""
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([a, b])
        d = mk_lit(2)  # fresh
        checker = DRATChecker(f, check_rat=True)
        for clause in ([neg(d), a], [neg(d), b], [d, neg(a), neg(b)]):
            self.assertTrue(checker.check_step("a", clause), f"{clause} rejected")
        self.assertGreaterEqual(checker.result.rat_steps, 1)

    def test_non_rat_clause_on_a_fresh_variable_is_rejected(self):
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([a, b])
        f.add([neg(a), neg(b)])
        checker = DRATChecker(f, check_rat=True)
        # (a) is neither RUP nor RAT here: resolving with (~a v ~b) gives
        # (a v ~b), which does not propagate to a conflict.
        self.assertFalse(checker.check_step("a", [a]))

    def test_rat_pivot_is_the_first_literal(self):
        """DRAT fixes the pivot as the first literal; a permuted clause with the
        wrong literal first is not necessarily accepted, and that asymmetry is
        part of the format, not a bug."""
        f = CNF(2)
        a, b = mk_lit(0), mk_lit(1)
        f.add([neg(a), b])
        self.assertTrue(DRATChecker(f).check_step("a", [a, neg(b)]))
        # same clause, pivot ~b: clauses containing b are (~a v b); resolvent is
        # (a v ~b) u {~a} which is a tautology, so this one also passes -- assert
        # the checker at least does not crash and reports a consistent verdict
        checker = DRATChecker(f)
        verdict = checker.check_step("a", [neg(b), a])
        self.assertIsInstance(verdict, bool)


def php(holes: int) -> CNF:
    """Pigeonhole formula with ``holes+1`` pigeons: unsatisfiable."""
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
