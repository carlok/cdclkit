# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Encodings, verified exhaustively against their specifications.

The test criterion for an encoding of constraint ``C`` over inputs ``x`` is:

    for every assignment to x:  the encoding is satisfiable under that
    assignment  <=>  C holds under that assignment

which is checked by solving the encoding with the input assignment supplied as
*assumptions*.  That is stronger than checking a few models: it verifies the
encoding neither forbids a legal assignment nor permits an illegal one, over
the whole input space.
"""

from __future__ import annotations

import itertools
import random
import unittest

from tests.util import fuzz_seed

from dratify.cnf import CNF
from cdclkit.encodings import Encoder, Optimiser, Totalizer, optimise
from dratify.lits import mk_lit, neg
from cdclkit.solver import Solver

AMO_METHODS = ("pairwise", "binary", "commander", "sequential", "totalizer")
AMK_METHODS = ("sequential", "totalizer")


def check_against_spec(test, build, n, spec, label=""):
    """Exhaustively compare an encoding with a Python predicate."""
    f = CNF()
    xs = [mk_lit(f.new_var()) for _ in range(n)]
    enc = Encoder(f)
    build(enc, xs)
    for bits in itertools.product((0, 1), repeat=n):
        s = Solver(f.nvars)
        ok = s.add_cnf(f)
        assumptions = [xs[i] if bits[i] else neg(xs[i]) for i in range(n)]
        got = bool(ok and s.solve(assumptions))
        test.assertEqual(got, spec(bits), f"{label} n={n} bits={bits}")
    return f


class TestAtMostOne(unittest.TestCase):
    def test_all_methods(self):
        for method in AMO_METHODS:
            for n in (1, 2, 3, 5, 7):
                with self.subTest(method=method, n=n):
                    check_against_spec(
                        self,
                        lambda e, x, m=method: e.at_most_one(x, m),
                        n,
                        lambda b: sum(b) <= 1,
                        f"amo/{method}",
                    )

    def test_exactly_one(self):
        for method in AMO_METHODS:
            with self.subTest(method=method):
                check_against_spec(
                    self,
                    lambda e, x, m=method: e.exactly_one(x, m),
                    5,
                    lambda b: sum(b) == 1,
                    f"eo/{method}",
                )

    def test_commander_is_linear_in_size(self):
        f = CNF()
        xs = [mk_lit(f.new_var()) for _ in range(200)]
        enc = Encoder(f)
        enc.amo_commander(xs)
        pairwise_size = 200 * 199 // 2
        self.assertLess(f.nclauses, pairwise_size // 4)

    def test_pairwise_uses_no_auxiliary_variables(self):
        f = CNF()
        xs = [mk_lit(f.new_var()) for _ in range(10)]
        before = f.nvars
        Encoder(f).amo_pairwise(xs)
        self.assertEqual(f.nvars, before)


class TestCardinality(unittest.TestCase):
    def test_at_most_k(self):
        for method in AMK_METHODS:
            for n in (4, 6):
                for k in range(0, n + 1):
                    with self.subTest(method=method, n=n, k=k):
                        check_against_spec(
                            self,
                            lambda e, x, k=k, m=method: e.at_most_k(x, k, m),
                            n,
                            lambda b, k=k: sum(b) <= k,
                            f"amk/{method}",
                        )

    def test_at_least_k(self):
        for method in AMK_METHODS:
            for k in range(0, 6):
                with self.subTest(method=method, k=k):
                    check_against_spec(
                        self,
                        lambda e, x, k=k, m=method: e.at_least_k(x, k, m),
                        5,
                        lambda b, k=k: sum(b) >= k,
                        f"alk/{method}",
                    )

    def test_exactly_k(self):
        for k in range(0, 5):
            with self.subTest(k=k):
                check_against_spec(
                    self,
                    lambda e, x, k=k: e.exactly_k(x, k),
                    4,
                    lambda b, k=k: sum(b) == k,
                    "exk",
                )

    def test_totalizer_outputs_are_the_unary_count(self):
        n = 6
        f = CNF()
        xs = [mk_lit(f.new_var()) for _ in range(n)]
        enc = Encoder(f)
        tot = Totalizer(enc, xs)
        for bits in itertools.product((0, 1), repeat=n):
            s = Solver(f.nvars)
            s.add_cnf(f)
            self.assertTrue(s.solve([xs[i] if bits[i] else neg(xs[i]) for i in range(n)]))
            count = sum(bits)
            for i, o in enumerate(tot.outputs):
                got = s.model[o >> 1] != bool(o & 1)
                self.assertEqual(got, count >= i + 1, f"bits={bits} out[{i}]")

    def test_totalizer_bound_can_be_tightened_by_assumption(self):
        n = 5
        s = Solver()
        xs = [mk_lit(s.new_var()) for _ in range(n)]
        enc = Encoder(s)
        tot = Totalizer(enc, xs)
        s.add_clause(xs)  # at least one
        for k in range(n, 0, -1):
            bound = tot.at_most_lit(k)
            assumptions = [bound] if bound is not None else []
            self.assertTrue(s.solve(assumptions), f"<= {k} should be satisfiable")
            self.assertLessEqual(sum(1 for x in xs if s.model[x >> 1]), k)
        self.assertFalse(s.solve([tot.at_most_lit(0)]))


class TestArcConsistency(unittest.TestCase):
    """Propagation strength, measured rather than claimed."""

    def _propagates(self, method, n, k, fixed_true):
        s = Solver()
        xs = [mk_lit(s.new_var()) for _ in range(n)]
        Encoder(s).at_most_k(xs, k, method)
        for i in fixed_true:
            s.add_clause([xs[i]])
        s._propagate()
        rest = [i for i in range(n) if i not in fixed_true]
        return all(s.value(xs[i]) != 0 for i in rest)

    def test_sequential_and_totalizer_are_arc_consistent(self):
        for method in ("sequential", "totalizer"):
            with self.subTest(method=method):
                self.assertTrue(self._propagates(method, 6, 2, [0, 1]))

    def test_binary_amo_propagates_but_costs_auxiliary_branching(self):
        """The binary encoding's trade-off, measured.

        It *does* propagate ``x_i true => x_j false`` (the code bits become
        fixed, and every other input disagrees with the code in some bit), so
        on the input variables it is as strong as pairwise here.  What it
        actually costs is size-vs-structure: it introduces log2(n) auxiliary
        variables the solver can branch on, and it says nothing at all until
        some input is fixed true.  This test pins down both halves.
        """
        s = Solver()
        xs = [mk_lit(s.new_var()) for _ in range(8)]
        before = s.nvars
        Encoder(s).amo_binary(xs)
        self.assertEqual(s.nvars - before, 3, "expected ceil(log2 8) code bits")

        s.add_clause([xs[0]])
        s._propagate()
        self.assertTrue(all(s.value(xs[i]) != 0 for i in range(1, 8)))

        # with only negative information, nothing propagates -- and that is
        # true of every at-most-one encoding, since at-most-one says nothing
        # about the last remaining literal
        s2 = Solver()
        ys = [mk_lit(s2.new_var()) for _ in range(8)]
        Encoder(s2).amo_binary(ys)
        for i in range(7):
            s2.add_clause([neg(ys[i])])
        s2._propagate()
        self.assertEqual(s2.value(ys[7]), 0)

    def test_pairwise_amo_is_arc_consistent(self):
        s = Solver()
        xs = [mk_lit(s.new_var()) for _ in range(8)]
        Encoder(s).amo_pairwise(xs)
        s.add_clause([xs[0]])
        s._propagate()
        self.assertTrue(all(s.value(xs[i]) != 0 for i in range(1, 8)))


class TestPseudoBoolean(unittest.TestCase):
    def test_random_pb_constraints(self):
        rng = random.Random(fuzz_seed(11))
        for _ in range(20):
            n = rng.randint(1, 5)
            w = [rng.choice([-4, -2, -1, 1, 2, 3, 5]) for _ in range(n)]
            bound = rng.randint(-3, sum(abs(x) for x in w))
            check_against_spec(
                self,
                lambda e, x, w=w, b=bound: e.assert_pb_leq(w, x, b),
                n,
                lambda bits, w=w, b=bound: sum(w[i] for i in range(len(w)) if bits[i]) <= b,
                f"pb<= w={w} b={bound}",
            )

    def test_pb_geq_and_eq(self):
        w = [3, 2, 2, 1]
        for bound in range(0, 9):
            check_against_spec(
                self,
                lambda e, x, b=bound: e.assert_pb_geq(w, x, b),
                4,
                lambda bits, b=bound: sum(w[i] for i in range(4) if bits[i]) >= b,
                f"pb>= {bound}",
            )
        for value in range(0, 9):
            check_against_spec(
                self,
                lambda e, x, v=value: e.assert_pb_eq(w, x, v),
                4,
                lambda bits, v=value: sum(w[i] for i in range(4) if bits[i]) == v,
                f"pb== {value}",
            )


class TestTseitin(unittest.TestCase):
    OPS = ("and", "or", "not", "xor", "iff", "imp", "ite")

    def _eval(self, e, bits):
        if isinstance(e, int):
            return bits[e >> 1] != bool(e & 1)
        op = e[0]
        if op == "not":
            return not self._eval(e[1], bits)
        if op == "and":
            return all(self._eval(x, bits) for x in e[1:])
        if op == "or":
            return any(self._eval(x, bits) for x in e[1:])
        if op == "xor":
            return self._eval(e[1], bits) ^ self._eval(e[2], bits)
        if op == "iff":
            return self._eval(e[1], bits) == self._eval(e[2], bits)
        if op == "imp":
            return (not self._eval(e[1], bits)) or self._eval(e[2], bits)
        if op == "ite":
            return self._eval(e[2] if self._eval(e[1], bits) else e[3], bits)
        raise AssertionError(op)

    def _random_expr(self, xs, depth, rng):
        if depth == 0 or rng.random() < 0.3:
            l = rng.choice(xs)
            return l if rng.random() < 0.5 else neg(l)
        op = rng.choice(self.OPS)
        if op == "not":
            return ("not", self._random_expr(xs, depth - 1, rng))
        if op in ("xor", "iff", "imp"):
            return (op, self._random_expr(xs, depth - 1, rng),
                    self._random_expr(xs, depth - 1, rng))
        if op == "ite":
            return (op, self._random_expr(xs, depth - 1, rng),
                    self._random_expr(xs, depth - 1, rng),
                    self._random_expr(xs, depth - 1, rng))
        return (op,) + tuple(
            self._random_expr(xs, depth - 1, rng) for _ in range(rng.randint(2, 3))
        )

    def test_random_expression_trees(self):
        rng = random.Random(fuzz_seed(5))
        for _ in range(40):
            n = rng.randint(1, 4)
            f = CNF()
            xs = [mk_lit(f.new_var()) for _ in range(n)]
            expr = self._random_expr(xs, 3, rng)
            enc = Encoder(f)
            enc.assert_expr(expr)
            for bits in itertools.product((0, 1), repeat=n):
                s = Solver(f.nvars)
                ok = s.add_cnf(f)
                got = bool(ok and s.solve(
                    [xs[i] if bits[i] else neg(xs[i]) for i in range(n)]
                ))
                want = self._eval(expr, [bool(b) for b in bits])
                self.assertEqual(got, want, f"{expr} @ {bits}")

    def test_xor_chain(self):
        for n in range(1, 6):
            for value in (True, False):
                check_against_spec(
                    self,
                    lambda e, x, v=value: e.xor_chain(x, v),
                    n,
                    lambda bits, v=value: (sum(bits) % 2 == 1) == v,
                    f"xor n={n} v={value}",
                )

    def test_gate_caching_reuses_definitions(self):
        f = CNF()
        a, b = mk_lit(f.new_var()), mk_lit(f.new_var())
        enc = Encoder(f)
        g1 = enc.and_gate([a, b])
        g2 = enc.and_gate([b, a])
        self.assertEqual(g1, g2, "and-gates over the same inputs must be shared")

    def test_constant_folding(self):
        f = CNF()
        a = mk_lit(f.new_var())
        enc = Encoder(f)
        self.assertEqual(enc.and_gate([a, neg(a)]), enc.false_lit)
        self.assertEqual(enc.and_gate([]), enc.true_lit)


class TestOptimise(unittest.TestCase):
    def test_minimises_true_literals(self):
        s = Solver()
        xs = [mk_lit(s.new_var()) for _ in range(6)]
        # force at least 2 of the first 4 to be true
        Encoder(s).at_least_k(xs[:4], 2)
        res = optimise(s, xs)
        self.assertIsNotNone(res)
        count, model = res
        self.assertEqual(count, 2)
        self.assertEqual(sum(1 for x in xs if model[x >> 1]), 2)

    def test_maximise(self):
        s = Solver()
        xs = [mk_lit(s.new_var()) for _ in range(5)]
        Encoder(s).at_most_k(xs, 3)
        res = optimise(s, xs, minimise=False)
        self.assertIsNotNone(res)
        count, model = res
        self.assertEqual(count, 3)

    def test_optimiser_is_reusable(self):
        """The class form encodes its counter once and can be resumed."""
        s = Solver()
        xs = [mk_lit(s.new_var()) for _ in range(6)]
        Encoder(s).at_least_k(xs[:4], 2)
        before = s.nvars
        opt = Optimiser(s, xs)
        after_encoding = s.nvars
        self.assertEqual(opt.run()[0], 2)
        first_run_vars = s.nvars
        self.assertEqual(first_run_vars, after_encoding,
                         "the search must not add variables")
        # resume: demand something impossible, confirm the best is retained
        self.assertEqual(opt.run(target=0), (2, opt.best[1]))
        self.assertEqual(s.nvars, first_run_vars,
                         "a second run must not re-encode the totalizer")
        self.assertGreater(after_encoding, before)

    def test_optimiser_reports_progress_and_can_stop_early(self):
        s = Solver()
        xs = [mk_lit(s.new_var()) for _ in range(8)]
        Encoder(s).at_least_k(xs, 3)
        seen = []
        opt = Optimiser(s, xs)
        opt.run(max_iterations=1, on_improve=lambda n, m: seen.append(n))
        self.assertEqual(len(seen), 1)
        self.assertIsNotNone(opt.best)
        self.assertGreaterEqual(opt.best[0], 3)
        # resuming continues from the partial result
        final = opt.run(target=opt.best[0] - 1)
        self.assertEqual(final[0], 3)

    def test_permanent_bound_variant_agrees(self):
        for assumption_based in (True, False):
            s = Solver()
            xs = [mk_lit(s.new_var()) for _ in range(6)]
            Encoder(s).at_least_k(xs[:4], 2)
            res = optimise(s, xs, assumption_based=assumption_based)
            self.assertEqual(res[0], 2)

    def test_unsat_returns_none(self):
        s = Solver(1)
        s.add_clause([mk_lit(0)])
        s.add_clause([neg(mk_lit(0))])
        self.assertIsNone(optimise(s, [mk_lit(0)]))


if __name__ == "__main__":
    unittest.main()


class TestDifferentialEncoding(unittest.TestCase):
    """Encode the same constraint two ways; the answers must match.

    This is the one class of bug the proof machinery cannot reach. A DRAT
    refutation certifies the clauses it was handed; it says nothing about
    whether those clauses mean the constraint someone wrote down. Every
    verified solver and verified checker in the field takes CNF as its input
    and starts from there, so the translation into CNF is the last unchecked
    step in the whole pipeline -- including this one.
    """

    from cdclkit.model import (EncodingDisagreement, Model, differential_solve)

    def test_every_at_most_one_encoding_agrees(self):
        from cdclkit.model import differential_solve

        for n in range(2, 8):
            for k_extra in (0, 1, 2):
                with self.subTest(n=n, at_least=k_extra):
                    def build(m, n=n, k=k_extra):
                        xs = m.bool_vars(n, "x")
                        m.at_most_one(xs)
                        if k:
                            m.at_least_k(xs, k)
                    # satisfiable only when at_least <= 1
                    sol = differential_solve(
                        build, methods=("pairwise", "binary",
                                        "commander", "sequential"))
                    self.assertEqual(sol is not None, k_extra <= 1)

    def test_every_at_most_k_encoding_agrees(self):
        from cdclkit.model import differential_solve

        for n in (5, 7, 9):
            for k in range(1, n):
                with self.subTest(n=n, k=k):
                    def build(m, n=n, k=k):
                        xs = m.bool_vars(n, "x")
                        m.at_most_k(xs, k)
                        m.at_least_k(xs, k)      # forces exactly k
                    self.assertIsNotNone(
                        differential_solve(build,
                                           methods=("sequential", "totalizer")))

    def test_a_broken_encoding_is_caught(self):
        """The check has to be able to fail, or it is decoration.

        Simulated by an off-by-one that only fires under one method, which is
        exactly the shape of a real encoding bug: correct on the path that got
        tested, wrong on the one that did not.
        """
        import cdclkit.model as M
        from cdclkit.model import EncodingDisagreement, Model, differential_solve

        class OffByOne(Model):
            def at_most_k(self, items, k, method="auto"):
                if self.encoding_method == "totalizer":
                    k -= 1
                super().at_most_k(items, k, method)

        def build(m):
            xs = m.bool_vars(5, "x")
            m.at_most_k(xs, 2)
            m.at_least_k(xs, 2)

        original = M.Model
        M.Model = OffByOne
        try:
            with self.assertRaises(EncodingDisagreement):
                differential_solve(build, methods=("sequential", "totalizer"))
        finally:
            M.Model = original

    def test_the_override_only_applies_where_it_fits(self):
        """`pairwise` is an at-most-one method and cannot encode at-most-3.

        Constraints the override does not fit keep their own choice instead of
        raising, so a model mixing the two kinds still builds.
        """
        from cdclkit.model import Model

        m = Model(encoding_method="pairwise")
        xs = m.bool_vars(6, "x")
        m.at_most_one(xs)      # uses pairwise
        m.at_most_k(xs, 3)     # falls back: pairwise is not an at-most-k method
        self.assertIsNotNone(m.solve())

    def test_verify_off_skips_the_model_check(self):
        from cdclkit.model import differential_solve

        def build(m):
            xs = m.bool_vars(4, "x")
            m.exactly_k(xs, 2)

        self.assertIsNotNone(
            differential_solve(build, methods=("sequential", "totalizer"),
                               verify=False))

    def test_a_model_that_does_not_satisfy_its_own_cnf_is_blamed_on_the_solver(self):
        """An invalid model is a solver bug, and must not be reported as an
        encoding disagreement -- the two have completely different fixes."""
        import cdclkit.model as M
        from cdclkit.model import EncodingDisagreement, Model, differential_solve

        class LiesAboutTheModel(Model):
            def solve(self, proof=None, assumptions=()):
                sol = super().solve(proof, assumptions)
                if sol is not None:
                    sol.bits = [not b for b in sol.bits]   # corrupt it
                return sol

        def build(m):
            xs = m.bool_vars(4, "x")
            m.exactly_k(xs, 2)

        original = M.Model
        M.Model = LiesAboutTheModel
        try:
            with self.assertRaises(EncodingDisagreement) as cm:
                differential_solve(build, methods=("sequential", "totalizer"))
            self.assertIn("solver bug", str(cm.exception))
        finally:
            M.Model = original

    def test_a_single_method_is_allowed_and_checks_nothing(self):
        """Degenerate but legal: one method cannot disagree with itself."""
        from cdclkit.model import differential_solve

        def build(m):
            m.at_most_one(m.bool_vars(3, "x"))

        self.assertIsNotNone(differential_solve(build, methods=("pairwise",)))


class TestModellingOperators(unittest.TestCase):
    """The operator surface of the modelling layer, which had no tests.

    `BoolVar` overloads `& | ^ >> ~` and `iff`, and `IntVar` overloads `== !=`
    plus `in_`, `ge`, `le`. They are the part of the API a user touches first
    and the part most likely to be quietly wrong, because an inverted operator
    still produces a well-formed formula with a plausible answer.
    """

    def _sat(self, build):
        from cdclkit.model import Model
        m = Model()
        build(m)
        return m.solve()

    def test_boolean_connectives_mean_what_they_say(self):
        from cdclkit.model import Model

        for expr, expect in (
            (lambda a, b: a & b, {(True, True)}),
            (lambda a, b: a | b, {(True, True), (True, False), (False, True)}),
            (lambda a, b: a ^ b, {(True, False), (False, True)}),
            (lambda a, b: a >> b, {(True, True), (False, True), (False, False)}),
            (lambda a, b: a.iff(b), {(True, True), (False, False)}),
        ):
            with self.subTest(expr=expr):
                got = set()
                for va in (False, True):
                    for vb in (False, True):
                        m = Model()
                        a, b = m.bool_var("a"), m.bool_var("b")
                        m.add(expr(a, b))
                        m.add_clause([a.lit ^ (0 if va else 1)])
                        m.add_clause([b.lit ^ (0 if vb else 1)])
                        if m.solve() is not None:
                            got.add((va, vb))
                self.assertEqual(got, expect)

    def test_negation_and_repr(self):
        from cdclkit.model import Model

        m = Model()
        a = m.bool_var("a")
        na = ~a
        self.assertIn("a", repr(a))
        self.assertIn("a", repr(na))
        m.add(a & na)                      # a and not-a
        self.assertIsNone(m.solve())

    def test_int_var_equality_membership_and_bounds(self):
        from cdclkit.model import Model

        m = Model()
        x = m.int_var(range(1, 6), "x")
        m.add(x != 3)
        m.add(x.in_([2, 3, 4]))
        sols = {s[x] for s in m.solutions(project=[x])}
        self.assertEqual(sols, {2, 4})

    def test_value_outside_the_domain_is_unsatisfiable_not_an_error(self):
        """`x == 99` when 99 is not in the domain is false, not a crash."""
        from cdclkit.model import Model

        m = Model()
        x = m.int_var(range(1, 4), "x")
        m.add(x == 99)
        self.assertIsNone(m.solve())
        self.assertIn("x", repr(x))

    def test_order_encoding_bounds(self):
        from cdclkit.model import Model

        m = Model()
        x = m.int_var(range(1, 10), "x", order=True)
        m.add_clause([x.ge(4)])
        m.add_clause([x.le(6)])
        sols = {s[x] for s in m.solutions(project=[x])}
        self.assertEqual(sols, {4, 5, 6})
        # a bound outside the domain is a constant, not an error
        self.assertIsInstance(x.ge(99), int)


class TestModelSolvesWhatItHolds(unittest.TestCase):
    """`Model.solve` reused its solver unless a *variable* had been added, so
    `add(x != first)` after a solve returned `first` again, and `solutions()`
    left its blocking clauses behind for the next `solve()` to answer from.

    Each answer is judged against the model's own CNF, not against the solver
    that produced it.
    """

    def test_a_constraint_without_a_new_variable_is_seen(self):
        from cdclkit.model import Model

        m = Model()
        x = m.int_var(range(3), "x")
        first = m.solve()[x]
        m.add(x != first)
        second = m.solve()
        self.assertNotEqual(second[x], first)
        self.assertTrue(m.cnf.is_satisfied_by(second.bits))

    def test_a_contradiction_after_a_solve_is_unsat(self):
        from cdclkit.model import Model

        m = Model()
        a = m.bool_var("a")
        self.assertIsNotNone(m.solve())
        m.add(a)
        m.add(~a)
        self.assertIsNone(m.solve())

    def test_equality_after_a_solve_is_honoured(self):
        from cdclkit.model import Model

        m = Model()
        x = m.int_var(range(1, 5), "x")
        m.solve()
        m.add(x == 3)
        self.assertEqual(m.solve()[x], 3)

    def test_a_new_proof_gets_a_proof(self):
        """An UNSAT answer from a solver built without the sink logged nothing,
        so the sink held no refutation of a formula that has one."""
        from dratify.proof import MemoryProof, check_proof

        from cdclkit.model import Model

        m = Model()
        p, q = m.bool_var("p"), m.bool_var("q")
        for clause in ([p, q], [~p, q], [p, ~q], [~p, ~q]):
            m.add_clause(clause)
        self.assertIsNone(m.solve())
        proof = MemoryProof()
        self.assertIsNone(m.solve(proof=proof))
        self.assertTrue(check_proof(m.cnf, proof.steps).ok)

    def test_an_unchanged_model_keeps_its_solver(self):
        """Learnt clauses survive for as long as they are still about this
        problem: rebuilding every time would be correct and wasteful."""
        from cdclkit.model import Model

        m = Model()
        m.bool_var("a")
        m.solve()
        s = m.solver
        m.solve()
        self.assertIs(m.solver, s)

    def test_enumeration_does_not_change_the_problem(self):
        from cdclkit.model import Model

        m = Model()
        a = m.bool_var("a")
        self.assertEqual(len(list(m.solutions(project=[a]))), 2)
        self.assertIsNotNone(m.solve())

    def test_a_partly_consumed_enumeration_excludes_nothing(self):
        from cdclkit.model import Model

        m = Model()
        a = m.bool_var("a")
        it = m.solutions(project=[a])
        seen = next(it)[a]
        next(it)
        m.add(a if seen else ~a)
        self.assertEqual(m.solve()[a], seen)
        self.assertEqual(len(list(m.solutions(project=[a]))), 1)

    def test_a_contradiction_replays_after_a_solve(self):
        from dratify.proof import MemoryProof, check_proof

        from cdclkit.model import Model

        m = Model()
        a = m.bool_var("a")
        m.solve()
        m.add(a)
        m.add(~a)
        proof = MemoryProof()
        self.assertIsNone(m.solve(proof=proof))
        self.assertTrue(check_proof(m.cnf, proof.steps).ok)


def _bool_solutions(build):
    from cdclkit.model import Model

    m = Model()
    a, b = m.bool_var("a"), m.bool_var("b")
    build(m, a, b)
    return {(s[a], s[b]) for s in m.solutions(project=[a, b])}


ALL_TWO = {(False, False), (False, True), (True, False), (True, True)}


class TestPythonBooleansInExpressions(unittest.TestCase):
    """`True` is the int 1, so it reached the encoder as literal 1, which is
    "not variable 0". `add(True)` asserted the first variable false and
    `add(a == b)`, which Python evaluated to `False`, asserted it true."""

    def test_add_true_constrains_nothing(self):
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add(True)), ALL_TWO)

    def test_add_false_is_unsat(self):
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add(False)), set())

    def test_constants_inside_a_tree_are_constants(self):
        cases = [
            (lambda m, a, b: m.add(b | False), {(False, True), (True, True)}),
            (lambda m, a, b: m.add(b & True), {(False, True), (True, True)}),
            (lambda m, a, b: m.add(b | True), ALL_TWO),
            (lambda m, a, b: m.add(b & False), set()),
            (lambda m, a, b: m.add(b >> False), {(False, False), (True, False)}),
            (lambda m, a, b: m.add(b ^ True), {(False, False), (True, False)}),
            (lambda m, a, b: m.add(("not", True)), set()),
        ]
        for i, (build, want) in enumerate(cases):
            with self.subTest(i=i):
                self.assertEqual(_bool_solutions(build), want)

    def test_a_clause_may_hold_a_constant(self):
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add_clause([b, False])),
                         {(False, True), (True, True)})
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add_clause([b, True])),
                         ALL_TWO)

    def test_a_cardinality_item_may_not_be_a_python_bool(self):
        """These take literals, and there is no literal to map it to here."""
        from cdclkit.model import Model

        m = Model()
        a = m.bool_var("a")
        with self.assertRaises(TypeError):
            m.at_most_one([True, a])
        with self.assertRaises(TypeError):
            m.exactly_k([False, a], 1)

    def test_equality_on_booleans_means_equality(self):
        same = {(False, False), (True, True)}
        differ = ALL_TWO - same
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add(a == b)), same)
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add(a != b)), differ)
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add(a == ~b)), differ)
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add(b == True)),  # noqa: E712
                         {(False, True), (True, True)})
        self.assertEqual(_bool_solutions(lambda m, a, b: m.add(b != True)),  # noqa: E712
                         {(False, False), (True, False)})

    def test_equality_with_anything_else_is_refused(self):
        """`a == 1` has no one meaning here: 1 is a literal and also Python's
        True. Falling back to Python's answer is how this bug got in."""
        from cdclkit.model import Model

        a = Model().bool_var("a")
        for other in (1, 0, "a", None):
            with self.subTest(other=other), self.assertRaises(TypeError):
                a == other
            with self.subTest(other=other), self.assertRaises(TypeError):
                a != other

    def test_booleans_stay_usable_as_keys_and_members(self):
        from cdclkit.model import Model

        m = Model()
        a, b = m.bool_var("a"), m.bool_var("b")
        self.assertEqual({a: 1, b: 2}[b], 2)
        self.assertEqual([a, b].index(a), 0)
        with self.assertRaises(TypeError):  # would answer 0 if it were truthy
            [a, b].index(b)

    def test_truth_of_a_variable_is_refused(self):
        """`a and b` is Python's `b`, and `not a` is Python's `False`. Neither
        reaches an operator, so there is nothing to compile: refuse."""
        from cdclkit.model import Model

        m = Model()
        a, b = m.bool_var("a"), m.bool_var("b")
        x = m.int_var(range(3), "x")
        for build in (lambda: a and b, lambda: a or b, lambda: not a,
                      lambda: x and b, lambda: not x):
            with self.assertRaises(TypeError):
                build()

    def test_a_wrong_answer_cannot_replay_any_more(self):
        """The finding's sharpest form: UNSAT with a passing proof, on a
        satisfiable problem."""
        from dratify.proof import MemoryProof, check_proof

        from cdclkit.model import Model

        m = Model()
        a, b = m.bool_var("a"), m.bool_var("b")
        m.add(~a)
        m.add(~b)
        m.add(a == b)
        sol = m.solve(proof=MemoryProof())
        self.assertIsNotNone(sol)
        self.assertEqual((sol[a], sol[b]), (False, False))


class TestTruncatedTotalizerPastTheCut(unittest.TestCase):
    """A truncated counter has no output past its cut, and it took that to mean
    the bound was vacuous, or impossible. `sum <= 1` over two inputs with
    `max_count=1` constrained nothing, and `sum >= 2` refuted a feasible problem
    with a proof that replays."""

    def _counter(self, n, max_count):
        f = CNF()
        xs = [mk_lit(f.new_var()) for _ in range(n)]
        return f, xs, Totalizer(Encoder(f), xs, max_count=max_count)

    def test_a_bound_it_cannot_express_is_refused(self):
        for method in ("assert_at_most", "at_most_lit"):
            with self.subTest(method=method), self.assertRaises(ValueError) as cm:
                _, _, t = self._counter(2, 1)
                getattr(t, method)(1)
            self.assertIn("max_count", str(cm.exception))
        for method in ("assert_at_least", "at_least_lit"):
            with self.subTest(method=method), self.assertRaises(ValueError):
                _, _, t = self._counter(2, 1)
                getattr(t, method)(2)

    def test_every_bound_it_does_answer_is_right(self):
        for n in range(1, 5):
            for cut in range(0, n + 2):
                for k in range(-1, n + 3):
                    for name, method, holds in (
                            ("<=", "assert_at_most", lambda c: c <= k),
                            (">=", "assert_at_least", lambda c: c >= k)):
                        f, xs, t = self._counter(n, cut)
                        try:
                            getattr(t, method)(k)
                        except ValueError:
                            self.assertGreaterEqual(k, cut)
                            self.assertLess(k, n if name == "<=" else n + 1)
                            continue
                        for bits in itertools.product((0, 1), repeat=n):
                            s = Solver(f.nvars)
                            ok = s.add_cnf(f)
                            got = bool(ok and s.solve([x if b else neg(x)
                                                       for x, b in zip(xs, bits)]))
                            self.assertEqual(got, holds(sum(bits)),
                                             f"n={n} cut={cut} sum{name}{k} {bits}")

    def test_the_truly_vacuous_and_impossible_cases_stay(self):
        _, _, t = self._counter(2, 1)
        self.assertIsNone(t.at_most_lit(2))
        self.assertIsNone(t.at_least_lit(0))
        self.assertEqual(t.at_least_lit(3), t.enc.false_lit)
        self.assertEqual(t.at_most_lit(-1), t.enc.false_lit)

    def test_at_most_k_through_the_totalizer_is_unaffected(self):
        check_against_spec(self, lambda e, xs: e.at_most_k(xs, 2, "totalizer"), 4,
                           lambda bits: sum(bits) <= 2)


class TestUndeclaredInputs(unittest.TestCase):
    """`CNF` and `Solver` both grow to cover a literal they have not seen, so
    `from_dimacs` hands out literals nothing has declared. An auxiliary variable was
    then the sink's next one, which could be one of the inputs: the binary encoding
    of two undeclared inputs read `x1 -> ~x1`."""

    def _agree(self, build, n, spec, sink=CNF):
        xs = [mk_lit(i) for i in range(n)]
        target = sink()
        build(Encoder(target), xs)
        f = target
        for bits in itertools.product((0, 1), repeat=n):
            if sink is CNF:
                s = Solver(f.nvars)
                ok = s.add_cnf(f)
            else:
                s, ok = target, True
            assumptions = [x if b else neg(x) for x, b in zip(xs, bits)]
            got = bool(ok and s.solve(assumptions))
            self.assertEqual(got, spec(bits), f"{bits}")

    def test_at_most_one(self):
        for method in AMO_METHODS + ("auto",):
            for n in (2, 3, 4, 7):
                for sink in (CNF, Solver):
                    with self.subTest(method=method, n=n, sink=sink.__name__):
                        self._agree(lambda e, xs: e.at_most_one(xs, method), n,
                                    lambda bits: sum(bits) <= 1, sink)

    def test_cardinality(self):
        for method in AMK_METHODS + ("auto",):
            for n, k in ((3, 1), (4, 2), (5, 3)):
                with self.subTest(method=method, n=n, k=k):
                    self._agree(lambda e, xs: e.at_most_k(xs, k, method), n,
                                lambda bits: sum(bits) <= k)
                    self._agree(lambda e, xs: e.at_least_k(xs, k, method), n,
                                lambda bits: sum(bits) >= k)
                    self._agree(lambda e, xs: e.exactly_k(xs, k, method), n,
                                lambda bits: sum(bits) == k)

    def test_gates_and_constants(self):
        def assert_output(gate):
            return lambda e, xs: e.add([gate(e, xs)])

        cases = [
            ("and", assert_output(lambda e, xs: e.and_gate(xs)), all),
            ("or", assert_output(lambda e, xs: e.or_gate(xs)), any),
            ("xor", assert_output(lambda e, xs: e.xor_gate(xs[0], xs[1])),
             lambda b: b[0] != b[1]),
            ("ite", assert_output(lambda e, xs: e.ite(xs[0], xs[1], neg(xs[1]))),
             lambda b: b[0] == b[1]),
        ]
        for label, build, spec in cases:
            with self.subTest(label=label):
                self._agree(build, 2, spec)

    def test_a_gate_over_a_contradiction_does_not_take_an_input(self):
        """The constant it returns needs a variable of its own."""
        f = CNF()
        enc = Encoder(f)
        x = mk_lit(0)
        self.assertEqual(enc.and_gate([x, neg(x)]) >> 1, 1)

    def test_expression_trees(self):
        def tree(e, xs):
            e.assert_expr(("or", True, ("and", xs[0], xs[1])))

        self._agree(tree, 2, lambda bits: True)
        self._agree(lambda e, xs: e.add([e.tseitin(("and", xs[0], xs[1]))]), 2, all)
        self._agree(lambda e, xs: e.assert_expr(("or", ("and", xs[0], xs[1]), xs[2])),
                    3, lambda b: (b[0] and b[1]) or b[2])
        self._agree(lambda e, xs: e.assert_expr(("not", ("xor", xs[0], False))), 1,
                    lambda b: not b[0])

    def test_pseudo_boolean_and_parity(self):
        self._agree(lambda e, xs: e.assert_pb_leq([2, 3, 1], xs, 3), 3,
                    lambda b: 2 * b[0] + 3 * b[1] + b[2] <= 3)
        self._agree(lambda e, xs: e.assert_pb_geq([2, 3, 1], xs, 3), 3,
                    lambda b: 2 * b[0] + 3 * b[1] + b[2] >= 3)
        self._agree(lambda e, xs: e.xor_chain(xs), 4, lambda b: sum(b) % 2 == 1)

    def test_totalizer_directly(self):
        self._agree(lambda e, xs: Totalizer(e, xs).assert_at_most(1), 3,
                    lambda bits: sum(bits) <= 1)


class TestNoInputs(unittest.TestCase):
    """A totalizer over nothing split its empty list in two for ever. A list built
    from data can come up empty, and only this method fell over on it."""

    def _sat(self, f):
        s = Solver(f.nvars)
        return bool(s.add_cnf(f) and s.solve())

    def test_at_most_one_of_nothing_holds(self):
        for method in AMO_METHODS + ("auto",):
            with self.subTest(method=method):
                f = CNF()
                Encoder(f).at_most_one([], method)
                self.assertTrue(self._sat(f))

    def test_exactly_one_of_nothing_is_impossible(self):
        for method in AMO_METHODS + ("auto",):
            with self.subTest(method=method):
                f = CNF()
                Encoder(f).exactly_one([], method)
                self.assertFalse(self._sat(f))

    def test_the_counter_counts_zero(self):
        f = CNF()
        t = Totalizer(Encoder(f), [])
        self.assertEqual(t.outputs, [])
        self.assertIsNone(t.at_most_lit(0))
        self.assertIsNone(t.at_least_lit(0))
        self.assertEqual(t.at_least_lit(1), t.enc.false_lit)
        self.assertEqual(t.at_most_lit(-1), t.enc.false_lit)

    def test_through_the_model(self):
        from cdclkit.model import Model

        m = Model()
        m.at_most_one([], method="totalizer")
        self.assertIsNotNone(m.solve())
        m = Model()
        m.exactly_one([], method="totalizer")
        self.assertIsNone(m.solve())


class TestNegativeK(unittest.TestCase):
    """A sum of booleans is never negative. `at_most_k` took k < 0 for k = 0 and
    forced everything false, which answered SAT, though `amk_sequential` and
    `amk_totalizer` under it, and `at_least_k` on the far side, all knew better. A
    negative bound comes from arithmetic: `budget - used`, once it has gone over."""

    def _sat(self, f):
        s = Solver(f.nvars)
        return bool(s.add_cnf(f) and s.solve())

    def test_nothing_is_at_most_or_exactly_negative(self):
        for name in ("at_most_k", "exactly_k"):
            for method in AMK_METHODS + ("auto",):
                for n in (0, 1, 3):
                    with self.subTest(name=name, method=method, n=n):
                        f = CNF()
                        xs = [mk_lit(f.new_var()) for _ in range(n)]
                        getattr(Encoder(f), name)(xs, -1, method)
                        self.assertFalse(self._sat(f))

    def test_at_most_k_mirrors_at_least_k(self):
        """`at_least_k(lits, n + 1)` is `at_most_k(~lits, -1)`, says its docstring."""
        for n in (1, 3):
            f, g = CNF(), CNF()
            xs = [mk_lit(f.new_var()) for _ in range(n)]
            ys = [mk_lit(g.new_var()) for _ in range(n)]
            Encoder(f).at_least_k(xs, n + 1)
            Encoder(g).at_most_k([neg(y) for y in ys], -1)
            self.assertEqual(self._sat(f), self._sat(g))

    def test_through_the_model(self):
        from cdclkit.model import Model

        for method in ("auto", "sequential", "totalizer"):
            for name in ("at_most_k", "exactly_k"):
                with self.subTest(method=method, name=name):
                    m = Model()
                    getattr(m, name)([m.bool_var("x")], -1, method=method)
                    self.assertIsNone(m.solve())
        m = Model()
        m.at_most_k([], -1)
        self.assertIsNone(m.solve())

    def test_zero_still_means_none(self):
        f = CNF()
        xs = [mk_lit(f.new_var()) for _ in range(2)]
        Encoder(f).at_most_k(xs, 0)
        self.assertTrue(self._sat(f))

