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
        rng = random.Random(11)
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
        rng = random.Random(5)
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
