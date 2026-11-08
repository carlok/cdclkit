# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Python equivalence checking: proofs, counterexamples, and loud rejection.

Three properties matter, in this order:

1. **Soundness of "equivalent".** If it says two functions agree, they must
   agree at the declared width -- checked here against exhaustive enumeration
   at widths small enough to enumerate.
2. **Soundness of counterexamples.** If it hands back an input, the two
   functions must genuinely differ there.
3. **Loud rejection.** Anything outside the modelled subset must raise rather
   than be approximated, because a checker that silently ignores a construct
   makes every "equivalent" answer meaningless.
"""

from __future__ import annotations

import itertools
import unittest

from cdclkit import native

from cdclkit.pyeq import UnsupportedConstruct, equivalent


def exhaustive_agree(f, g, widths):
    """Ground truth by enumeration over every input at the declared width.

    Only valid for functions whose *intermediate* values cannot overflow.
    Running `f` in Python and wrapping the result is not the same as wrapping
    every operation: at 5 bits with a=-16, b=15, `a - b` is -31 in Python and
    +1 in the circuit, so a subsequent `if d < 0` takes different branches.
    Comparing against a naive Python reference would then blame the circuit for
    being right. Functions used with this helper therefore avoid arithmetic
    that can leave the range.
    """
    names = list(widths)
    w = max(widths.values())
    lo, hi = -(1 << (w - 1)), (1 << (w - 1))

    def wrap(v):
        v &= (1 << w) - 1
        return v - (1 << w) if v >= (1 << (w - 1)) else v

    for combo in itertools.product(*[range(lo, hi) for _ in names]):
        kw = dict(zip(names, combo))
        if wrap(f(**kw)) != wrap(g(**kw)):
            return False, kw
    return True, None


class TestProofs(unittest.TestCase):
    def test_algebraic_refactor_is_proved(self):
        def slow(a, b):
            return a * 2 + b * 2

        def fast(a, b):
            return (a + b) << 1

        r = equivalent(slow, fast, widths={"a": 8, "b": 8})
        self.assertTrue(r.proved, r.report())

    def test_identity_refactors(self):
        cases = [
            (lambda x: x + 0, lambda x: x),
            (lambda x: x * 8, lambda x: x << 3),
            (lambda x: x & x, lambda x: x),
            (lambda x: x ^ 0, lambda x: x),
            (lambda x: -(-x), lambda x: x),
            (lambda x: x | 0, lambda x: x),
        ]
        # lambdas have no retrievable multi-line source in some contexts, so
        # define real functions for the ones we actually compile
        def f1(x): return x + 0
        def g1(x): return x
        def f2(x): return x * 8
        def g2(x): return x << 3
        def f3(x): return -(-x)
        def g3(x): return x
        for f, g, label in ((f1, g1, "+0"), (f2, g2, "*8 vs <<3"),
                            (f3, g3, "double negation")):
            with self.subTest(case=label):
                self.assertTrue(equivalent(f, g, widths={"x": 6}).proved)

    def test_branches_and_early_return(self):
        def max_a(a, b):
            if a > b:
                return a
            return b

        def max_b(a, b):
            m = b
            if a > b:
                m = a
            return m

        self.assertTrue(equivalent(max_a, max_b, widths={"a": 5, "b": 5}).proved)

    def test_unrolled_loop_matches_closed_form(self):
        def accumulate(n):
            t = 0
            for _i in range(4):
                t = t + n
            return t

        def closed(n):
            return n * 4

        self.assertTrue(equivalent(accumulate, closed, widths={"n": 6}).proved)

    def test_proof_agrees_with_exhaustive_enumeration(self):
        """The claim 'equivalent' must survive brute force at a small width.

        These select rather than compute, so no intermediate can overflow and
        Python's semantics coincide with the circuit's -- see
        `exhaustive_agree`.
        """
        def f(a, b):
            if a < b:
                return b
            return a

        def g(a, b):
            m = a
            if b > a:
                m = b
            return m

        widths = {"a": 5, "b": 5}
        proved = equivalent(f, g, widths=widths).proved
        truth, _ = exhaustive_agree(f, g, widths)
        self.assertTrue(truth, "the reference itself should find them equal")
        self.assertEqual(proved, truth)

    def test_disagreement_agrees_with_exhaustive_enumeration(self):
        """And the negative direction: when brute force finds a difference,
        the checker must find one too."""
        def f(a, b):
            if a < b:
                return b
            return a

        def wrong(a, b):
            if a < b:
                return a
            return b

        widths = {"a": 5, "b": 5}
        r = equivalent(f, wrong, widths=widths)
        truth, witness = exhaustive_agree(f, wrong, widths)
        self.assertFalse(truth)
        self.assertFalse(r.proved)
        kw = r.counterexample
        self.assertNotEqual(f(**kw), wrong(**kw),
                            "the returned input must genuinely distinguish them")


class TestCounterexamples(unittest.TestCase):
    def test_wrong_refactor_is_caught(self):
        def max_ok(a, b):
            if a > b:
                return a
            return b

        def max_bad(a, b):
            if a >= b:
                return b
            return a

        r = equivalent(max_ok, max_bad, widths={"a": 5, "b": 5})
        self.assertFalse(r.proved)
        self.assertIsNotNone(r.counterexample)
        # the counterexample must be genuine
        kw = r.counterexample
        self.assertNotEqual(max_ok(**kw), max_bad(**kw))

    def test_counterexamples_are_never_spurious(self):
        """Every returned input must actually distinguish the two circuits;
        `equivalent` asserts this internally, so this drives it over cases."""
        def f(x):
            return x + 1

        def g(x):
            return x + 2

        r = equivalent(f, g, widths={"x": 6})
        self.assertFalse(r.proved)
        self.assertIsNotNone(r.outputs)
        self.assertNotEqual(r.outputs[0], r.outputs[1])

    def test_overflow_difference_is_labelled_as_such(self):
        """(x*4)//4 is x in Python and is not at 6 bits, because x*4 wraps.
        Both are true and the result must say which one it found."""
        def orig(x):
            return (x * 4) // 4

        def simplified(x):
            return x

        r = equivalent(orig, simplified, widths={"x": 6})
        self.assertFalse(r.proved)
        self.assertTrue(r.overflow_only,
                        "a difference Python does not share must be flagged")
        self.assertIn("overflow", r.report())


class TestOperatorSemantics(unittest.TestCase):
    """Every modelled operator, checked against Python at a width small enough
    to enumerate.

    This is the layer where a silent mistake would be worst: a wrong shift or
    comparison would not crash, it would just quietly prove the wrong things.
    Each case avoids intermediate overflow so Python is a valid reference (see
    `exhaustive_agree`).
    """

    W = 5

    def _same_as_python(self, fn, reference, label):
        """The circuit for `fn` must match what Python computes for `fn`.

        This used to call `equivalent(fn, reference)`, which compiles *both*
        arguments -- so Python never ran and the assertion said only that pyeq
        agreed with itself. A logical instead of arithmetic `>>` would have
        compiled `shr` and `div2` to the same wrong circuit and passed.

        `exhaustive_agree` is the oracle the class docstring already pointed
        at: it enumerates every input at this width and runs the plain Python
        function. `equivalent` still gets asserted alongside it, so a
        disagreement between the two is visible rather than one replacing the
        other.
        """
        widths = {"x": self.W}
        ok, cex = exhaustive_agree(fn, reference, widths)
        self.assertTrue(ok, f"{label}: the compiled function and plain Python "
                            f"disagree at {cex}")
        r = equivalent(fn, reference, widths=widths)
        self.assertTrue(r.proved, f"{label}: {r.report()}")

    def test_bitwise_operators(self):
        def f_and(x): return x & 12
        def g_and(x): return x & 12
        def f_or(x): return x | 5
        def g_or(x): return x | 5
        def f_xor(x): return x ^ 9
        def g_xor(x): return x ^ 9
        def f_inv(x): return ~x
        def g_inv(x): return -x - 1          # the identity ~x == -x-1
        for f, g, label in ((f_and, g_and, "&"), (f_or, g_or, "|"),
                            (f_xor, g_xor, "^"), (f_inv, g_inv, "~ == -x-1")):
            with self.subTest(op=label):
                self._same_as_python(f, g, label)

    def test_shift_identities(self):
        def shl(x): return x << 2
        def mul4(x): return x * 4
        self._same_as_python(shl, mul4, "<<2 == *4")

        def shr(x): return x >> 1
        def div2(x): return x // 2
        self._same_as_python(shr, div2, ">>1 == //2 (arithmetic)")

    def test_modulo_by_power_of_two(self):
        def mod8(x): return x % 8
        def mask7(x): return x & 7
        self._same_as_python(mod8, mask7, "%8 == &7")

    def test_all_six_comparisons(self):
        def lt(x): return 1 if x < 3 else 0
        def ge_not(x): return 0 if x >= 3 else 1
        self._same_as_python(lt, ge_not, "< is the negation of >=")

        def gt(x): return 1 if x > 3 else 0
        def le_not(x): return 0 if x <= 3 else 1
        self._same_as_python(gt, le_not, "> is the negation of <=")

        def eq(x): return 1 if x == 3 else 0
        def ne_not(x): return 0 if x != 3 else 1
        self._same_as_python(eq, ne_not, "== is the negation of !=")

    def test_boolean_operators(self):
        def both(x): return 1 if (x > 0 and x < 4) else 0
        def demorgan(x): return 0 if (x <= 0 or x >= 4) else 1
        self._same_as_python(both, demorgan, "de Morgan")

    def test_boolean_operators_as_values(self):
        """`and` and `or` return an operand. They were compiled to 0/1, which is
        right for a comparison and wrong for anything else: `x or 5` at x = 2 is
        2, and it was proved equal to `1`."""
        def and_same(x): return x and x
        def or_same(x): return x or x
        def ident(x): return x
        self._same_as_python(and_same, ident, "x and x is x")
        self._same_as_python(or_same, ident, "x or x is x")

        def or_five(x): return x or 5
        def or_five_spelt(x): return x if x else 5
        self._same_as_python(or_five, or_five_spelt, "a or b")

        def and_five(x): return x and 5
        def and_five_spelt(x): return 5 if x else x
        self._same_as_python(and_five, and_five_spelt, "a and b")

        def chained(x): return x and 3 and x - 1 or 7
        def chained_spelt(x):
            if x == 0:
                return 7
            if x - 1 == 0:
                return 7
            return x - 1
        self._same_as_python(chained, chained_spelt, "a and b and c or d")

        def comparisons(x): return (x > 0) and (x < 3)
        def as_ints_flat(x): return 1 if x > 0 and x < 3 else 0
        self._same_as_python(comparisons, as_ints_flat, "comparisons as operands")

    def test_the_operand_is_not_a_truth_value(self):
        def x_and_x(x): return x and x
        def x_or_x(x): return x or x
        def x_or_5(x): return x or 5
        def x_and_5(x): return x and 5
        def is_set(x): return 1 if x else 0
        def one(x): return 1
        engines = ["python"] + (["native"] if native.available() else [])
        for engine in engines:
            for f, g in ((x_and_x, is_set), (x_or_x, is_set), (x_or_5, one),
                         (x_and_5, is_set)):
                with self.subTest(f=f.__name__, g=g.__name__, engine=engine):
                    r = equivalent(f, g, {"x": 3}, engine=engine)
                    self.assertIs(r.proved, False, "they differ at x = 2")
                    self.assertFalse(r.overflow_only, r.report())
                    cex = r.counterexample
                    self.assertNotEqual(f(**cex), g(**cex))

    def test_unary_and_ifexp(self):
        def neg_then_neg(x): return -(-x)
        def ident(x): return +x
        self._same_as_python(neg_then_neg, ident, "unary minus/plus")

        def via_ifexp(x): return 1 if x else 0
        def via_ne(x): return 1 if x != 0 else 0
        self._same_as_python(via_ifexp, via_ne, "truthiness == != 0")

    def test_augmented_assignment(self):
        def aug(x):
            t = x
            t += x
            t *= 2
            return t

        def direct(x):
            return x * 4

        self._same_as_python(aug, direct, "augmented assignment")

    def test_nested_branches(self):
        def nested(x):
            if x < 0:
                if x < -2:
                    return 1
                return 2
            return 3

        def flat(x):
            if x < -2:
                return 1
            if x < 0:
                return 2
            return 3

        self._same_as_python(nested, flat, "nested vs flat branches")

    def test_not_operator(self):
        def with_not(x): return 1 if not (x > 0) else 0
        def without(x): return 1 if x <= 0 else 0
        self._same_as_python(with_not, without, "not")

    def test_docstring_and_pass_are_ignored(self):
        def documented(x):
            """This docstring must not affect the circuit."""
            pass
            return x

        def bare(x):
            return x

        self._same_as_python(documented, bare, "docstring/pass")

    def test_no_return_yields_zero(self):
        def implicit(x):
            if x > 0:
                return 0
            return 0

        def zero(x):
            return 0

        self._same_as_python(implicit, zero, "constant zero")


class TestRejection(unittest.TestCase):
    def _reject(self, fn, needle):
        with self.assertRaises(UnsupportedConstruct) as cm:
            equivalent(fn, fn, widths={"a": 4})
        self.assertIn(needle, str(cm.exception).lower())

    def test_while_loop(self):
        def uses_while(a):
            while a > 0:
                a = a - 1
            return a

        self._reject(uses_while, "while")

    def test_unbounded_range(self):
        def dynamic_loop(a):
            t = 0
            for _i in range(a):
                t = t + 1
            return t

        self._reject(dynamic_loop, "non-constant")

    def test_division_by_non_power_of_two(self):
        def div3(a):
            return a // 3

        self._reject(div3, "power")

    def test_function_call(self):
        def helper(x):
            return x

        def calls(a):
            return helper(a)

        self._reject(calls, "call")

    def test_string_constant(self):
        def uses_str(a):
            s = "no"
            return a

        self._reject(uses_str, "constant of type str")

    def test_a_bare_expression_is_not_ignored(self):
        """Every one of these was dropped by a line that said bare expressions
        have no effect, and proved equal to a function it differs from."""
        def identity(a): return a

        def walrus(a):
            (a := a + 1)
            return a

        def yields(a):
            yield a
            return a

        def raises(a):
            a % 0
            return a

        def call_one_level_down(a):
            [print(a) for i in range(1)]
            return a

        def name(a):
            b
            return a

        for fn in (walrus, yields, raises, call_one_level_down, name):
            with self.subTest(fn=fn.__name__):
                with self.assertRaises(UnsupportedConstruct):
                    equivalent(fn, identity, widths={"a": 3})

    def test_a_construct_in_code_that_never_runs_still_counts(self):
        """`yield` makes the whole function a generator wherever it sits, and a
        body the compiler skips is not a body Python ignores."""
        def identity(a): return a

        def after_return(a):
            return a
            yield a

        def in_an_empty_loop(a):
            for _i in range(0):
                yield a
            return a

        def in_a_dead_branch(a):
            if False:
                yield a
            return a

        for fn in (after_return, in_an_empty_loop, in_a_dead_branch):
            with self.subTest(fn=fn.__name__):
                with self.assertRaises(UnsupportedConstruct):
                    equivalent(fn, identity, widths={"a": 3})

    def test_the_subset_is_an_allowlist(self):
        """A node nobody thought of has to raise. Listing the bad ones is how
        the walrus got through."""
        def identity(a): return a

        cases = {
            "global": "def f(a):\n    global q\n    return a\n",
            "lambda": "def f(a):\n    g = lambda: 1\n    return a\n",
            "del": "def f(a):\n    b = 1\n    del b\n    return a\n",
            "assert": "def f(a):\n    assert a\n    return a\n",
            "with": "def f(a):\n    with a:\n        pass\n    return a\n",
            "try": "def f(a):\n    try:\n        pass\n    except E:\n        pass\n"
                   "    return a\n",
            "raise": "def f(a):\n    raise E\n    return a\n",
            "import": "def f(a):\n    import os\n    return a\n",
            "nested def": "def f(a):\n    def g():\n        return 1\n    return a\n",
            "class": "def f(a):\n    class C:\n        pass\n    return a\n",
            "list": "def f(a):\n    b = [a]\n    return a\n",
            "subscript": "def f(a):\n    return a[0]\n",
            "attribute": "def f(a):\n    return a.real\n",
            "fstring": "def f(a):\n    b = f'{a}'\n    return a\n",
            "yield expression": "def f(a):\n    b = (yield)\n    return a\n",
            "power": "def f(a):\n    return a ** 2\n",
            "true division": "def f(a):\n    return a / 2\n",
            "is": "def f(a):\n    return a is a\n",
            "in": "def f(a):\n    return a in a\n",
        }
        import tempfile, importlib.util, pathlib
        with tempfile.TemporaryDirectory() as d:
            for label, src in cases.items():
                with self.subTest(label=label):
                    path = pathlib.Path(d) / f"m_{abs(hash(label))}.py"
                    path.write_text(src)
                    spec = importlib.util.spec_from_file_location(path.stem, path)
                    mod = importlib.util.module_from_spec(spec)
                    spec.loader.exec_module(mod)
                    with self.assertRaises(UnsupportedConstruct) as cm:
                        equivalent(mod.f, identity, widths={"a": 3})
                    self.assertIn("line", str(cm.exception))

    def test_annotations_and_constants_stay_in_the_subset(self):
        def annotated(a: int) -> int:
            """A docstring."""
            ...
            7
            return a

        def identity(a): return a

        self.assertIs(equivalent(annotated, identity, widths={"a": 3}).proved, True)

    def test_a_decorated_function_is_not_its_undecorated_body(self):
        """`inspect.getsource` follows `__wrapped__`, so what compiled was not
        the callable `equivalent` was handed."""
        import functools

        def double(fn):
            @functools.wraps(fn)
            def wrapper(a):
                return fn(a) * 2
            return wrapper

        def nothing(fn):
            return fn

        @double
        def wraps_it(a): return a

        @nothing
        def decorated_only(a): return a

        def plain(a): return a

        def wrapped_by_hand(a): return a
        wrapped_by_hand.__wrapped__ = plain

        for fn in (wraps_it, decorated_only, wrapped_by_hand):
            for args in ((fn, plain), (plain, fn)):
                with self.subTest(fn=fn.__name__, first=args[0].__name__):
                    with self.assertRaises(UnsupportedConstruct):
                        equivalent(*args, widths={"a": 3})

    def test_missing_width_is_reported(self):
        def two(a, b):
            return a + b

        with self.assertRaises(UnsupportedConstruct) as cm:
            equivalent(two, two, widths={"a": 4})
        self.assertIn("b", str(cm.exception))


def _slow(a, b):
    return a * 2 + b * 2


def _fast(a, b):
    return (a + b) << 1


def _mul_ab(a, b):
    return a * b


def _mul_ba(a, b):
    return b * a


class TestProvedMeansChecked(unittest.TestCase):
    """`proved` is a claim about a proof, so the proof has to exist and pass.

    Without these, `equivalent()` would be the one part of the toolkit that
    asks to be trusted -- in a project whose premise is that nothing should
    have to be.
    """

    def test_a_proved_equivalence_carries_a_verified_proof(self):
        r = equivalent(_slow, _fast, widths={"a": 8, "b": 8})
        self.assertIs(r.proved, True)
        self.assertTrue(r.proof_checked, "proved=True without a checked proof")
        self.assertGreater(r.proof_steps, 0, "a proof of zero steps proves nothing")
        self.assertIn("verified", r.report())

    @unittest.skipUnless(native.available(),
                         "needs the native engine; without it this compared "
                         "Python against Python and passed")
    def test_both_engines_prove_it_and_both_proofs_verify(self):
        """Both engines must produce a *checkable* proof. Not the same one.

        The engines run the same search -- identical conflict counts -- but
        they do not emit identical proofs, and it is worth knowing why before
        someone reads the bit-exactness claim too broadly.

        When an input clause has root-false literals, `add_clause` internally
        adds a strengthened version. `cdclkit/solver.py` logs that strengthened
        clause as a DRAT addition; the Rust engine does not. Both are correct:
        the step is RUP-derivable from the root units, so the checker reaches
        the same conclusion whether or not it is spelled out. Python emits
        677 additions here against Rust's 208, from the same 133 conflicts.

        So the contract is "every proof verifies", not "every proof matches".
        Asserting the stronger thing was a test that failed for a reason that
        turned out to be neither engine's fault.
        """
        a = equivalent(_slow, _fast, widths={"a": 8, "b": 8}, engine="python")
        b = equivalent(_slow, _fast, widths={"a": 8, "b": 8}, engine="native")
        self.assertIs(a.proved, True)
        self.assertIs(b.proved, True)
        self.assertTrue(a.proof_checked and b.proof_checked)
        self.assertGreater(min(a.proof_steps, b.proof_steps), 0)

    def test_verify_off_is_reported_rather_than_hidden(self):
        r = equivalent(_slow, _fast, widths={"a": 8, "b": 8}, verify=False)
        self.assertIs(r.proved, True)
        self.assertFalse(r.proof_checked)
        self.assertIn("UNVERIFIED", r.report(),
                      "an unverified answer must say so, or the flag is a trap")

    def test_exhausted_budget_is_undecided_and_never_proved(self):
        """The regression test this whole change exists for.

        `proved` used to be set from `if not res.sat`, and the pipeline returns
        `None` for an exhausted budget. `None` is falsy, so the moment a budget
        existed, "I gave up" would have been recorded as "I proved it".
        """
        r = equivalent(_mul_ab, _mul_ba, widths={"a": 12, "b": 12},
                       max_conflicts=1)
        self.assertIsNone(r.proved, "an exhausted budget must decide nothing")
        self.assertIsNot(r.proved, True)
        self.assertFalse(bool(r), "undecided must not read as proved")
        self.assertFalse(r.proof_checked)
        self.assertIsNone(r.counterexample)
        self.assertIn("UNDECIDED", r.report())

    def test_a_generous_budget_still_decides(self):
        """The budget must bound the search, not break it."""
        r = equivalent(_slow, _fast, widths={"a": 8, "b": 8},
                       max_conflicts=1_000_000)
        self.assertIs(r.proved, True)
        self.assertTrue(r.proof_checked)

    def test_a_counterexample_needs_no_proof(self):
        """UNSAT needs a certificate; SAT is its own."""
        def clamp_a(x, lo, hi):
            if x < lo:
                return lo
            if x > hi:
                return hi
            return x

        def clamp_b(x, lo, hi):
            if x > hi:
                return hi
            if x < lo:
                return lo
            return x

        r = equivalent(clamp_a, clamp_b, widths={"x": 6, "lo": 6, "hi": 6})
        self.assertIs(r.proved, False)
        self.assertFalse(r.proof_checked)
        self.assertIsNotNone(r.counterexample)

    def test_a_rejected_proof_raises_instead_of_claiming_equivalence(self):
        """If the checker ever disagrees with the solver, say nothing.

        There is no honest verdict available in that situation: the two things
        built to cross-check each other have contradicted, so both are suspect.
        Returning `proved=False` would blame the user's code for a bug in ours,
        and `proved=True` would be the exact failure the check exists to catch.
        Simulated by handing back a truncated proof, since the real solver has
        never produced one the checker rejects.
        """
        import cdclkit.pyeq as pyeq
        from cdclkit.pyeq import ProofRejected

        real = pyeq._solve_miter

        def truncated(formula, engine, budget, want_proof):
            status, model, steps, conflicts = real(formula, engine, budget, want_proof)
            # drop the tail: the empty clause is never derived, so the proof
            # no longer establishes anything
            return status, model, (steps[:2] if steps else steps), conflicts

        pyeq._solve_miter = truncated
        try:
            with self.assertRaises(ProofRejected) as cm:
                equivalent(_slow, _fast, widths={"a": 6, "b": 6})
        finally:
            pyeq._solve_miter = real
        self.assertIn("bug in cdclkit", str(cm.exception))

    def test_the_emitted_proof_is_a_proof_of_the_miter_itself(self):
        """Not of some rewritten formula.

        This is why the verified path refuses to preprocess: bounded variable
        elimination adds clauses that do not follow from the input, so its
        refutation would not check against the miter. Rebuilding the same
        miter and checking the proof against it is the assertion that the
        formula the proof talks about is the formula the caller asked about.
        """
        from dratify.cnf import CNF
        from cdclkit.encodings import Encoder
        from dratify.proof import check_proof
        from cdclkit.pyeq import compile_function

        f = CNF()
        enc = Encoder(f)
        out_a, inputs = compile_function(_slow, enc, {"a": 8, "b": 8})
        out_b, _ = compile_function(_fast, enc, {"a": 8, "b": 8}, inputs=inputs)
        w = max(out_a.width, out_b.width)
        x, y = out_a.extend(w), out_b.extend(w)
        enc.add([enc.xor_gate(p, q) for p, q in zip(x.bits, y.bits)])

        from cdclkit.pyeq import _solve_miter

        status, _, steps, _ = _solve_miter(f, "python", None, want_proof=True)
        self.assertIs(status, False)
        self.assertTrue(check_proof(f, steps).ok)



# --------------------------------------------------------------------------
# implicit None
# --------------------------------------------------------------------------


def _guard_falls_off(x):
    if x > 0:
        return 1
    # falls off the end -> Python returns None


def _guard_explicit(x):
    if x > 0:
        return 1
    return 1


def _bare_return(a):
    if a > 0:
        return 1
    return


def _returns_zero(a):
    if a > 0:
        return 1
    return 0


def _no_return_at_all(a):
    x = a + 1


def _constant_zero(a):
    return 0


def _default_three(a, b=3):
    return a + b


def _default_ninetynine(a, b=99):
    return b + a


class TestImplicitNoneIsNotAnInteger(unittest.TestCase):
    """Every path here once produced a *false proof*, with `proof_checked`.

    A function that can finish without an explicit `return` yields None, and
    None is not a bit-vector. Modelling it as an integer -- as 0, or as the
    last guarded value -- makes `equivalent` report agreement between
    functions that visibly disagree in Python.

    These are regression tests, not hypotheticals: each pair below returned
    ``proved=True, proof_checked=True`` before the guard existed. They are
    also the reason the DRAT certificate cannot be the whole story for
    `pyeq` -- the proof was valid; it certified a circuit that did not mean
    what the source said. The front end is upstream of everything the proof
    covers.
    """

    def test_falling_off_the_end_is_refused(self):
        with self.assertRaises(UnsupportedConstruct) as cm:
            equivalent(_guard_explicit, _guard_falls_off, widths={"x": 8})
        self.assertIn("without returning", str(cm.exception))

    def test_bare_return_is_refused(self):
        # `return` and `return 0` are different functions; `return None` was
        # already rejected, so accepting a bare `return` as 0 was inconsistent
        # as well as unsound.
        with self.assertRaises(UnsupportedConstruct) as cm:
            equivalent(_returns_zero, _bare_return, widths={"a": 8})
        self.assertIn("bare", str(cm.exception))

    def test_body_with_no_return_is_refused(self):
        # This one skipped the guard by short-circuiting on an empty return
        # set before the check ran.
        with self.assertRaises(UnsupportedConstruct):
            equivalent(_constant_zero, _no_return_at_all, widths={"a": 8})

    def test_default_arguments_are_refused(self):
        # Defaults were dropped and every parameter treated as a free input,
        # so these two "proved equivalent" despite f(1) == 4 and g(1) == 100.
        with self.assertRaises(UnsupportedConstruct) as cm:
            equivalent(_default_three, _default_ninetynine,
                       widths={"a": 8, "b": 8})
        self.assertIn("default", str(cm.exception))

    def test_total_functions_still_prove(self):
        # The guard must not cost anything for functions that always return.
        r = equivalent(_returns_zero, _returns_zero, widths={"a": 8})
        self.assertIs(r.proved, True)
        self.assertTrue(r.proof_checked)

    def test_guard_accepts_returns_in_both_arms(self):
        def a(x):
            if x > 0:
                return 1
            else:
                return 2

        def b(x):
            if x > 0:
                return 1
            return 2

        self.assertIs(equivalent(a, b, widths={"x": 8}).proved, True)



if __name__ == "__main__":
    unittest.main()
