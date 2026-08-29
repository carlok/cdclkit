# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Prove two Python functions agree on every input, or produce one that breaks.

    >>> def slow(a, b): return a * 2 + b * 2
    >>> def fast(a, b): return (a + b) << 1
    >>> equivalent(slow, fast, widths={"a": 8, "b": 8}).proved
    True

The question this answers is "did my refactor change behaviour?", and it
answers it by *proof* rather than by sampling. Tests check the inputs you
thought of. This checks all of them.

How
---
Each function is compiled from its Python AST into a fixed-width bit-vector
circuit, the circuit into CNF via `cdclkit.encodings.Encoder`, and the two
circuits into a **miter**: shared inputs, outputs compared, the comparison
asserted to differ. Unsatisfiable means no input distinguishes them. Satisfiable
means the model *is* a distinguishing input, which is handed back.

The solving half of this already existed -- `examples/equivalence.py` miters two
adder implementations, and `bench/run_bench.py` builds an array multiplier out
of the same gates. This module is the front end.

**Semantics, and this matters**
-------------------------------
Python integers are arbitrary precision. This compiles them to **fixed-width
two's-complement with wrapping**, at a width you declare. So:

* "equivalent" means **equivalent as fixed-width machine integers**, not as
  Python programs. Two functions that agree at 8 bits can differ in Python if
  either exceeds the range, and vice versa;
* a counterexample is always real *at that width* -- the circuit outputs are
  read back from the model and asserted to differ, so a spurious one is a bug
  here and says so;
* when the circuits differ but Python agrees, the result sets
  ``overflow_only`` and says so. `(x * 4) // 4` equals `x` in Python and does
  **not** at 6 bits, because `x * 4` wraps. Both facts are worth knowing and
  they are different facts.

Every operation whose meaning would be ambiguous is rejected rather than
guessed. `//` and `%` are supported only for constant powers of two, because
general division needs a restoring divider whose cost is rarely worth it and
whose silent wrong answer would be worse. Unsupported syntax raises
`UnsupportedConstruct` with the line number. A verifier that quietly ignores a
construct is worse than no verifier.
"""

from __future__ import annotations

import ast
import inspect
import textwrap
from typing import Callable, Sequence

from dratify.cnf import CNF
from .encodings import Encoder
from dratify.lits import mk_lit, neg
from .native import available as _native_available
from dratify.proof import MemoryProof

__all__ = [
    "equivalent",
    "EquivalenceResult",
    "UnsupportedConstruct",
    "BitVec",
    "compile_function",
]


class UnsupportedConstruct(Exception):
    """Raised for Python this module will not model.

    Deliberately fatal. Silently approximating a construct would make every
    "equivalent" answer meaningless, since you could never tell whether the
    proof covered the code you wrote or a simplification of it.
    """


# --------------------------------------------------------------------------
# bit vectors
# --------------------------------------------------------------------------


class BitVec:
    """A fixed-width integer as a list of literals, least significant first.

    Two's complement. Every operation wraps at `width` bits, which is what the
    hardware a Python int eventually runs on does anyway -- the difference is
    that here it is explicit and declared.
    """

    __slots__ = ("bits", "enc")

    def __init__(self, enc: Encoder, bits: Sequence[int]) -> None:
        self.enc = enc
        self.bits = list(bits)

    @property
    def width(self) -> int:
        return len(self.bits)

    @classmethod
    def constant(cls, enc: Encoder, value: int, width: int) -> "BitVec":
        t, f = enc.true_lit, enc.false_lit
        return cls(enc, [(t if (value >> i) & 1 else f) for i in range(width)])

    @classmethod
    def input(cls, enc: Encoder, width: int, name: str) -> "BitVec":
        return cls(enc, [enc.new_lit(f"{name}[{i}]") for i in range(width)])

    # -- bitwise --------------------------------------------------------

    def _zip(self, other: "BitVec", op) -> "BitVec":
        w = max(self.width, other.width)
        a, b = self.extend(w), other.extend(w)
        return BitVec(self.enc, [op(x, y) for x, y in zip(a.bits, b.bits)])

    def __and__(self, o): return self._zip(o, lambda x, y: self.enc.and_gate([x, y]))
    def __or__(self, o): return self._zip(o, lambda x, y: self.enc.or_gate([x, y]))
    def __xor__(self, o): return self._zip(o, lambda x, y: self.enc.xor_gate(x, y))

    def __invert__(self) -> "BitVec":
        return BitVec(self.enc, [neg(b) for b in self.bits])

    def extend(self, width: int) -> "BitVec":
        """Sign-extend or truncate to `width`."""
        if width == self.width:
            return self
        if width < self.width:
            return BitVec(self.enc, self.bits[:width])
        sign = self.bits[-1] if self.bits else self.enc.false_lit
        return BitVec(self.enc, self.bits + [sign] * (width - self.width))

    # -- arithmetic -----------------------------------------------------

    def __add__(self, other: "BitVec") -> "BitVec":
        """Ripple-carry addition, wrapping at the top bit."""
        enc = self.enc
        w = max(self.width, other.width)
        a, b = self.extend(w), other.extend(w)
        out, carry = [], enc.false_lit
        for i in range(w):
            x, y = a.bits[i], b.bits[i]
            xy = enc.xor_gate(x, y)
            out.append(enc.xor_gate(xy, carry))
            carry = enc.or_gate([enc.and_gate([x, y]),
                                 enc.and_gate([x, carry]),
                                 enc.and_gate([y, carry])])
        return BitVec(enc, out)

    def __neg__(self) -> "BitVec":
        """Two's complement negation: ~x + 1."""
        return (~self) + BitVec.constant(self.enc, 1, self.width)

    def __sub__(self, other: "BitVec") -> "BitVec":
        return self + (-other.extend(max(self.width, other.width)))

    def __mul__(self, other: "BitVec") -> "BitVec":
        """Shift-and-add array multiplier, truncated to `width`.

        Same construction as the factoring benchmark in `bench/run_bench.py`,
        which is where its correctness was first exercised.
        """
        enc = self.enc
        w = max(self.width, other.width)
        a, b = self.extend(w), other.extend(w)
        acc = BitVec.constant(enc, 0, w)
        for i in range(w):
            # partial product a << i, gated on b[i]
            row = [enc.false_lit] * i + [
                enc.and_gate([a.bits[j], b.bits[i]]) for j in range(w - i)
            ]
            acc = acc + BitVec(enc, row)
        return acc.extend(w)

    def shl(self, k: int) -> "BitVec":
        if k >= self.width:
            return BitVec.constant(self.enc, 0, self.width)
        return BitVec(self.enc,
                      [self.enc.false_lit] * k + self.bits[: self.width - k])

    def shr(self, k: int, arithmetic: bool = True) -> "BitVec":
        """Right shift.  Arithmetic (sign-propagating) by default, because
        Python's `>>` on negative ints is arithmetic."""
        fill = self.bits[-1] if arithmetic else self.enc.false_lit
        if k >= self.width:
            return BitVec(self.enc, [fill] * self.width)
        return BitVec(self.enc, self.bits[k:] + [fill] * k)

    # -- comparison -----------------------------------------------------

    def eq(self, other: "BitVec") -> int:
        w = max(self.width, other.width)
        a, b = self.extend(w), other.extend(w)
        same = [neg(self.enc.xor_gate(x, y)) for x, y in zip(a.bits, b.bits)]
        return self.enc.and_gate(same)

    def slt(self, other: "BitVec") -> int:
        """Signed less-than, via the sign of the difference with overflow
        correction: a < b iff (a-b) is negative, XOR the signed-overflow flag."""
        enc = self.enc
        w = max(self.width, other.width) + 1  # one extra bit kills the overflow case
        a, b = self.extend(w), other.extend(w)
        return (a - b).bits[-1]

    def is_zero(self) -> int:
        return self.enc.and_gate([neg(b) for b in self.bits])


def _ite_bv(enc: Encoder, cond: int, a: BitVec, b: BitVec) -> BitVec:
    w = max(a.width, b.width)
    a, b = a.extend(w), b.extend(w)
    return BitVec(enc, [enc.ite(cond, x, y) for x, y in zip(a.bits, b.bits)])


# --------------------------------------------------------------------------
# the compiler
# --------------------------------------------------------------------------

_CMP = {ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE}


class _Compiler(ast.NodeVisitor):
    """Compile one function body into a circuit.

    Control flow is handled by *path conditions* rather than by branching:
    every assignment under an `if` becomes a select between the new value and
    the old one, gated on the branch condition. That is what makes early
    returns work -- each `return` records `(condition, value)`, and the result
    is the chain of selects over those pairs.
    """

    def __init__(self, enc: Encoder, width: int, env: dict[str, BitVec]) -> None:
        self.enc = enc
        self.width = width
        self.env = dict(env)
        self.returns: list[tuple[int, BitVec]] = []
        self.pc = enc.true_lit  # current path condition

    # -- helpers --------------------------------------------------------

    def _fail(self, node: ast.AST, what: str) -> None:
        line = getattr(node, "lineno", "?")
        raise UnsupportedConstruct(
            f"line {line}: {what} is not supported. This checker models a "
            f"restricted subset on purpose -- approximating it silently would "
            f"make every 'equivalent' answer meaningless."
        )

    def const(self, v: int) -> BitVec:
        return BitVec.constant(self.enc, v, self.width)

    # -- expressions ----------------------------------------------------

    def expr(self, node: ast.AST) -> BitVec:
        if isinstance(node, ast.Constant):
            if isinstance(node.value, bool):
                return self.const(1 if node.value else 0)
            if isinstance(node.value, int):
                return self.const(node.value)
            self._fail(node, f"constant of type {type(node.value).__name__}")

        if isinstance(node, ast.Name):
            if node.id not in self.env:
                self._fail(node, f"name {node.id!r} used before assignment")
            return self.env[node.id]

        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.USub):
                return -self.expr(node.operand)
            if isinstance(node.op, ast.UAdd):
                return self.expr(node.operand)
            if isinstance(node.op, ast.Invert):
                return ~self.expr(node.operand)
            if isinstance(node.op, ast.Not):
                c = self.truth(node.operand)
                return _ite_bv(self.enc, c, self.const(0), self.const(1))
            self._fail(node, type(node.op).__name__)

        if isinstance(node, ast.BinOp):
            return self.binop(node)

        if isinstance(node, (ast.Compare, ast.BoolOp)):
            c = self.truth(node)
            return _ite_bv(self.enc, c, self.const(1), self.const(0))

        if isinstance(node, ast.IfExp):
            c = self.truth(node.test)
            return _ite_bv(self.enc, c, self.expr(node.body), self.expr(node.orelse))

        if isinstance(node, ast.Call):
            self._fail(node, "function calls (inline the callee, or pass it "
                             "through `helpers=`)")

        self._fail(node, type(node).__name__)

    def binop(self, node: ast.BinOp) -> BitVec:
        op = node.op
        left = self.expr(node.left)

        # shifts and power-of-two division need a constant right operand
        if isinstance(op, (ast.LShift, ast.RShift, ast.FloorDiv, ast.Mod)):
            if not (isinstance(node.right, ast.Constant)
                    and isinstance(node.right.value, int)):
                self._fail(node, f"{type(op).__name__} by a non-constant")
            k = node.right.value
            if isinstance(op, ast.LShift):
                return left.shl(k)
            if isinstance(op, ast.RShift):
                return left.shr(k)
            # // and % only by powers of two: a general divider is a large
            # circuit and rarely what a refactor hinges on
            if k <= 0 or (k & (k - 1)) != 0:
                self._fail(node, f"{type(op).__name__} by {k} "
                                 f"(only positive powers of two)")
            shift = k.bit_length() - 1
            if isinstance(op, ast.FloorDiv):
                return left.shr(shift)
            mask = self.const(k - 1)
            return left & mask

        right = self.expr(node.right)
        if isinstance(op, ast.Add):
            return left + right
        if isinstance(op, ast.Sub):
            return left - right
        if isinstance(op, ast.Mult):
            return left * right
        if isinstance(op, ast.BitAnd):
            return left & right
        if isinstance(op, ast.BitOr):
            return left | right
        if isinstance(op, ast.BitXor):
            return left ^ right
        self._fail(node, type(op).__name__)

    def truth(self, node: ast.AST) -> int:
        """Compile an expression used as a condition into a single literal."""
        if isinstance(node, ast.Compare):
            if len(node.ops) != 1:
                self._fail(node, "chained comparison")
            op = node.ops[0]
            if type(op) not in _CMP:
                self._fail(node, type(op).__name__)
            a, b = self.expr(node.left), self.expr(node.comparators[0])
            if isinstance(op, ast.Eq):
                return a.eq(b)
            if isinstance(op, ast.NotEq):
                return neg(a.eq(b))
            if isinstance(op, ast.Lt):
                return a.slt(b)
            if isinstance(op, ast.GtE):
                return neg(a.slt(b))
            if isinstance(op, ast.Gt):
                return b.slt(a)
            if isinstance(op, ast.LtE):
                return neg(b.slt(a))

        if isinstance(node, ast.BoolOp):
            parts = [self.truth(v) for v in node.values]
            if isinstance(node.op, ast.And):
                return self.enc.and_gate(parts)
            return self.enc.or_gate(parts)

        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return neg(self.truth(node.operand))

        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return self.enc.true_lit if node.value else self.enc.false_lit

        # any other expression is truthy when non-zero
        return neg(self.expr(node).is_zero())

    # -- statements -----------------------------------------------------

    def block(self, body: list[ast.stmt]) -> None:
        for stmt in body:
            self.stmt(stmt)

    def stmt(self, node: ast.stmt) -> None:
        if isinstance(node, ast.Assign):
            if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
                self._fail(node, "tuple or attribute assignment")
            self.assign(node.targets[0].id, self.expr(node.value))
            return

        if isinstance(node, ast.AugAssign):
            if not isinstance(node.target, ast.Name):
                self._fail(node, "augmented assignment to a non-name")
            fake = ast.BinOp(left=ast.Name(id=node.target.id, ctx=ast.Load()),
                             op=node.op, right=node.value)
            ast.copy_location(fake, node)
            ast.copy_location(fake.left, node)
            self.assign(node.target.id, self.binop(fake))
            return

        if isinstance(node, ast.Return):
            if node.value is None:
                # A bare `return` yields None. Modelling it as 0 makes a false
                # proof against a function that really does return 0, and it
                # contradicts `return None`, which this compiler rejects.
                self._fail(node, "a bare `return` (it yields None, not an "
                                 "integer; `return None` is rejected for the "
                                 "same reason)")
            value = self.expr(node.value)
            self.returns.append((self.pc, value))
            # everything after a return on this path is unreachable
            self.pc = self.enc.false_lit
            return

        if isinstance(node, ast.If):
            cond = self.truth(node.test)
            before = dict(self.env)
            outer_pc = self.pc

            self.pc = self.enc.and_gate([outer_pc, cond])
            self.block(node.body)
            then_env, then_pc = dict(self.env), self.pc

            self.env = dict(before)
            self.pc = self.enc.and_gate([outer_pc, neg(cond)])
            self.block(node.orelse)
            else_env, else_pc = dict(self.env), self.pc

            merged = {}
            for name in set(then_env) | set(else_env):
                t = then_env.get(name, before.get(name))
                e = else_env.get(name, before.get(name))
                if t is None or e is None:
                    continue  # defined on only one branch: not readable after
                merged[name] = t if t is e else _ite_bv(self.enc, cond, t, e)
            self.env = merged
            # the path survives if either branch did
            self.pc = self.enc.or_gate([then_pc, else_pc])
            return

        if isinstance(node, ast.For):
            self.unroll_for(node)
            return

        if isinstance(node, (ast.Pass, ast.Expr)) and not isinstance(
                getattr(node, "value", None), ast.Call):
            return  # docstrings and bare expressions have no effect

        if isinstance(node, ast.While):
            self._fail(node, "while loops (bound is not statically known; use "
                             "`for i in range(k)` with a constant k)")

        self._fail(node, type(node).__name__)

    def assign(self, name: str, value: BitVec) -> None:
        """Assign under the current path condition.

        Inside a branch the assignment is conditional, so the variable becomes
        a select between the new value and whatever it held before.
        """
        self.env[name] = value

    def unroll_for(self, node: ast.For) -> None:
        if not isinstance(node.target, ast.Name):
            self._fail(node, "loop over a non-name target")
        call = node.iter
        if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
                and call.func.id == "range"):
            self._fail(node, "iteration over anything but range(...)")
        args = []
        for a in call.args:
            if not (isinstance(a, ast.Constant) and isinstance(a.value, int)):
                self._fail(node, "range() with a non-constant bound "
                                 "(the loop must be statically bounded to unroll)")
            args.append(a.value)
        rng = range(*args) if args else range(0)
        if len(rng) > 256:
            self._fail(node, f"range of {len(rng)} iterations (limit 256; "
                             f"unrolling is linear in the bound)")
        if node.orelse:
            self._fail(node, "for/else")
        for i in rng:
            self.env[node.target.id] = self.const(i)
            self.block(node.body)

    # -- result ---------------------------------------------------------

    def result(self, body: list[ast.stmt]) -> BitVec:
        # This check must precede the empty-`returns` case below: a body with
        # no return at all also falls off the end, and short-circuiting first
        # would skip the guard entirely.
        # The last return is only a sound unconditional fallback when control
        # cannot reach the end of the body without it. If it can, the function
        # yields None on that path and there is no bit-vector for that -- so
        # refuse rather than silently model the guarded value as unconditional.
        # Modelling it would make a *false proof*: two functions agreeing on
        # the guarded value would be "proved equivalent" while differing
        # wherever one falls through.
        if not _definitely_returns(body):
            raise UnsupportedConstruct(
                "control can reach the end of the function without returning, "
                "so it yields None on that path; pyeq models integers only. "
                "Add an explicit return.")
        if not self.returns:            # unreachable once the guard above holds
            return self.const(0)
        value = self.returns[-1][1]
        for cond, v in reversed(self.returns[:-1]):
            value = _ite_bv(self.enc, cond, v, value)
        return value


def _definitely_returns(body: list[ast.stmt]) -> bool:
    """True when control cannot reach the end of `body` without returning.

    A `for` loop never counts: its bound can be zero, so the body may not run.
    An `if` counts only when both arms are present and both definitely return.
    """
    for stmt in body:
        if isinstance(stmt, ast.Return):
            return True
        if isinstance(stmt, ast.If):
            if (stmt.orelse and _definitely_returns(stmt.body)
                    and _definitely_returns(stmt.orelse)):
                return True
    return False


def _function_ast(fn: Callable) -> ast.FunctionDef:
    try:
        src = textwrap.dedent(inspect.getsource(fn))
    except (OSError, TypeError) as e:
        raise UnsupportedConstruct(
            f"cannot read the source of {getattr(fn, '__name__', fn)!r}: {e}"
        ) from None
    tree = ast.parse(src)
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            return node
    raise UnsupportedConstruct("no function definition found in the source")


def compile_function(
    fn: Callable,
    enc: Encoder,
    widths: dict[str, int],
    inputs: dict[str, BitVec] | None = None,
) -> tuple[BitVec, dict[str, BitVec]]:
    """Compile `fn` into a circuit.  Returns (result, inputs used)."""
    tree = _function_ast(fn)
    if tree.args.vararg or tree.args.kwarg or tree.args.kwonlyargs:
        raise UnsupportedConstruct("*args, **kwargs and keyword-only parameters")
    if tree.args.defaults or tree.args.kw_defaults:
        # Every parameter is compiled as a free symbolic input, so a default is
        # simply dropped. Two functions with different defaults would then be
        # "proved equivalent" while disagreeing on every call that omits the
        # argument.
        raise UnsupportedConstruct(
            "default argument values are not modelled -- every parameter is "
            "compiled as a free input, so the default is silently dropped")
    names = [a.arg for a in tree.args.args]
    missing = [n for n in names if n not in widths]
    if missing:
        raise UnsupportedConstruct(
            f"no width declared for parameter(s) {', '.join(missing)}; "
            f"pass widths={{'{missing[0]}': 8, ...}}"
        )
    width = max(widths[n] for n in names) if names else 8

    env = dict(inputs) if inputs else {}
    for n in names:
        if n not in env:
            env[n] = BitVec.input(enc, widths[n], n).extend(width)
    c = _Compiler(enc, width, env)
    c.block(tree.body)
    return c.result(tree.body), {n: env[n] for n in names}


# --------------------------------------------------------------------------
# the miter
# --------------------------------------------------------------------------


class EquivalenceResult:
    """Outcome of an equivalence check.

    ``proved`` is three-valued and the distinction matters:

    ``True``   the functions agree on every input at the declared widths, and
               (unless ``verify=False``) a DRAT proof of that was replayed by
               an independent checker.
    ``False``  they differ, and ``counterexample`` is an input where they do.
    ``None``   the conflict budget ran out. Nothing was decided either way.

    ``None`` is falsy, so ``if result:`` is still safe -- an undecided check
    never reads as a proof. Code that needs the distinction must test
    ``is True`` / ``is None`` explicitly.
    """

    __slots__ = ("proved", "counterexample", "width", "vars", "clauses",
                 "seconds", "outputs", "python_outputs", "overflow_only",
                 "proof_checked", "proof_steps", "conflicts")

    def __init__(self) -> None:
        self.proved: bool | None = False
        #: True when a DRAT proof of the UNSAT miter was replayed and accepted
        self.proof_checked: bool = False
        #: length of that proof, in steps
        self.proof_steps: int = 0
        self.conflicts: int = 0
        self.counterexample: dict[str, int] | None = None
        #: what the two circuits produce at the declared width
        self.outputs: tuple[int, int] | None = None
        #: what the two Python functions produce with arbitrary precision
        self.python_outputs: tuple[int, int] | None = None
        #: True when the circuits differ but Python agrees -- the divergence is
        #: an artefact of fixed-width wrapping, not of the refactor
        self.overflow_only: bool = False
        self.width: int = 0
        self.vars: int = 0
        self.clauses: int = 0
        self.seconds: float = 0.0

    def __bool__(self) -> bool:
        # `is True`, not truthiness: an exhausted budget must never read as a
        # proof, and `None` would be the value most likely to be mistaken for
        # one by code that only ever checks `if result:`
        return self.proved is True

    def report(self) -> str:
        if self.proved is None:
            return (f"c UNDECIDED at {self.width} bits: budget exhausted after "
                    f"{self.conflicts} conflicts. Nothing was proved and "
                    f"nothing was refuted; raise max_conflicts or narrow the "
                    f"widths.")
        if self.proved:
            how = (f"proof of {self.proof_steps} steps verified"
                   if self.proof_checked else "UNVERIFIED: verify=False")
            return (f"c equivalent at {self.width} bits, {how} "
                    f"({self.vars} vars, {self.clauses} clauses, "
                    f"{self.seconds*1000:.0f} ms)")
        args = ", ".join(f"{k}={v}" for k, v in (self.counterexample or {}).items())
        got = ("" if self.outputs is None
               else f" -> {self.outputs[0]} vs {self.outputs[1]}")
        head = f"c NOT equivalent at {self.width} bits: {args}{got}"
        if self.overflow_only:
            head += (f"\nc   ...but Python agrees here "
                     f"({self.python_outputs[0]}): the difference is fixed-width "
                     f"overflow, not the refactor. Widen, or accept it as a real "
                     f"difference for machine integers.")
        return head


def _as_signed(bits: list[bool]) -> int:
    """Interpret a little-endian bit list as two's complement."""
    n = 0
    for i, b in enumerate(bits):
        if b:
            n |= 1 << i
        # fall through
    if bits and bits[-1]:
        n -= 1 << len(bits)
    return n


class ProofRejected(RuntimeError):
    """The solver said UNSAT and the independent checker disagreed.

    This is never a statement about the user's code. It means the solver, the
    checker or the circuit compiler is broken, and it is raised rather than
    returned because there is no honest verdict to hand back: the two things
    that are supposed to agree did not.
    """


def _solve_miter(formula: CNF, engine: str, budget: int | None, want_proof: bool):
    """Solve the miter, optionally logging a DRAT proof.

    Returns ``(status, model, steps, conflicts)`` with ``status is None``
    meaning the budget ran out.

    This deliberately does not go through :func:`cdclkit.pipeline.solve_adaptive`.
    Preprocessing rewrites the formula -- bounded variable elimination in
    particular adds clauses that do not follow from the input alone -- so a
    refutation of the preprocessed formula is not a refutation of the miter,
    and checking it against the miter would fail. Given a choice between a
    faster solve and a checkable one, this module takes the checkable one.
    """
    if engine == "native" and _native_available():
        from . import native
        from dratify.lits import from_dimacs

        s = native.require().Solver(formula.nvars)
        if want_proof:
            s.enable_proof()  # must precede the first clause
        for c in formula.clauses:
            if not s.add_clause(list(c)):
                return False, None, None, s.conflicts
        res = s.solve(budget)
        if res is None:
            return None, None, None, s.conflicts
        steps = (None if res or not want_proof else
                 [(k, tuple(from_dimacs(d) for d in lits))
                  for k, lits in s.proof_steps()])
        return res, (list(s.model) if res else None), steps, s.conflicts

    from .solver import Solver

    proof = MemoryProof() if want_proof else None
    s = Solver(formula.nvars, proof=proof)
    if not s.add_cnf(formula):
        return False, None, (proof.steps if proof else None), s.stats.conflicts
    res = s.solve(max_conflicts=budget)
    if res is None:
        return None, None, None, s.stats.conflicts
    steps = None if res or not want_proof else proof.steps
    return res, (list(s.model) if res else None), steps, s.stats.conflicts


def equivalent(
    f: Callable,
    g: Callable,
    widths: dict[str, int],
    engine: str = "native",
    verify: bool = True,
    max_conflicts: int | None = None,
) -> EquivalenceResult:
    """Prove `f` and `g` agree on every input, or return one where they differ.

    `widths` maps each parameter name to its bit width. Both functions must
    take the same parameters.

    `verify` (on by default) makes the solver emit a DRAT proof of the
    equivalence and replays it through an independent checker before
    `result.proved` is allowed to be True. It costs roughly the solve again.
    Turning it off means the answer rests on the solver's word, which is the
    one thing this project exists not to ask of anyone.

    `max_conflicts` bounds the search. On exhaustion the result is
    `proved=None` -- undecided -- never `True`.

    The answer is about **fixed-width two's-complement arithmetic** at the
    declared widths, not about Python's arbitrary-precision integers -- see the
    module docstring. A counterexample is re-simulated before being returned,
    so it is never spurious.
    """
    import time

    t0 = time.perf_counter()
    formula = CNF()
    enc = Encoder(formula)

    out_f, inputs = compile_function(f, enc, widths)
    out_g, _ = compile_function(g, enc, widths, inputs=inputs)

    w = max(out_f.width, out_g.width)
    a, b = out_f.extend(w), out_g.extend(w)
    # the miter: assert at least one output bit differs
    enc.add([enc.xor_gate(x, y) for x, y in zip(a.bits, b.bits)])

    r = EquivalenceResult()
    r.width = max(widths.values()) if widths else 0
    r.vars = formula.nvars
    r.clauses = formula.nclauses

    status, model, steps, conflicts = _solve_miter(
        formula, engine, max_conflicts, want_proof=verify)
    r.conflicts = conflicts

    if status is None:  # budget exhausted -- decided nothing
        r.proved = None
        r.seconds = time.perf_counter() - t0
        return r

    if status is False:
        # The miter is unsatisfiable: no input distinguishes the two
        # functions. That is the claim the whole call exists to make, so it is
        # the claim that gets checked rather than trusted.
        if verify:
            from dratify.proof import check_proof

            chk = check_proof(formula, steps or [])
            if not chk.ok:
                raise ProofRejected(
                    f"the solver reported the functions equivalent, and the "
                    f"independent checker rejected its proof at step "
                    f"{chk.failed_step}: {chk.reason}. This is a bug in cdclkit, "
                    f"not in your code. Please report it with both functions "
                    f"and the widths."
                )
            r.proof_checked = True
            r.proof_steps = chk.steps
        r.proved = True
        r.seconds = time.perf_counter() - t0
        return r

    r.seconds = time.perf_counter() - t0

    def value(bv: BitVec, n: int) -> int:
        return _as_signed([model[l >> 1] != bool(l & 1) for l in bv.bits[:n]])

    r.counterexample = {
        name: value(bv, widths[name]) for name, bv in inputs.items()
    }
    # What the circuits actually produce. This is the authoritative answer:
    # it is the semantics the proof is about.
    r.outputs = (value(a, w), value(b, w))
    if r.outputs[0] == r.outputs[1]:
        raise AssertionError(
            f"the solver reported a difference at {r.counterexample} but both "
            f"circuits evaluate to {r.outputs[0]} there. That is a bug in this "
            f"compiler, not in your code."
        )

    # And what Python says, which is *not* the same question: Python integers
    # are arbitrary precision, so an operation that overflows the declared width
    # wraps in the circuit and does not in Python. When the circuits differ but
    # Python agrees, the divergence is an overflow artefact -- still a real
    # difference for fixed-width machine integers, but a different finding, and
    # the caller should be told which one they have.
    try:
        fv, gv = f(**r.counterexample), g(**r.counterexample)
        r.python_outputs = (fv, gv)
        r.overflow_only = (fv == gv)
    except Exception:
        r.python_outputs = None  # not every function accepts the raw ints
    return r
