# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The baselines pyeq has to beat to be worth anything.

Every baseline runs against a *wrapped source* form of the function: the same
body with each arithmetic operation explicitly masked to the declared width.
Executing that under ordinary Python gives exactly the circuit's semantics,
which is what makes the comparison with pyeq legitimate (see wrapping.py).

Two independent implementations of fixed-width semantics live in this
experiment -- the AST interpreter in `wrapping.py` and the source transform
here. `--cross-check` requires them to agree, on the same principle as the
differential encoding work in `cdclkit/model.py`: one implementation of a
translation is an assumption, two that agree is evidence.
"""

from __future__ import annotations

import ast
import inspect
import random
import textwrap
from typing import Callable

from wrapping import wrap


class _Wrapper(ast.NodeTransformer):
    """Mask every arithmetic result to `width` bits."""

    def __init__(self, width: int) -> None:
        self.w = width

    def _call(self, node: ast.expr) -> ast.expr:
        return ast.Call(func=ast.Name(id="_w", ctx=ast.Load()),
                        args=[node, ast.Constant(value=self.w)], keywords=[])

    #: ops whose right operand the compiler consumes as a raw Python int
    #: (a shift count or a power-of-two divisor) rather than turning it into a
    #: bit-vector -- see `binop` in cdclkit/pyeq.py
    _RAW_RIGHT = (ast.LShift, ast.RShift, ast.FloorDiv, ast.Mod)

    def visit_BinOp(self, node: ast.BinOp) -> ast.expr:
        if isinstance(node.op, self._RAW_RIGHT):
            # Leave the right operand alone. Truncating it would turn
            # `// 256` at width 8 into a division by zero, whereas the circuit
            # compiles it to an arithmetic shift right by 8 -- which is what
            # unwrapped Python floor division already does.
            node.left = self.visit(node.left)
        else:
            self.generic_visit(node)
        return self._call(node)

    def visit_UnaryOp(self, node: ast.UnaryOp) -> ast.expr:
        self.generic_visit(node)
        if isinstance(node.op, (ast.USub, ast.Invert)):
            return self._call(node)
        return node

    def visit_AugAssign(self, node: ast.AugAssign) -> ast.stmt:
        # `total += a` is not a BinOp node, so visit_BinOp never sees it and
        # the accumulation would run at full Python precision. Desugar to an
        # explicit BinOp and let the normal path wrap it.
        desugared = ast.Assign(
            targets=[ast.Name(id=node.target.id, ctx=ast.Store())],
            value=ast.BinOp(left=ast.Name(id=node.target.id, ctx=ast.Load()),
                            op=node.op, right=node.value))
        return self.visit(ast.fix_missing_locations(desugared))

    def visit_For(self, node: ast.For) -> ast.stmt:
        # `range(8)` is structural: the compiler reads the bound as a raw int
        # and unrolls, so truncating it to the width would turn `range(8)` at
        # width 4 into `range(-8)` -- an empty loop that silently returns the
        # initial accumulator. Visit the body, never the iterator.
        node.body = [self.visit(s) for s in node.body]
        node.orelse = [self.visit(s) for s in node.orelse]
        # the compiler binds the loop variable through `const()`, which does
        # truncate -- mirror that
        bind = ast.parse(f"{node.target.id} = _w({node.target.id}, {self.w})").body[0]
        node.body = [bind] + node.body
        return node

    def visit_Constant(self, node: ast.Constant) -> ast.expr:
        # `BitVec.constant` keeps bits 0..width-1, so the circuit truncates
        # constants. Shift counts and divisors are exempt (see visit_BinOp).
        if isinstance(node.value, int) and not isinstance(node.value, bool):
            return ast.Constant(value=wrap(node.value, self.w))
        return node


def wrapped_source(fn: Callable, width: int, name: str) -> str:
    """Source for `fn` renamed to `name`, wrapping every op to `width` bits.

    Parameters are wrapped on entry, which is what the circuit does with its
    input bit-vectors. Loop variables are wrapped where they are bound.
    """
    tree = ast.parse(textwrap.dedent(inspect.getsource(fn)))
    fdef = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef))
    fdef.name = name
    fdef.decorator_list = []

    params = [a.arg for a in fdef.args.args]
    body = _Wrapper(width).visit(ast.Module(body=fdef.body, type_ignores=[]))
    prologue = [
        ast.parse(f"{p} = _w({p}, {width})").body[0] for p in params
    ]
    fdef.body = prologue + body.body
    ast.fix_missing_locations(fdef)
    return ast.unparse(fdef)


def compile_wrapped(fn: Callable, width: int) -> Callable:
    ns: dict = {"_w": wrap}
    exec(compile(ast.parse(wrapped_source(fn, width, "_f")), "<wrapped>", "exec"), ns)
    return ns["_f"]


# ---------------------------------------------------------------------------
# vector sources
# ---------------------------------------------------------------------------

def _edge_values(width: int) -> list[int]:
    lo, hi = -(1 << (width - 1)), (1 << (width - 1)) - 1
    vals = {0, 1, -1, 2, -2, lo, hi, lo + 1, hi - 1, 3, -3}
    k = 1
    while k <= hi:
        vals.update({k, -k, k - 1, k + 1})
        k <<= 1
    return sorted(v for v in vals if lo <= v <= hi)


def _cartesian(vals: list[int], arity: int, cap: int) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = [()]
    for _ in range(arity):
        out = [t + (v,) for t in out for v in vals]
        if len(out) > cap:
            rng = random.Random(20260829)
            out = rng.sample(out, cap)
    return out


def _random_vectors(arity: int, width: int, n: int, seed: int) -> list[tuple[int, ...]]:
    rng = random.Random(seed)
    lo, hi = -(1 << (width - 1)), (1 << (width - 1)) - 1
    return [tuple(rng.randint(lo, hi) for _ in range(arity)) for _ in range(n)]


def _first_difference(fa: Callable, fb: Callable,
                      vectors) -> tuple[int, ...] | None:
    for vec in vectors:
        try:
            a = fa(*vec)
        except Exception:
            a = ("raised",)
        try:
            b = fb(*vec)
        except Exception:
            b = ("raised",)
        if a != b:
            return vec
    return None


# ---------------------------------------------------------------------------
# the baselines
# ---------------------------------------------------------------------------

def baseline_random(orig, ref, arity, width, n, seed):
    fa, fb = compile_wrapped(orig, width), compile_wrapped(ref, width)
    return _first_difference(fa, fb, _random_vectors(arity, width, n, seed))


def baseline_edge(orig, ref, arity, width, cap=20000):
    fa, fb = compile_wrapped(orig, width), compile_wrapped(ref, width)
    return _first_difference(fa, fb, _cartesian(_edge_values(width), arity, cap))


def baseline_hypothesis(orig, ref, arity, width, max_examples=1000):
    """Hypothesis with a stated budget. Returns a falsifying vector or None."""
    try:
        from hypothesis import given, settings, strategies as st, HealthCheck
        from hypothesis import seed as hyp_seed
    except ImportError:
        return "unavailable"

    fa, fb = compile_wrapped(orig, width), compile_wrapped(ref, width)
    lo, hi = -(1 << (width - 1)), (1 << (width - 1)) - 1
    found: list[tuple[int, ...]] = []

    ints = st.integers(min_value=lo, max_value=hi)

    @hyp_seed(20260829)
    @settings(max_examples=max_examples, deadline=None, database=None,
              suppress_health_check=list(HealthCheck))
    @given(st.tuples(*[ints] * arity))
    def prop(vec):
        try:
            a = fa(*vec)
        except Exception:
            a = ("raised",)
        try:
            b = fb(*vec)
        except Exception:
            b = ("raised",)
        if a != b:
            found.append(vec)
        assert a == b

    try:
        prop()
    except AssertionError:
        pass
    return found[-1] if found else None
