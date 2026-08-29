# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Evaluate a subset function with fixed-width two's-complement semantics.

This is the single most load-bearing piece of the experiment, and the easiest
thing to get quietly wrong.

`pyeq` answers "are these two functions identical **as fixed-width machine
integers**". Python answers "are they identical with arbitrary precision".
Those are different questions. If the sampling baselines run in Python
semantics while pyeq runs in circuit semantics, the two are not being compared
and the marginal catch rate -- the entire deliverable -- is meaningless.

So the baselines evaluate through this interpreter, which wraps after every
operation exactly as the circuit does. It is validated against `pyeq` itself:
when `pyeq` reports a counterexample it also reports the two circuit outputs at
that point, and this interpreter must reproduce them exactly.

Python's own `>>` on negatives is arithmetic and its `//` and `%` floor, which
matches `BitVec.shr(arithmetic=True)` and the power-of-two paths in
`cdclkit/pyeq.py`. So those operators need no correction -- only the wrap does.
"""

from __future__ import annotations

import ast
import inspect
import textwrap


def wrap(v: int, width: int) -> int:
    """Two's-complement wrap to `width` bits."""
    half = 1 << (width - 1)
    return ((v + half) & ((1 << width) - 1)) - half


class _Interp:
    def __init__(self, width: int, env: dict[str, int]) -> None:
        self.w = width
        self.env = env

    def _w(self, v: int) -> int:
        return wrap(v, self.w)

    def expr(self, n: ast.expr) -> int:
        if isinstance(n, ast.Constant):
            if isinstance(n.value, bool):
                return 1 if n.value else 0
            if isinstance(n.value, int):
                return self._w(n.value)
            raise ValueError(f"constant {n.value!r}")
        if isinstance(n, ast.Name):
            return self.env[n.id]
        if isinstance(n, ast.UnaryOp):
            v = self.expr(n.operand)
            if isinstance(n.op, ast.USub):
                return self._w(-v)
            if isinstance(n.op, ast.UAdd):
                return v
            if isinstance(n.op, ast.Invert):
                return self._w(~v)
            if isinstance(n.op, ast.Not):
                return 0 if self.truth(n.operand) else 1
            raise ValueError(type(n.op).__name__)
        if isinstance(n, ast.BinOp):
            op = n.op
            a = self.expr(n.left)
            if isinstance(op, (ast.LShift, ast.RShift, ast.FloorDiv, ast.Mod)):
                # raw int, not a width-truncated bit-vector -- matches the
                # `k = node.right.value` path in cdclkit/pyeq.py's `binop`
                if not isinstance(n.right, ast.Constant):
                    raise ValueError(f"{type(op).__name__} by a non-constant")
                b = n.right.value
            else:
                b = self.expr(n.right)
            if isinstance(op, ast.Add):
                return self._w(a + b)
            if isinstance(op, ast.Sub):
                return self._w(a - b)
            if isinstance(op, ast.Mult):
                return self._w(a * b)
            if isinstance(op, ast.BitAnd):
                return self._w(a & b)
            if isinstance(op, ast.BitOr):
                return self._w(a | b)
            if isinstance(op, ast.BitXor):
                return self._w(a ^ b)
            if isinstance(op, ast.LShift):
                return self._w(a << b) if b >= 0 else self._raise_shift()
            if isinstance(op, ast.RShift):
                return self._w(a >> b) if b >= 0 else self._raise_shift()
            if isinstance(op, ast.FloorDiv):
                return self._w(a // b)
            if isinstance(op, ast.Mod):
                return self._w(a % b)
            raise ValueError(type(op).__name__)
        if isinstance(n, ast.IfExp):
            return self.expr(n.body) if self.truth(n.test) else self.expr(n.orelse)
        if isinstance(n, (ast.Compare, ast.BoolOp)):
            return 1 if self.truth(n) else 0
        raise ValueError(type(n).__name__)

    @staticmethod
    def _raise_shift():
        raise ValueError("negative shift count")

    def truth(self, n: ast.expr) -> bool:
        if isinstance(n, ast.Compare):
            if len(n.ops) != 1:
                raise ValueError("chained comparison")
            a, b = self.expr(n.left), self.expr(n.comparators[0])
            op = n.ops[0]
            if isinstance(op, ast.Lt):
                return a < b
            if isinstance(op, ast.LtE):
                return a <= b
            if isinstance(op, ast.Gt):
                return a > b
            if isinstance(op, ast.GtE):
                return a >= b
            if isinstance(op, ast.Eq):
                return a == b
            if isinstance(op, ast.NotEq):
                return a != b
            raise ValueError(type(op).__name__)
        if isinstance(n, ast.BoolOp):
            vals = n.values
            if isinstance(n.op, ast.And):
                return all(self.truth(v) for v in vals)
            return any(self.truth(v) for v in vals)
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.Not):
            return not self.truth(n.operand)
        return self.expr(n) != 0


class _Return(Exception):
    def __init__(self, value: int) -> None:
        self.value = value


def _block(interp: _Interp, body: list[ast.stmt]) -> None:
    for s in body:
        if isinstance(s, ast.Return):
            raise _Return(0 if s.value is None else interp.expr(s.value))
        if isinstance(s, ast.Assign):
            if len(s.targets) != 1 or not isinstance(s.targets[0], ast.Name):
                raise ValueError("tuple or attribute assignment")
            interp.env[s.targets[0].id] = interp.expr(s.value)
        elif isinstance(s, ast.AugAssign):
            if not isinstance(s.target, ast.Name):
                raise ValueError("augmented assignment to a non-name")
            cur = ast.BinOp(left=ast.Name(id=s.target.id, ctx=ast.Load()),
                            op=s.op, right=s.value)
            interp.env[s.target.id] = interp.expr(ast.fix_missing_locations(cur))
        elif isinstance(s, ast.If):
            _block(interp, s.body if interp.truth(s.test) else s.orelse)
        elif isinstance(s, ast.For):
            call = s.iter
            lo_hi = [c.value for c in call.args]
            for i in range(*lo_hi):
                interp.env[s.target.id] = interp._w(i)
                _block(interp, s.body)
        elif isinstance(s, ast.Pass) or (isinstance(s, ast.Expr)
                                         and isinstance(s.value, ast.Constant)):
            continue
        else:
            raise ValueError(type(s).__name__)


def evaluate(fn, args: dict[str, int], width: int) -> int:
    """Run `fn` on `args`, wrapping every operation to `width` bits."""
    tree = ast.parse(textwrap.dedent(inspect.getsource(fn)))
    fdef = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef))
    env = {k: wrap(v, width) for k, v in args.items()}
    interp = _Interp(width, env)
    try:
        _block(interp, fdef.body)
    except _Return as r:
        return r.value
    # Falls off the end. The guard excludes these, so reaching here is a bug in
    # the harness rather than in the function under test.
    raise ValueError(f"{fn.__name__} fell off the end -- guard.py should have "
                     f"excluded it")
