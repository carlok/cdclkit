# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Refuse functions that `cdclkit.pyeq` would model unsoundly.

`pyeq` has a known bug: `_Compiler.result()` takes the last recorded return as
an *unconditional* fallback and discards its path condition. So a function that
can reach the end without returning compiles to whatever its last branch
returned, for every input:

    def a(x):
        if x > 0:
            return 1        # Python: a(-1) is None

    equivalent(a, lambda-equivalent-of-`return 1`)  ->  proved = True

Measured, this is the *only* shape that misbehaves -- functions where every path
returns are handled correctly, and so is guard-clause restructuring, which is
the most common "refactor for clarity" output. But "the model dropped a return
path" is exactly a refactor bug this experiment exists to count, so leaving it
in would bias the headline number downward by an amount nobody can quantify.

This is a pre-flight check, not a fix. When the compiler is fixed the guard
becomes unnecessary, and re-running the experiment without it measures what the
bug was costing.
"""

from __future__ import annotations

import ast
import sys


def definitely_returns(body: list[ast.stmt]) -> bool:
    """True when every path through `body` hits a `return`.

    Conservative in the direction that matters: when unsure, say False, which
    means the function gets excluded rather than silently mismodelled.
    """
    for stmt in body:
        if isinstance(stmt, ast.Return):
            return True
        if isinstance(stmt, ast.If):
            # An `if` without `else` cannot guarantee a return: the condition
            # may be false and control falls past it.
            if stmt.orelse and definitely_returns(stmt.body) \
                    and definitely_returns(stmt.orelse):
                return True
        # A `for` body may execute zero times, so it never guarantees a return.
        # `while True:` would, but pyeq rejects `while` outright, so the case
        # cannot arise here.
    return False


def falls_off_the_end(fn) -> bool:
    """True when `fn` has a path reaching its end without returning."""
    import inspect
    import textwrap

    tree = ast.parse(textwrap.dedent(inspect.getsource(fn)))
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            return not definitely_returns(node.body)
    raise ValueError(f"no function definition found in {fn!r}")


def _self_test() -> int:
    """The guard must reject and accept. One that only ever accepts is a no-op."""

    def every_path(x):
        if x > 0:
            return 1
        return 2

    def guard_clauses(x, y):
        if x <= 0:
            return 0
        if y <= 0:
            return x
        return x + y

    def loop_then_return(x):
        n = 0
        for _i in range(4):
            n += x
        return n

    def bare(x):
        return x

    def falls(x):
        if x > 0:
            return 1                      # no else, no trailing return

    def falls_in_loop(x):
        for _i in range(4):
            if x > 0:
                return 1                  # loop may not run, if may not fire

    def falls_nested(x, y):
        if x > 0:
            if y > 0:
                return 1
            return 2                      # inner covered, outer is not

    accept = [every_path, guard_clauses, loop_then_return, bare]
    reject = [falls, falls_in_loop, falls_nested]

    bad = 0
    for f in accept:
        if falls_off_the_end(f):
            print(f"  FAIL {f.__name__}: rejected, but every path returns")
            bad += 1
    for f in reject:
        if not falls_off_the_end(f):
            print(f"  FAIL {f.__name__}: accepted, but a path falls through")
            bad += 1
    print(f"  guard self-test: {len(accept)} accept + {len(reject)} reject, "
          f"{bad} wrong")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(_self_test() if "--self-test" in sys.argv else 0)
