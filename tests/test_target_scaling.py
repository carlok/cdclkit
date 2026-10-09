# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Target phases must not make the search quadratic in the number of variables.

With target phases on (the default), each time the trail reached a new depth
the solver copied the whole trail into the target. The comment beside it said
improvements "become rare quickly". That holds only once conflicts happen. A
search that makes many decisions without a conflict improves on every one, so
n decisions copied 1, 2, ..., n entries.

Measured on the Python engine, solving one unit clause in a formula that
declares n variables: 4,096 took 0.8 s, 16,384 took 10.6 s and 65,536 took
144 s -- each 4x costing about 13x. Turning target phases off made 16,384
take 0.11 s. Since dratify 0.1.7 a header may declare up to 2^20 variables
from a file of any length, so a 22-byte file cost hours of CPU.

The test compares scaling rather than absolute time, which shared CI runners
cannot be trusted with: quadrupling the variables should cost about 4x when
the search is linear and about 16x when it is quadratic. The threshold sits
between them, and each size takes the best of three runs to damp noise.
"""

from __future__ import annotations

import time
import unittest

from cdclkit import native
from cdclkit.solver import Solver


def _solve(nvars: int, engine: str) -> bool:
    """One unit clause, `nvars` declared: every other variable is a decision."""
    if engine == "native":
        s = native.require().Solver(nvars)   # defaults match Config
    else:
        s = Solver(nvars)
    s.add_clause([0])
    return s.solve()


def _seconds(nvars: int, engine: str) -> float:
    best = float("inf")
    for _ in range(3):
        t0 = time.perf_counter()
        sat = _solve(nvars, engine)
        best = min(best, time.perf_counter() - t0)
        assert sat
    return best


class TestUnusedVariablesCostLinearTime(unittest.TestCase):
    #: quadrupling: ~4x if linear, ~16x if quadratic
    LIMIT = 8.0

    def _check(self, engine: str, small: int):
        t_small = _seconds(small, engine)
        t_large = _seconds(4 * small, engine)
        ratio = t_large / max(t_small, 1e-4)
        self.assertLess(
            ratio, self.LIMIT,
            f"{engine}: {small:,} vars took {t_small:.3f}s and "
            f"{4 * small:,} took {t_large:.3f}s, a {ratio:.1f}x increase for "
            f"4x the variables. Linear is ~4x; this is closer to quadratic.")

    def test_python_engine(self):
        self._check("python", 4096)

    @unittest.skipUnless(native.available(),
                         "native engine not built for this interpreter")
    def test_native_engine(self):
        # Rust is fast enough that the quadratic term only dominates at
        # larger sizes.
        self._check("native", 32768)


if __name__ == "__main__":
    unittest.main()
