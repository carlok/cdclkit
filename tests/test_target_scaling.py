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
cannot be trusted with. Multiplying the variables by 16 costs about 20x when
the search is linear (measured 19-23x on both engines; arrays outgrowing the
cache add a little) and about 256x when it is quadratic. The limit, 64, sits
between them with room on both sides. The first version stepped by 4 with a
limit of 8: linear is 4.5x there, and a macOS runner measured 8.3x on native
runs of 4 and 32 ms, so the margin was too thin. Each size takes the best of
five runs to damp noise.

Run against cdclkit 0.1.4, from before the fix, this test measures 252x on
native and 218x on Python, so it still fails where it should.
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
    for _ in range(5):
        t0 = time.perf_counter()
        sat = _solve(nvars, engine)
        best = min(best, time.perf_counter() - t0)
        assert sat
    return best


class TestUnusedVariablesCostLinearTime(unittest.TestCase):
    #: 16x the variables: ~20x if linear, ~256x if quadratic
    FACTOR = 16
    LIMIT = 64.0

    def _check(self, engine: str, small: int):
        t_small = _seconds(small, engine)
        t_large = _seconds(self.FACTOR * small, engine)
        ratio = t_large / max(t_small, 1e-4)
        self.assertLess(
            ratio, self.LIMIT,
            f"{engine}: {small:,} vars took {t_small:.3f}s and "
            f"{self.FACTOR * small:,} took {t_large:.3f}s, a {ratio:.1f}x "
            f"increase for {self.FACTOR}x the variables. Linear is ~20x; "
            f"quadratic is ~256x.")

    def test_python_engine(self):
        self._check("python", 1024)

    @unittest.skipUnless(native.available(),
                         "native engine not built for this interpreter")
    def test_native_engine(self):
        # Rust is fast enough that smaller sizes finish in under a millisecond,
        # which is timer noise rather than a measurement.
        self._check("native", 32768)


if __name__ == "__main__":
    unittest.main()
