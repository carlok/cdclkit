# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Proving a refactor is safe, and catching one that is not.

Tests check the inputs you thought of. This checks all of them: each function
is compiled to a fixed-width bit-vector circuit, the two are wired into a
miter, and the solver either proves no input distinguishes them or hands back
one that does.

Run:  python3 examples/refactor_check.py
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from cdclkit.pyeq import UnsupportedConstruct, equivalent

WIDTH = 8


def check(title: str, f, g, widths, expect_equal: bool) -> None:
    r = equivalent(f, g, widths=widths)
    verdict = "EQUIVALENT" if r.proved else "DIFFERS"
    print(f"\n=== {title} ===")
    print(f"  {verdict}   {r.report()}")
    assert r.proved is expect_equal, f"{title}: expected proved={expect_equal}"
    # "EQUIVALENT" here is not the solver's opinion. The refutation it produced
    # was replayed by a checker that shares no code with it, and only then was
    # the answer allowed to say so.
    if r.proved:
        assert r.proof_checked and r.proof_steps > 0, "proved without a proof"


# --------------------------------------------------------------------------
# 1. an optimisation that is safe
# --------------------------------------------------------------------------

def scale_original(a, b):
    return a * 2 + b * 2


def scale_refactored(a, b):
    return (a + b) << 1


# --------------------------------------------------------------------------
# 2. an off-by-one that no small test would catch
# --------------------------------------------------------------------------

def clamp_original(x, lo, hi):
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


def clamp_refactored(x, lo, hi):
    # the bug: `>=` instead of `>` returns hi when x == hi, which is the same
    # value -- so this is still correct. The real bug is below.
    if x < lo:
        return lo
    if x >= hi:
        return hi
    return x


def clamp_broken(x, lo, hi):
    # swaps the order of the bounds checks, which only matters when lo > hi
    if x > hi:
        return hi
    if x < lo:
        return lo
    return x


# --------------------------------------------------------------------------
# 3. a loop replaced by a closed form
# --------------------------------------------------------------------------

def sum_loop(n):
    total = 0
    for _i in range(5):
        total = total + n
    return total


def sum_closed(n):
    return n * 5


# --------------------------------------------------------------------------
# 4. a rewrite that is only correct when nothing overflows
# --------------------------------------------------------------------------

def average_naive(a, b):
    return (a + b) >> 1


def average_safe(a, b):
    # the classic overflow-avoiding form
    return a + ((b - a) >> 1)


def main() -> None:
    print("Proving refactors correct on every input, not just the tested ones.")

    check("strength reduction: a*2 + b*2  ->  (a+b) << 1",
          scale_original, scale_refactored,
          {"a": WIDTH, "b": WIDTH}, expect_equal=True)

    check("clamp: > replaced by >=",
          clamp_original, clamp_refactored,
          {"x": 6, "lo": 6, "hi": 6}, expect_equal=True)

    check("clamp: bounds checks reordered",
          clamp_original, clamp_broken,
          {"x": 6, "lo": 6, "hi": 6}, expect_equal=False)

    check("loop unrolled into a multiply",
          sum_loop, sum_closed, {"n": WIDTH}, expect_equal=True)

    # The interesting one. These two are the same in exact arithmetic, and the
    # second exists precisely because the first overflows. At a fixed width the
    # checker finds that difference -- and tells you Python would not have.
    r = equivalent(average_naive, average_safe, widths={"a": 8, "b": 8})
    print("\n=== average: (a+b)>>1  vs  a + ((b-a)>>1) ===")
    print(f"  {'EQUIVALENT' if r.proved else 'DIFFERS'}   {r.report()}")
    if not r.proved and r.overflow_only:
        print("  -> this is exactly why the second form exists: the naive one")
        print("     overflows, and the checker found an input that proves it.")

    print("\n=== unsupported code is rejected, never approximated ===")

    def unbounded(a):
        while a > 0:
            a = a - 1
        return a

    try:
        equivalent(unbounded, unbounded, widths={"a": 4})
        print("  ERROR: should have been rejected")
    except UnsupportedConstruct as e:
        print(f"  {str(e).splitlines()[0][:90]}")

    print("\n=== a check that gives up says so ===")
    r = equivalent(average_naive, average_naive, widths={"a": 16, "b": 16},
                   max_conflicts=1)
    print(f"  {r.report()}")
    assert r.proved is None, "an exhausted budget must decide nothing"
    assert not r, "undecided must never read as proved"

    print("\nEvery 'EQUIVALENT' above is a proof over the whole input space at")
    print(f"the declared width, not a sample. For two {WIDTH}-bit arguments that")
    print(f"is {2 ** (2 * WIDTH):,} input pairs -- and each proof was replayed")
    print("by an independent checker before being reported.")


if __name__ == "__main__":
    main()
