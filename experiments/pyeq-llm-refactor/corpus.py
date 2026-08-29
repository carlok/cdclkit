# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Frozen corpus for the LLM-refactor experiment.

Small integer functions of recognisable shapes -- bit twiddling, saturating
arithmetic, clamping, comparator networks, packing. Chosen from what a working
engineer writes, NOT from what `cdclkit.pyeq` is known to handle well; that
distinction is what makes the resulting number mean anything.

**Frozen before any refactor is generated, and not to be edited afterwards.**
Iterating on the corpus after seeing results is the training-on-the-test-set
failure this repository already documents about its own kissat number.

Every function here stays inside pyeq's verified subset: `+ - *`, `& | ^ ~`,
`<< >>`, comparisons, `and/or/not`, `if`/ternary, `for i in range(k)` with
constant k, assignment, augmented assignment, `return`. `//` and `%` only by
constant powers of two. No `while`, no calls, no subscripts -- all four are
rejected by the compiler, and an external brief that claimed `while` was
supported is the reason this docstring is explicit.

Every function returns on every path, which `guard.py` enforces.
"""

from __future__ import annotations


# -- sign, magnitude, comparison ------------------------------------------

def f_abs(a):
    if a < 0:
        return -a
    return a


def f_sign(a):
    if a > 0:
        return 1
    if a < 0:
        return -1
    return 0


def f_max2(a, b):
    if a > b:
        return a
    return b


def f_min2(a, b):
    if a < b:
        return a
    return b


def f_max3(a, b, c):
    m = a
    if b > m:
        m = b
    if c > m:
        m = c
    return m


def f_median3(a, b, c):
    if a > b:
        t = a
        a = b
        b = t
    if b > c:
        b = c
    if a > b:
        b = a
    return b


def f_cmp3(a, b):
    if a < b:
        return -1
    if a > b:
        return 1
    return 0


def f_in_range(a, lo, hi):
    if a < lo:
        return 0
    if a > hi:
        return 0
    return 1


def f_clamp(x, lo, hi):
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


def f_cond_negate(a, flag):
    if flag != 0:
        return -a
    return a


def f_cond_swap_hi(a, b):
    if a > b:
        return a
    return b


# -- saturating and wrapping arithmetic -----------------------------------

def f_sat_add(a, b):
    s = a + b
    if a > 0 and b > 0 and s < 0:
        return 127
    if a < 0 and b < 0 and s > 0:
        return -128
    return s


def f_sat_sub(a, b):
    d = a - b
    if a >= 0 and b < 0 and d < 0:
        return 127
    if a < 0 and b > 0 and d > 0:
        return -128
    return d


def f_double_clamped(a):
    d = a + a
    if a > 0 and d < 0:
        return 127
    if a < 0 and d > 0:
        return -128
    return d


def f_avg_floor(a, b):
    return (a + b) >> 1


def f_avg_no_overflow(a, b):
    return a + ((b - a) >> 1)


def f_lerp_half(a, b):
    return a + ((b - a) >> 1)


def f_diff_or_zero(a, b):
    if a > b:
        return a - b
    return 0


# -- bit counting and parity ----------------------------------------------

def f_popcount8(a):
    n = 0
    for _i in range(8):
        n = n + (a & 1)
        a = a >> 1
    return n


def f_parity8(a):
    p = 0
    for _i in range(8):
        p = p ^ (a & 1)
        a = a >> 1
    return p


def f_hamming8(a, b):
    x = a ^ b
    n = 0
    for _i in range(8):
        n = n + (x & 1)
        x = x >> 1
    return n


def f_trailing_zeros8(a):
    n = 0
    for _i in range(8):
        if (a & 1) == 0 and n == _i:
            n = n + 1
        a = a >> 1
    return n


def f_count_leading_ones8(a):
    n = 0
    for i in range(8):
        b = (a >> (7 - i)) & 1
        if b == 1 and n == i:
            n = n + 1
    return n


def f_highest_bit8(a):
    h = 0
    for i in range(8):
        if ((a >> i) & 1) != 0:
            h = i
    return h


# -- bit manipulation ------------------------------------------------------

def f_bit_test(a, i):
    return (a >> 3) & 1


def f_bit_set3(a):
    return a | 8


def f_bit_clear3(a):
    return a & ~8


def f_bit_toggle3(a):
    return a ^ 8


def f_swap_nibbles(a):
    return ((a & 15) << 4) | ((a >> 4) & 15)


def f_reverse4(a):
    r = 0
    for i in range(4):
        r = (r << 1) | ((a >> i) & 1)
    return r


def f_rotl4(a):
    return ((a << 1) & 15) | ((a >> 3) & 1)


def f_gray_encode(a):
    return a ^ (a >> 1)


def f_gray_decode4(a):
    b = a
    b = b ^ (b >> 1)
    b = b ^ (b >> 2)
    return b & 15


def f_interleave2(a, b):
    r = 0
    for i in range(4):
        r = r | (((a >> i) & 1) << (i + i))
        r = r | (((b >> i) & 1) << (i + i + 1))
    return r


def f_mask_low(a, k):
    return a & 15


def f_extract_field(a):
    return (a >> 2) & 7


def f_is_power_of_two(a):
    if a <= 0:
        return 0
    if (a & (a - 1)) == 0:
        return 1
    return 0


def f_next_pow2_8(a):
    a = a - 1
    a = a | (a >> 1)
    a = a | (a >> 2)
    a = a | (a >> 4)
    return a + 1


# -- alignment and scaling by powers of two --------------------------------

def f_align_down8(a):
    return a & ~7


def f_align_up8(a):
    return (a + 7) & ~7


def f_div_round_up4(a):
    return (a + 3) >> 2


def f_scale_half(a):
    return a >> 1


def f_fixed_mul_q8(a, b):
    return (a * b) // 256


def f_fixed_mul_q4(a, b):
    return (a * b) >> 4


def f_mod_pow2(a):
    return a % 16


def f_is_odd(a):
    return a & 1


def f_is_even(a):
    if (a & 1) == 0:
        return 1
    return 0


# -- packing ---------------------------------------------------------------

def f_pack_nibbles(hi, lo):
    return ((hi & 15) << 4) | (lo & 15)


def f_unpack_hi(a):
    return (a >> 4) & 15


def f_pack_rgb332(r, g, b):
    return ((r & 7) << 5) | ((g & 7) << 2) | (b & 3)


def f_checksum_fold4(a):
    s = 0
    for i in range(4):
        s = s + ((a >> (i + i)) & 3)
    return s % 16


def f_accumulate(a):
    total = 0
    for _i in range(5):
        total += a
    return total


def f_weighted_sum(a, b):
    return (a << 2) + (b << 1) + a


#: Written naturally, rejected by the subset. Kept rather than rewritten,
#: because *why* they are rejected is a finding.
#:
#: All five shift by the loop variable -- `a >> i` inside `for i in range(8)`.
#: The unroller already binds `i` to a constant at each step
#: (`cdclkit/pyeq.py::unroll_for`: `self.env[node.target.id] = self.const(i)`),
#: but the shift guard in `binop` tests `isinstance(node.right, ast.Constant)`
#: at the AST level and never consults that environment. So the compiler knows
#: the value and refuses to look.
#:
#: That makes this an implementation oversight rather than a design limit, and
#: it costs 5 of 53 natural formulations -- 9.4% of a corpus written without
#: any thought for the tool. Reported, not worked around: rewriting these to
#: fit would hide exactly the coverage gap the experiment is supposed to
#: measure.
SUBSET_REJECTED = [
    "f_count_leading_ones8", "f_highest_bit8", "f_reverse4",
    "f_interleave2", "f_checksum_fold4",
]

#: The frozen list. Order is fixed; nothing is appended after the first run.
#: The five above are excluded -- their originals do not compile, so no
#: refactor of them could participate.
CORPUS = [
    f_abs, f_sign, f_max2, f_min2, f_max3, f_median3, f_cmp3, f_in_range,
    f_clamp, f_cond_negate, f_cond_swap_hi,
    f_sat_add, f_sat_sub, f_double_clamped, f_avg_floor, f_avg_no_overflow,
    f_lerp_half, f_diff_or_zero,
    f_popcount8, f_parity8, f_hamming8, f_trailing_zeros8,
    f_bit_test, f_bit_set3, f_bit_clear3, f_bit_toggle3, f_swap_nibbles,
    f_rotl4, f_gray_encode, f_gray_decode4,
    f_mask_low, f_extract_field, f_is_power_of_two, f_next_pow2_8,
    f_align_down8, f_align_up8, f_div_round_up4, f_scale_half,
    f_fixed_mul_q8, f_fixed_mul_q4, f_mod_pow2, f_is_odd, f_is_even,
    f_pack_nibbles, f_unpack_hi, f_pack_rgb332,
    f_accumulate, f_weighted_sum,
]
