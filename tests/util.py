# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Shared helpers for the test suite."""

from __future__ import annotations

import os
import random

from dratify.cnf import CNF
from dratify.lits import mk_lit
from dratify.proof import MemoryProof
from cdclkit.solver import Solver


def random_cnf(rng: random.Random, max_vars: int = 10, ratio: float = 4.5,
               k_choices=(1, 2, 3, 3, 3)) -> CNF:
    """A small random CNF, sized so brute force stays instant."""
    n = rng.randint(2, max_vars)
    m = rng.randint(1, max(1, int(ratio * n)))
    f = CNF(n)
    for _ in range(m):
        k = min(rng.choice(k_choices), n)
        vs = rng.sample(range(n), k)
        f.add([mk_lit(v, rng.random() < 0.5) for v in vs])
    return f


def solve_with_proof(f: CNF):
    """Solve ``f`` while recording a DRAT proof.  Returns ``(sat, proof)``."""
    proof = MemoryProof()
    s = Solver(f.nvars, proof=proof)
    ok = s.add_cnf(f)
    sat = bool(s.solve()) if ok else False
    return sat, proof


# --------------------------------------------------------------------------
# fuzzing support
# --------------------------------------------------------------------------
#
# A fuzzer that finds a bug you cannot reproduce is worse than no fuzzer at
# all, so nothing here ever draws from the global `random` module or from the
# clock.  Every case is derived from `fuzz_seed(base) + case_index`, which is
# reported in the subTest label, so a red run names the exact integer needed to
# replay it in isolation.


def fuzz_seed(base: int) -> int:
    """Seed base for a fuzz family, overridable to re-run a reported failure.

    ``CDCLKIT_FUZZ_SEED=12345 python3 -m unittest discover -s tests`` shifts
    every seeded family by the same offset, which is how you widen the search after a clean
    run without editing the source.
    """
    return base + int(os.environ.get("CDCLKIT_FUZZ_SEED", "0"))


def fuzz_cases(default: int) -> int:
    """Case count for one fuzz family, scaled by ``CDCLKIT_FUZZ``.

    These run inside ``make gate``, which must stay in the seconds.  The
    default budget is chosen for that; ``CDCLKIT_FUZZ=20`` turns the same code
    into a soak test without a second implementation to maintain.
    """
    try:
        factor = float(os.environ.get("CDCLKIT_FUZZ", "1"))
    except ValueError:
        factor = 1.0
    return max(1, int(default * factor))
