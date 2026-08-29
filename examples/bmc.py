# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Bounded model checking of a sequential circuit.

Everything else in `examples/` is combinational -- one snapshot of a system.
Bounded model checking is the temporal version: unroll the transition relation
`k` times and ask whether a bad state is reachable within `k` steps.

    I(s0) ∧ T(s0,s1) ∧ T(s1,s2) ∧ ... ∧ T(s_{k-1},s_k) ∧ ( ⋁ᵢ Bad(sᵢ) )

Satisfiable means "here is a counterexample trace of length ≤ k", and the model
literally *is* the trace, state by state.  Unsatisfiable means no counterexample
of that length exists -- a bounded guarantee, and the one BMC actually gives
you.  (Unbounded proof needs induction or interpolation on top; the bounded
result is what SAT delivers directly, and it is what found the majority of real
hardware bugs in the decade after Biere et al. introduced it in 1999.)

The system here is a **linear feedback shift register**: state is n bits, each
step shifts right and feeds back the XOR of the tap positions into the top bit.
Two properties are checked:

1. *the all-zero state is unreachable from a non-zero seed* -- true, because the
   LFSR transition is a linear bijection and 0 maps to 0, so no non-zero state
   can ever reach it.  UNSAT, with the DRAT proof checked here.
2. *a specific target state is reachable in exactly k steps* -- SAT, and the
   witness trace is re-simulated in Python bit by bit to confirm the solver did
   not hallucinate it.

A note on what the numbers mean: both queries here are solved with **zero
conflicts**, because a fixed seed (or a fixed target) determines the entire
unrolled trace by propagation alone -- an LFSR is a chain of XOR gates, and
unit propagation evaluates it.  That is the honest reading, and it is the point
rather than a disappointment: the interesting artefact is the *certificate*,
and BMC gets hard exactly when the transition relation stops being
deterministic in one direction (non-deterministic inputs, several processes,
memories).

Run:  python3 examples/bmc.py
"""

from __future__ import annotations

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from dratify.cnf import CNF
from cdclkit.encodings import Encoder
from dratify.lits import mk_lit, neg
from dratify.proof import MemoryProof, check_proof
from cdclkit.solver import Solver

WIDTH = 12
TAPS = (0, 3, 5, 11)  # feedback taps (bit indices)


# --------------------------------------------------------------------------
# the reference implementation, in Python
# --------------------------------------------------------------------------


def step(state: tuple[int, ...]) -> tuple[int, ...]:
    fb = 0
    for t in TAPS:
        fb ^= state[t]
    return (fb,) + state[:-1]


def simulate(seed: tuple[int, ...], steps: int) -> list[tuple[int, ...]]:
    trace = [seed]
    for _ in range(steps):
        trace.append(step(trace[-1]))
    return trace


# --------------------------------------------------------------------------
# the unrolled encoding
# --------------------------------------------------------------------------


def unroll(k: int) -> tuple[CNF, list[list[int]], Encoder]:
    """Build k transition steps; returns the formula and the state literals."""
    f = CNF()
    enc = Encoder(f)
    states = [[mk_lit(f.new_var(f"s{t}b{i}")) for i in range(WIDTH)] for t in range(k + 1)]
    for t in range(k):
        cur, nxt = states[t], states[t + 1]
        # feedback bit: XOR of the taps, wired as a gate chain
        fb = cur[TAPS[0]]
        for tap in TAPS[1:]:
            fb = enc.xor_gate(fb, cur[tap])
        enc.equiv(nxt[0], fb)
        for i in range(1, WIDTH):
            enc.equiv(nxt[i], cur[i - 1])
    return f, states, enc


def state_is(lits: list[int], bits: tuple[int, ...]) -> list[int]:
    """Literals asserting that a state equals a concrete bit pattern."""
    return [lits[i] if bits[i] else neg(lits[i]) for i in range(WIDTH)]


def show(bits) -> str:
    return "".join(str(b) for b in bits)


def read_state(model, lits) -> tuple[int, ...]:
    return tuple(1 if model[l >> 1] != bool(l & 1) else 0 for l in lits)


# --------------------------------------------------------------------------
# property 1: the all-zero state is unreachable
# --------------------------------------------------------------------------


def check_zero_unreachable(k: int) -> None:
    print(f"\n=== property 1: all-zero state unreachable within {k} steps ===")
    f, states, enc = unroll(k)
    seed = tuple(1 if i == 0 else 0 for i in range(WIDTH))
    for l in state_is(states[0], seed):
        f.add([l])
    # bad state: some time step is all zeros
    bad = []
    for t in range(k + 1):
        z = enc.and_gate([neg(l) for l in states[t]])
        bad.append(z)
    f.add(bad)

    print(f"unrolled CNF: {f.nvars} variables, {f.nclauses} clauses")
    proof = MemoryProof()
    s = Solver(f.nvars, proof=proof)
    ok = s.add_cnf(f)
    t0 = time.perf_counter()
    sat = s.solve() if ok else False
    dt = time.perf_counter() - t0
    if sat:
        print("counterexample found -- the property is FALSE")
        return
    print(f"UNSAT in {dt*1000:.1f} ms ({s.stats.conflicts} conflicts): "
          f"no trace of length <= {k} reaches the all-zero state")
    t0 = time.perf_counter()
    res = check_proof(f, proof)
    print(f"DRAT proof: {len(proof.steps)} steps, checked in {time.perf_counter()-t0:.2f}s "
          f"-> {'VERIFIED' if res.ok else 'REJECTED: ' + res.reason}")
    assert res.ok


# --------------------------------------------------------------------------
# property 2: a target state is reachable, with the witness trace
# --------------------------------------------------------------------------


def find_trace(k: int) -> None:
    print(f"\n=== property 2: reach a target state in exactly {k} steps ===")
    seed = tuple(1 if i == 0 else 0 for i in range(WIDTH))
    target = simulate(seed, k)[-1]
    print(f"target (computed by simulation): {show(target)}")

    f, states, enc = unroll(k)
    for l in state_is(states[k], target):
        f.add([l])
    # do NOT constrain the seed: the solver must find a predecessor itself
    s = Solver(f.nvars)
    ok = s.add_cnf(f)
    t0 = time.perf_counter()
    sat = s.solve() if ok else False
    dt = time.perf_counter() - t0
    assert sat, "the target is reachable by construction"
    trace = [read_state(s.model, states[t]) for t in range(k + 1)]
    print(f"SAT in {dt*1000:.1f} ms ({s.stats.conflicts} conflicts, "
          f"{s.stats.decisions} decisions)")
    print("witness trace:")
    for t, st in enumerate(trace):
        print(f"  t={t:>2}  {show(st)}")

    # re-simulate the witness independently
    ref = simulate(trace[0], k)
    assert ref == trace, "the solver's trace is not a real execution"
    assert trace[-1] == target
    print("the trace was re-simulated in Python and matches step for step")

    # the LFSR is a bijection, so the predecessor is unique -- prove it
    block = [neg(l) for l in state_is(states[0], trace[0])]
    f2 = f.copy()
    f2.add(block)
    proof = MemoryProof()
    s2 = Solver(f2.nvars, proof=proof)
    ok = s2.add_cnf(f2)
    second = s2.solve() if ok else False
    if second:
        print("more than one predecessor: the transition is not injective")
    else:
        res = check_proof(f2, proof)
        print(f"the predecessor is unique ({len(proof.steps)}-step proof -> "
              f"{'VERIFIED' if res.ok else 'REJECTED'}), which is exactly what "
              "'the transition relation is a bijection' means")
        assert res.ok


if __name__ == "__main__":
    print(f"LFSR: {WIDTH} bits, taps at {TAPS}")
    check_zero_unreachable(k=10)
    find_trace(k=8)
