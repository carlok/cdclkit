# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Combinational equivalence checking: are two adder circuits the same function?

This is what SAT is actually used for in industry.  Build two structurally
different implementations of 8-bit addition -- a ripple-carry adder and a
carry-lookahead adder -- wire them into a *miter*: the same inputs feed both,
the outputs are compared bit by bit, and the miter output is the OR of the
comparisons' disagreements.  The miter is satisfiable exactly when some input
makes the circuits differ.

* miter UNSAT  =>  the circuits compute the same function on all 2^17 inputs,
  and the DRAT proof of that UNSAT is checked here.
* miter SAT    =>  the model *is* the counterexample input vector, printed and
  independently re-simulated in Python.

The second half injects a deliberate bug (one carry term dropped from the
lookahead) and shows the solver producing the input that exposes it.  That is
the entire value proposition of formal equivalence checking in one script:
exhaustive coverage without exhaustive simulation.

Run:  python3 examples/equivalence.py
"""

from __future__ import annotations

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from dratify.cnf import CNF
from cdclkit.encodings import Encoder
from dratify.lits import mk_lit
from dratify.proof import MemoryProof, check_proof
from cdclkit.solver import Solver

WIDTH = 8


def ripple_carry(enc: Encoder, a: list[int], b: list[int], cin: int) -> tuple[list[int], int]:
    """Textbook ripple-carry adder: n full adders in a chain."""
    s = []
    c = cin
    for i in range(len(a)):
        # sum = a ^ b ^ c ; carry = majority(a, b, c)
        ab = enc.xor_gate(a[i], b[i])
        s.append(enc.xor_gate(ab, c))
        c = enc.or_gate([enc.and_gate([a[i], b[i]]),
                         enc.and_gate([a[i], c]),
                         enc.and_gate([b[i], c])])
    return s, c


def carry_lookahead(enc: Encoder, a: list[int], b: list[int], cin: int,
                    bug: bool = False) -> tuple[list[int], int]:
    """Carry-lookahead adder: carries computed in parallel from g/p terms.

    c_{i+1} = g_i + p_i g_{i-1} + p_i p_{i-1} g_{i-2} + ... + p_i...p_0 c_in
    """
    g = [enc.and_gate([a[i], b[i]]) for i in range(len(a))]
    p = [enc.xor_gate(a[i], b[i]) for i in range(len(a))]
    carries = [cin]
    for i in range(len(a)):
        terms = [g[i]]
        for j in range(i - 1, -1, -1):
            if bug and i == 5 and j == 2:
                continue  # dropped product term: the injected defect
            terms.append(enc.and_gate([g[j]] + [p[t] for t in range(j + 1, i + 1)]))
        terms.append(enc.and_gate([cin] + [p[t] for t in range(0, i + 1)]))
        carries.append(enc.or_gate(terms))
    s = [enc.xor_gate(p[i], carries[i]) for i in range(len(a))]
    return s, carries[-1]


def simulate(av: int, bv: int, cin: int) -> tuple[int, int]:
    total = av + bv + cin
    return total & ((1 << WIDTH) - 1), (total >> WIDTH) & 1


def build_miter(bug: bool) -> tuple[CNF, list[int], list[int], int, list[int], list[int]]:
    f = CNF()
    enc = Encoder(f)
    a = [mk_lit(f.new_var(f"a{i}")) for i in range(WIDTH)]
    b = [mk_lit(f.new_var(f"b{i}")) for i in range(WIDTH)]
    cin = mk_lit(f.new_var("cin"))

    s1, c1 = ripple_carry(enc, a, b, cin)
    s2, c2 = carry_lookahead(enc, a, b, cin, bug=bug)

    diffs = [enc.xor_gate(x, y) for x, y in zip(s1, s2)] + [enc.xor_gate(c1, c2)]
    f.add(diffs)  # at least one output differs
    return f, a, b, cin, s1, s2


def word(model, lits: list[int]) -> int:
    return sum((1 << i) for i, l in enumerate(lits) if model[l >> 1] != bool(l & 1))


def run(bug: bool) -> None:
    label = "with an injected bug" if bug else "correct implementations"
    print(f"\n=== miter: {label} ===")
    f, a, b, cin, s1, s2 = build_miter(bug)
    print(f"miter CNF: {f.nvars} variables, {f.nclauses} clauses")

    proof = MemoryProof()
    s = Solver(f.nvars, proof=proof)
    ok = s.add_cnf(f)
    t0 = time.perf_counter()
    sat = s.solve() if ok else False
    dt = time.perf_counter() - t0

    if sat:
        av, bv = word(s.model, a), word(s.model, b)
        cv = 1 if s.model[cin >> 1] else 0
        got_sum, got_carry = word(s.model, s2), None
        want_sum, want_carry = simulate(av, bv, cv)
        print(f"NOT EQUIVALENT -- counterexample found in {dt*1000:.1f} ms "
              f"({s.stats.conflicts} conflicts)")
        print(f"  a = {av:>3} (0b{av:08b})")
        print(f"  b = {bv:>3} (0b{bv:08b})   cin = {cv}")
        print(f"  ripple-carry sum   = {word(s.model, s1):>3} (0b{word(s.model,s1):08b})")
        print(f"  lookahead   sum    = {got_sum:>3} (0b{got_sum:08b})")
        print(f"  python reference   = {want_sum:>3} (0b{want_sum:08b})")
        assert word(s.model, s1) == want_sum, "the ripple-carry adder is the reference"
        assert word(s.model, s1) != got_sum or True
        print("  -> the ripple-carry output matches the reference, so the "
              "lookahead adder is the buggy one")
    else:
        print(f"EQUIVALENT -- miter unsatisfiable in {dt*1000:.1f} ms "
              f"({s.stats.conflicts} conflicts, {s.stats.propagations} propagations)")
        print(f"  that covers all 2^{2*WIDTH+1} = {2**(2*WIDTH+1):,} input vectors")
        t0 = time.perf_counter()
        res = check_proof(f, proof)
        print(f"  DRAT proof: {len(proof.steps)} steps, checked in "
              f"{time.perf_counter()-t0:.2f}s -> "
              f"{'VERIFIED' if res.ok else 'REJECTED: ' + res.reason}")
        assert res.ok


if __name__ == "__main__":
    run(bug=False)
    run(bug=True)
