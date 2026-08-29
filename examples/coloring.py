# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Chromatic number by SAT, with a machine-checked proof of optimality.

Graph colouring is the standard demonstration of the difference between
"finding" and "proving": a 4-colouring of a graph is a witness anyone can check
in linear time, but "this graph needs 4 colours" is a statement about all
3-colourings, of which there may be none to point at.  SAT gives both sides:
solve for k colours (SAT, here is the colouring) and for k-1 (UNSAT, here is
the DRAT proof).

The instances are **Mycielskians**.  Mycielski's construction takes a
triangle-free graph with chromatic number k and produces a triangle-free graph
with chromatic number k+1, which is how you get graphs that need many colours
without containing a big clique -- exactly the graphs where greedy colouring
heuristics fail and where the lower bound genuinely has to be proved.  M(2)=K2,
M(3)=C5, M(4) is the 11-vertex Grötzsch graph, M(5) has 23 vertices.

Symmetry breaking: colours are interchangeable, so every colouring has k!
relabellings and a naive encoding wastes its life re-proving the same thing.
Fixing the colour of the first vertex, and forcing vertex i to use only colours
1..i+1, removes that symmetry.  The script reports the cost with and without it.

Run:  python3 examples/coloring.py
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


def mycielski(k: int) -> tuple[int, list[tuple[int, int]]]:
    """Return (n, edges) for the k-th Mycielskian; chromatic number is k."""
    n, edges = 2, [(0, 1)]  # K2, chi = 2
    for _ in range(k - 2):
        m = n
        new_edges = list(edges)
        # u_i copies v_i's neighbourhood; w connects to every u_i
        for (a, b) in edges:
            new_edges.append((a, m + b))
            new_edges.append((b, m + a))
        for i in range(n):
            new_edges.append((m + i, 2 * m))
        n, edges = 2 * m + 1, new_edges
    return n, edges


def build(n: int, edges, k: int, symmetry: bool) -> tuple[CNF, list[list[int]]]:
    f = CNF()
    enc = Encoder(f)
    x = [[mk_lit(f.new_var(f"v{v}c{c}")) for c in range(k)] for v in range(n)]
    for v in range(n):
        enc.exactly_one(x[v])
    for (a, b) in edges:
        for c in range(k):
            f.add([neg(x[a][c]), neg(x[b][c])])
    if symmetry:
        # vertex v may only use colours 0..v  (precolouring the first clique
        # would be stronger, but this works for any graph and is enough to
        # kill the k! factor)
        for v in range(min(n, k)):
            for c in range(v + 1, k):
                f.add([neg(x[v][c])])
    return f, x


def try_k(n, edges, k, symmetry=True, want_proof=False):
    f, x = build(n, edges, k, symmetry)
    proof = MemoryProof() if want_proof else None
    s = Solver(f.nvars, proof=proof)
    ok = s.add_cnf(f)
    t0 = time.perf_counter()
    sat = s.solve() if ok else False
    dt = time.perf_counter() - t0
    colouring = None
    if sat:
        colouring = [next(c for c in range(k) if s.model[x[v][c] >> 1]) for v in range(n)]
        for (a, b) in edges:
            assert colouring[a] != colouring[b], "the model is not a proper colouring"
    return sat, colouring, dt, s.stats, f, proof


def main() -> None:
    for k in (3, 4, 5):
        n, edges = mycielski(k)
        print(f"\n=== Mycielskian M({k}): {n} vertices, {len(edges)} edges "
              f"(triangle-free, chi = {k}) ===")
        chi = None
        for trial_k in range(2, k + 2):
            sat, colouring, dt, stats, f, _ = try_k(n, edges, trial_k)
            verdict = "colourable" if sat else "impossible"
            print(f"  {trial_k} colours: {verdict:<12} "
                  f"{dt*1000:>8.1f} ms  {stats.conflicts:>7} conflicts")
            if sat:
                chi = trial_k
                print(f"    colouring: {colouring}")
                break
        assert chi == k, f"expected chromatic number {k}, got {chi}"

        # prove the lower bound with a checked certificate
        sat, _, dt, stats, f, proof = try_k(n, edges, k - 1, want_proof=True)
        assert not sat
        res = check_proof(f, proof)
        print(f"  lower bound: {k-1} colours is UNSAT, DRAT proof of "
              f"{len(proof.steps)} steps -> "
              f"{'VERIFIED' if res.ok else 'REJECTED: ' + res.reason}")
        assert res.ok

        # what symmetry breaking is worth
        sat_a, _, dt_a, st_a, _, _ = try_k(n, edges, k - 1, symmetry=True)
        sat_b, _, dt_b, st_b, _, _ = try_k(n, edges, k - 1, symmetry=False)
        assert not sat_a and not sat_b
        print(f"  symmetry breaking on the {k-1}-colour refutation: "
              f"{st_a.conflicts} vs {st_b.conflicts} conflicts "
              f"({dt_a*1000:.1f} ms vs {dt_b*1000:.1f} ms)")


if __name__ == "__main__":
    main()
