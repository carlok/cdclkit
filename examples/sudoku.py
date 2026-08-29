# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Sudoku as SAT, including a machine-checked uniqueness proof.

The encoding is the standard one-hot: 9*9*9 = 729 booleans, ``x[r][c][v]``
meaning "cell (r,c) holds value v", with exactly-one constraints on cells,
rows, columns and boxes.  That is 324 exactly-one constraints -- and because
the at-most-one part is arc consistent, unit propagation alone reproduces the
"naked single" and "hidden single" rules human solvers use.  Puzzles rated
"easy" are usually solved by propagation with zero decisions; the solver
statistics printed below make that visible.

The second half is the part a hand-written Sudoku solver rarely does: after
finding a solution, add its negation as a clause and solve again.  If that is
UNSAT, the puzzle has exactly one solution -- and the DRAT proof of that UNSAT
is checked here, so "unique" is certified rather than asserted.

Run:  python3 examples/sudoku.py
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

N = 9
BOX = 3

# "Platinum Blonde", one of the hardest known 17-clue-ish puzzles for
# propagation-based solvers, plus a gentle one for contrast.
HARD = (
    "000000012"
    "000000003"
    "002300400"
    "001800005"
    "060070800"
    "000009000"
    "008500000"
    "900040500"
    "470006000"
)
EASY = (
    "530070000"
    "600195000"
    "098000060"
    "800060003"
    "400803001"
    "700020006"
    "060000280"
    "000419005"
    "000080079"
)


def build(puzzle: str) -> tuple[CNF, list[list[list[int]]]]:
    f = CNF()
    x = [[[mk_lit(f.new_var(f"r{r}c{c}v{v+1}")) for v in range(N)] for c in range(N)]
         for r in range(N)]
    enc = Encoder(f)

    for r in range(N):
        for c in range(N):
            enc.exactly_one(x[r][c])            # every cell holds one value
    for r in range(N):
        for v in range(N):
            enc.exactly_one([x[r][c][v] for c in range(N)])   # rows
    for c in range(N):
        for v in range(N):
            enc.exactly_one([x[r][c][v] for r in range(N)])   # columns
    for br in range(0, N, BOX):
        for bc in range(0, N, BOX):
            for v in range(N):
                enc.exactly_one(
                    [x[br + i][bc + j][v] for i in range(BOX) for j in range(BOX)]
                )
    for i, ch in enumerate(puzzle):
        if ch.isdigit() and ch != "0":
            r, c, v = i // N, i % N, int(ch) - 1
            f.add([x[r][c][v]])
    return f, x


def read_grid(model, x) -> list[list[int]]:
    grid = []
    for r in range(N):
        row = []
        for c in range(N):
            row.append(next(v + 1 for v in range(N) if model[x[r][c][v] >> 1]))
        grid.append(row)
    return grid


def show(grid) -> str:
    out = []
    for r, row in enumerate(grid):
        if r and r % BOX == 0:
            out.append("------+-------+------")
        cells = " ".join(
            ("|" if c and c % BOX == 0 else "") + str(v) for c, v in enumerate(row)
        )
        out.append(cells.replace("|", "| "))
    return "\n".join(out)


def solve_puzzle(name: str, puzzle: str) -> None:
    print(f"\n=== {name} ===")
    f, x = build(puzzle)
    print(f"encoding: {f.nvars} variables, {f.nclauses} clauses")

    s = Solver(f.nvars)
    s.add_cnf(f)
    t0 = time.perf_counter()
    if not s.solve():
        print("no solution")
        return
    dt = time.perf_counter() - t0
    grid = read_grid(s.model, x)
    print(show(grid))
    print(
        f"solved in {dt*1000:.1f} ms  "
        f"[{s.stats.decisions} decisions, {s.stats.conflicts} conflicts, "
        f"{s.stats.propagations} propagations]"
    )
    if s.stats.decisions == 0:
        print("-> solved by unit propagation alone: the encoding's arc consistency "
              "reproduces every 'single' the puzzle needed")

    # rows must be a permutation, so the answer is a valid Latin square
    assert all(sorted(row) == list(range(1, 10)) for row in grid)
    assert all(sorted(col) == list(range(1, 10)) for col in zip(*grid))

    # -- uniqueness, with a checked proof
    proof = MemoryProof()
    s2 = Solver(f.nvars, proof=proof)
    s2.add_cnf(f)
    block = [neg(x[r][c][grid[r][c] - 1]) for r in range(N) for c in range(N)]
    f2 = f.copy()
    f2.add(block)
    s2.add_clause(block)
    t0 = time.perf_counter()
    second = s2.solve()
    dt = time.perf_counter() - t0
    if second:
        print("the puzzle has at least two solutions")
        return
    res = check_proof(f2, proof)
    print(
        f"uniqueness: no second solution ({dt*1000:.1f} ms, "
        f"{s2.stats.conflicts} conflicts); DRAT proof of {len(proof.steps)} steps "
        f"-> {'VERIFIED' if res.ok else 'REJECTED: ' + res.reason}"
    )


if __name__ == "__main__":
    solve_puzzle("easy", EASY)
    solve_puzzle("hard (Platinum Blonde family)", HARD)
