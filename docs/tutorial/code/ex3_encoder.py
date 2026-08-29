# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.

"""Constraints people actually have, without writing clauses by hand.

Colour a triangle with 2 colours. Each node needs exactly one colour, and
adjacent nodes must differ. A triangle needs 3 colours, so this is UNSAT.
"""
from cdclkit import CNF, Encoder, solve, neg

for n_colours in (2, 3):
    f = CNF()
    enc = Encoder(f)

    nodes = ["x", "y", "z"]
    edges = [("x", "y"), ("y", "z"), ("x", "z")]

    # colour[node][c] is true when `node` has colour c
    colour = {n: [enc.new_lit() for _ in range(n_colours)] for n in nodes}

    for n in nodes:
        enc.exactly_one(colour[n])          # one colour per node
    for a, b in edges:
        for c in range(n_colours):          # never the same colour on an edge
            # note neg(), not -x: internal literals are non-negative
            enc.add([neg(colour[a][c]), neg(colour[b][c])])

    sat, model = solve(f)
    print(f"{n_colours} colours: {'SAT' if sat else 'UNSAT'}"
          f"   ({f.nvars} vars, {len(f.clauses)} clauses)")
