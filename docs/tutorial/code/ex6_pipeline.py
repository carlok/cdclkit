# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.

"""One problem, end to end, showing every intermediate.

Three exams. Some students are enrolled in both Algebra and Biology, some in
both Biology and Chemistry, some in both Algebra and Chemistry. An exam pair
with a shared student cannot go in the same slot.

Two slots is impossible. Three works. We do both, and write out the files that
pass between the stages.
"""
import pathlib
from cdclkit import CNF, Encoder, solve, neg, write_dimacs, MemoryProof
import dratify

EXAMS = ["Algebra", "Biology", "Chemistry"]
CLASHES = [("Algebra", "Biology"), ("Biology", "Chemistry"), ("Algebra", "Chemistry")]
OUT = pathlib.Path(__file__).resolve().parent.parent / "build"
OUT.mkdir(exist_ok=True)


def build(n_slots):
    """Encode the timetable. Returns (formula, variable map)."""
    f = CNF()
    enc = Encoder(f)
    # x[e][s] is true when exam e sits in slot s
    x = {e: [enc.new_lit() for _ in range(n_slots)] for e in EXAMS}

    for e in EXAMS:
        enc.exactly_one(x[e])                     # every exam gets one slot
    for a, b in CLASHES:
        for s in range(n_slots):                  # clashing exams differ
            enc.add([neg(x[a][s]), neg(x[b][s])])
    return f, x


# ---------------------------------------------------------------- two slots
f2, _ = build(2)
proof = MemoryProof()
sat2, _ = solve(f2, proof=proof)

with open(OUT / "timetable2.cnf", "w") as fh:
    write_dimacs(f2, fh)
(OUT / "timetable2.drat").write_text(proof.to_text())

print(f"2 slots: {'SAT' if sat2 else 'UNSAT'}"
      f"  ({f2.nvars} vars, {len(f2.clauses)} clauses)")
print(f"  proof: {proof.n_add} additions, {proof.n_del} deletions")
print(f"  checked: {dratify.check_proof(f2, proof).ok}")
print(f"  wrote build/timetable2.cnf and build/timetable2.drat")

# -------------------------------------------------------------- three slots
f3, x3 = build(3)
sat3, model = solve(f3)
print()
print(f"3 slots: {'SAT' if sat3 else 'UNSAT'}"
      f"  ({f3.nvars} vars, {len(f3.clauses)} clauses)")
for e in EXAMS:
    slot = next(s for s in range(3) if model[x3[e][s] >> 1])
    print(f"  {e:<10} -> slot {slot + 1}")
