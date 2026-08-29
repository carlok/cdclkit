# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.

"""An unsatisfiable formula, and the proof that it is."""
from cdclkit import parse_dimacs, solve, MemoryProof
import dratify

# All four combinations of two variables are forbidden, so nothing is left.
formula = parse_dimacs("""
p cnf 2 4
 1  2 0
 1 -2 0
-1  2 0
-1 -2 0
""")

proof = MemoryProof()
sat, model = solve(formula, proof=proof)
print("satisfiable:", sat)
print("proof steps:", proof.n_add, "additions,", proof.n_del, "deletions")

result = dratify.check_proof(formula, proof)
print("proof verified by an independent checker:", result.ok)
print("empty clause derived:", result.reached_empty)
