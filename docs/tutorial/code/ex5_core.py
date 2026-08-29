# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.

"""Why is it unsatisfiable? Ask for the part that matters.

A minimal unsatisfiable subset (MUS) is a subset of the clauses that is still
unsatisfiable, and stops being so if you drop any one of them.
"""
from cdclkit import parse_dimacs, mus

# Clause 4 is irrelevant to the contradiction between 1, 2 and 3.
formula = parse_dimacs("""
p cnf 3 4
 1 0
-1 2 0
-2 0
 3 0
""")

core = mus(formula)
print("clause indices in the minimal unsatisfiable subset:", core)
print("dropping any one of them makes it satisfiable again")
