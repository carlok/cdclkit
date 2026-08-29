"""Smallest possible: write a formula by hand, ask whether it can be satisfied."""
from cdclkit import parse_dimacs, solve

# (a OR b) AND (NOT a OR b) AND (a OR NOT b)
# DIMACS: variables are 1, 2, ...; a negative number is a negated variable;
# each clause ends with 0.
text = """
p cnf 2 3
 1  2 0
-1  2 0
 1 -2 0
"""

formula = parse_dimacs(text)
print("variables:", formula.nvars, " clauses:", len(formula.clauses))

sat, model = solve(formula)
print("satisfiable:", sat)
if sat:
    # model is indexed by variable number - 1
    print("a =", model[0], " b =", model[1])
