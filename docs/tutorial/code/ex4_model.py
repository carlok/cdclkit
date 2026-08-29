"""The modelling layer: integers and all-different, no clauses in sight.

A 4x4 Sudoku. Each cell holds 1..4; rows, columns and 2x2 boxes are
all-different.
"""
from cdclkit.model import Model

PUZZLE = [
    [1, 0, 0, 0],
    [0, 0, 3, 0],
    [0, 4, 0, 0],
    [0, 0, 0, 2],
]

m = Model()
cell = [[m.int_var(range(1, 5), f"c{r}{c}") for c in range(4)] for r in range(4)]

for r in range(4):
    m.all_different(cell[r])                                  # rows
for c in range(4):
    m.all_different([cell[r][c] for r in range(4)])           # columns
for br in (0, 2):
    for bc in (0, 2):                                         # 2x2 boxes
        m.all_different([cell[br + i][bc + j] for i in range(2) for j in range(2)])

for r in range(4):
    for c in range(4):
        if PUZZLE[r][c]:
            m.add(cell[r][c] == PUZZLE[r][c])                 # the givens

sol = m.solve()
print("solved:", sol is not None)
for r in range(4):
    print("   ", " ".join(str(sol.value(cell[r][c])) for c in range(4)))
