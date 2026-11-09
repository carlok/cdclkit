# encodings-3: at_most_k and exactly_k with k < 0 keep the all-false assignment

**Proposed severity: Bug**, "an encoding has the wrong solutions". Off the requested grid, which stops
at k = 0. All other k in [-2, n + 2] pass for all three functions.

## Minimal case

One input and k = -1, for readability. `at_most_k(f, [], -1)` fails too, with no inputs at all.

## Reproducer

Run from the repo root.

```python
from campaign import dpll
from dratify.cnf import CNF
from dratify.lits import mk_lit, to_dimacs
from cdclkit.encodings import Encoder, at_most_k, exactly_k

for name, call in (
    ("at_most_k(x, -1)", lambda f, x: at_most_k(f, x, -1)),
    ("exactly_k(x, -1)", lambda f, x: exactly_k(f, x, -1)),
    ("amk_sequential(x, -1)", lambda f, x: Encoder(f).amk_sequential(x, -1)),
    ("amk_totalizer(x, -1)", lambda f, x: Encoder(f).amk_totalizer(x, -1)),
):
    f = CNF()
    x = [mk_lit(f.new_var())]
    call(f, x)
    clauses = [[to_dimacs(l) for l in c] for c in f.clauses]
    print(name, sorted(dpll.projected_models(clauses, [1])))
```

Actual output:

```
at_most_k(x, -1) [(False,)]
exactly_k(x, -1) [(False,)]
amk_sequential(x, -1) []
amk_totalizer(x, -1) []
```

## What it should be

No count is at most -1, or equal to -1, so the solution set is empty. The two lower-level methods say
so and the wrapper around them does not. The module has the matching case right on the other side:
`at_least_k` with k > n adds the empty clause, and `at_most_k` with k < 0 is its mirror image. So
`at_least_k(lits, n + 1)` is unsatisfiable, and `at_most_k(~lits, -1)`, which its own docstring calls
equivalent, is not.

In oracle terms, on what the call emits and what it should emit:

```python
from campaign import oracle
oracle.satisfiable([[-1]])  # True:  what at_most_k(x, -1) emits
oracle.satisfiable([[]])    # False: what amk_sequential(x, -1) emits
```

## Why this severity

A negative k comes from arithmetic, such as `at_most_k(lits, budget - used)` when the budget has gone
over. Setting everything false answers "satisfiable" for a problem with no solution. It is off the
grid as asked, so it is the caller's call whether it matters, but the sibling methods show the intent.

## Suspected cause

`cdclkit/encodings.py:470`, `at_most_k`: `if k <= 0` treats k < 0 like k = 0. `exactly_k` inherits it,
since `at_least_k` is vacuous at k <= 0.

Engines: both, since the formula is wrong before a solver sees it. `solve()` and
`solve_adaptive` with either engine answer SAT on `at_most_k(x, -1)`. The fix looks clear: add
`if k < 0: self.add([]); return` ahead of it, as `amk_sequential` does at `encodings.py:440`.

## Proposed failing test

```python
import unittest
from dratify.cnf import CNF
from dratify.lits import mk_lit
from cdclkit.encodings import at_most_k, exactly_k
from cdclkit.solver import Solver

class TestNegativeK(unittest.TestCase):
    def test_no_count_is_at_most_or_equal_to_a_negative_k(self):
        for fn in (at_most_k, exactly_k):
            for n in (0, 1, 3):
                f = CNF()
                xs = [mk_lit(f.new_var()) for _ in range(n)]
                fn(f, xs, -1)
                s = Solver(f.nvars)
                self.assertFalse(s.add_cnf(f) and s.solve(), f"{fn.__name__} n={n}")

if __name__ == "__main__":
    unittest.main()
```
