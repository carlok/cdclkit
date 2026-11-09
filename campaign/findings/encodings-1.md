# encodings-1: Totalizer over no inputs recurses forever

**Proposed severity: Bug.** On the requested grid, at n = 0.

## Minimal case

`at_most_one(f, [], "totalizer")`. It is the empty input list and nothing else. n = 1 passes.

## Reproducer

Run from the repo root.

```python
from dratify.cnf import CNF
from cdclkit.encodings import Encoder, Totalizer, at_most_one, exactly_one

for name, call in (
    ("at_most_one([], 'totalizer')", lambda: at_most_one(CNF(), [], "totalizer")),
    ("exactly_one([], 'totalizer')", lambda: exactly_one(CNF(), [], "totalizer")),
    ("Encoder.amk_totalizer([], 0)", lambda: Encoder(CNF()).amk_totalizer([], 0)),
    ("Totalizer(enc, [])", lambda: Totalizer(Encoder(CNF()), [])),
):
    try:
        call()
        print(name, "ok")
    except RecursionError:
        print(name, "RecursionError")
```

Actual output:

```
at_most_one([], 'totalizer') RecursionError
exactly_one([], 'totalizer') RecursionError
Encoder.amk_totalizer([], 0) RecursionError
Totalizer(enc, []) RecursionError
```

## What it should be

`sum([]) = 0`, so at-most-one of nothing holds and exactly-one of nothing does not. The oracle
agrees on the two formulas the other methods already produce for the same call:

```python
from campaign import oracle
oracle.satisfiable([])    # True: what at_most_one(f, [], m) gives for every other method
oracle.satisfiable([[]])  # False: what exactly_one(f, [], m) gives for every other method
```

The other five methods handle n = 0, and `at_most_k(f, [], 0, "totalizer")` passes only because
`k >= n` returns before the totalizer is built.

## Why this severity

The brief's Bug class is "an encoding has the wrong solutions". A crash is not a wrong solution set,
but one method of six has no answer on a cell of the grid, and it is not a documented limit. A caller
who builds constraints from a list that can come up empty gets it, and only under this method.

## Suspected cause

`cdclkit/encodings.py:609`, `Totalizer._build`. The base case is `len(lits) == 1`, so an empty list
splits into two empty lists without end. `Optimiser.__init__` (`encodings.py:745`) already guards
against this with `if self.counted`, so the hazard was seen in one caller.

Engines: neither. It fails while encoding, before any solver runs. The fix looks clear: return `[]`
for an empty `lits` in `_build`. `at_most_lit` and `at_least_lit` then behave, because `k >= 0` is
vacuous and `k > 0` is false over no inputs.

## Proposed failing test

```python
import unittest
from dratify.cnf import CNF
from cdclkit.encodings import at_most_one, exactly_one
from cdclkit.solver import Solver

class TestTotalizerNoInputs(unittest.TestCase):
    def test_no_inputs_is_a_count_of_zero(self):
        f = CNF()
        at_most_one(f, [], "totalizer")
        self.assertEqual(f.clauses, [])
        g = CNF()
        exactly_one(g, [], "totalizer")
        s = Solver(g.nvars)
        self.assertFalse(s.add_cnf(g) and s.solve())

if __name__ == "__main__":
    unittest.main()
```
