# encodings-6: An Optimiser with no soft literals ignores a negative bound

**Proposed severity: Note.** It has no effect on `optimise()`, or on any bound of zero or more. It does
not fit the brief's Bug list, and it is filed so that the run's label explains the mismatch.

## Minimal case

An empty solver and no soft literals.

## Reproducer

Run from the repo root.

```python
from cdclkit.encodings import Optimiser
from cdclkit.solver import Solver

opt = Optimiser(Solver(), [])
print("solve_with_bound(-1):", opt.solve_with_bound(-1))
print("run(target=-1):", opt.run(target=-1))
```

Actual output:

```
solve_with_bound(-1): []
run(target=-1): (0, [])
```

## What it should be

`solve_with_bound`'s docstring says "Solve demanding `count <= bound`. Returns a model or None". The
count is 0, and 0 <= -1 is false, so both should answer None. With one soft literal or more, the same
calls do, because `at_most_lit` returns `false_lit`.

## Suspected cause

`cdclkit/encodings.py:757`: `if bound is not None and self.totalizer is not None`, and with no soft
literals `totalizer` is None, so the bound is dropped.

Engines: Python only, as `Optimiser` asserts a Python `Solver`. The fix looks clear: return None when
`bound < 0` and there is no totalizer.

## Proposed failing test

```python
import unittest
from cdclkit.encodings import Optimiser
from cdclkit.solver import Solver

class TestOptimiserNoSoftLiterals(unittest.TestCase):
    def test_a_negative_bound_is_unsatisfiable(self):
        opt = Optimiser(Solver(), [])
        self.assertIsNone(opt.solve_with_bound(-1))
        self.assertIsNone(Optimiser(Solver(), []).run(target=-1))

if __name__ == "__main__":
    unittest.main()
```
