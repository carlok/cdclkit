# modelling-8: `at_most_k` and `exactly_k` accept k < 0 as k = 0

**Proposed severity: Bug.** An encoding with the wrong solutions. A sum of booleans cannot be negative, so both are unsatisfiable,
and `amk_sequential` already says so. Reachable only by passing a negative k, which a computed bound can
do.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model

for method in ("auto", "sequential", "totalizer"):
    m = Model()
    x = m.bool_var("x")
    m.at_most_k([x], -1, method=method)
    n = Model()
    y = n.bool_var("y")
    n.exactly_k([y], -1, method=method)
    print(method, "at_most_k -1 SAT:", m.solve() is not None, "| exactly_k -1 SAT:", n.solve() is not None)
```

## Actual output

```
auto at_most_k -1 SAT: True | exactly_k -1 SAT: True
sequential at_most_k -1 SAT: True | exactly_k -1 SAT: True
totalizer at_most_k -1 SAT: True | exactly_k -1 SAT: True
```

## What it should be

Enumeration: no assignment has `sum <= -1` or `sum == -1`, so both must be None.

## Suspected cause

`cdclkit/encodings.py:470`: `if k <= 0:` forces every literal false, which is right only for k = 0.
`amk_sequential` (`encodings.py:440`) handles k < 0 with an empty clause, and `at_most_k` never lets it
get there.

## Engines

The CNF is wrong, so every engine gives the same answer.

## Fix

Clear. In `at_most_k`, add the empty clause when k < 0, before the k >= n test, so `n = 0` is covered.
`exactly_k` then follows. Overlaps the encodings corner, which should be checked for a duplicate.

## Proposed test

```python
import unittest

from cdclkit.model import Model


class TestNegativeK(unittest.TestCase):
    def test_at_most_negative_is_unsat(self):
        for method in ("auto", "sequential", "totalizer"):
            m = Model()
            m.at_most_k([m.bool_var("x")], -1, method=method)
            self.assertIsNone(m.solve(), method)

    def test_exactly_negative_is_unsat(self):
        for method in ("auto", "sequential", "totalizer"):
            m = Model()
            m.exactly_k([m.bool_var("x")], -1, method=method)
            self.assertIsNone(m.solve(), method)

    def test_at_most_negative_over_nothing_is_unsat(self):
        m = Model()
        m.at_most_k([], -1)
        self.assertIsNone(m.solve())
```
