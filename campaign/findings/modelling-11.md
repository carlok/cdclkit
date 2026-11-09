# modelling-11: `at_most_one([])` and `exactly_one([])` overflow the stack under the totalizer

**Proposed severity: Bug.** A crash on valid input, with no wrong answer. The other five methods take the empty list, and
`at_most_k([], 0, method="totalizer")` returns early. A computed list can be empty.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model

for name in ("at_most_one", "exactly_one"):
    m = Model()
    try:
        getattr(m, name)([], method="totalizer")
        print(name, "ok")
    except RecursionError as e:
        print(name, "RecursionError:", e)
m = Model()
m.at_most_one([], method="pairwise")
print("pairwise ok, SAT:", m.solve() is not None)
```

## Actual output

```
at_most_one RecursionError: maximum recursion depth exceeded
exactly_one RecursionError: maximum recursion depth exceeded
pairwise ok, SAT: True
```

## What it should be

`at_most_one([])` is trivially true, `exactly_one([])` is unsatisfiable. Neither should raise.

## Suspected cause

`cdclkit/encodings.py:609-615`: `Totalizer._build` has a base case for one literal only, and for an empty
list it recurses on `lits[:0]` forever. `at_most_one` at `encodings.py:415-416` calls `amk_totalizer` with no
guard. `at_most_k` has one at `encodings.py:468`.

## Engines

Python only: this is in the Encoder, which is Python on both paths.

## Fix

Clear. Return `[]` from `_build` for an empty list. Overlaps the encodings corner, which should be
checked for a duplicate.

## Proposed test

```python
import unittest

from cdclkit.model import Model


class TestEmptyTotalizer(unittest.TestCase):
    def test_at_most_one_of_nothing_holds(self):
        m = Model()
        m.at_most_one([], method="totalizer")
        self.assertIsNotNone(m.solve())

    def test_exactly_one_of_nothing_is_unsat(self):
        m = Model()
        m.exactly_one([], method="totalizer")
        self.assertIsNone(m.solve())
```
