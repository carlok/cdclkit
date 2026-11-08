# modelling-15: `Model.solutions()` without `project` repeats solutions

**Proposed severity: Note.** The set of solutions is right and only the count is off, so no solution is wrong. It contradicts the
docstring's "distinct" only if distinct is read at the level of the user's variables. `Solver.enumerate_models`
explains the effect, which is why this is a Note.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model

m = Model()
xs = m.bool_vars(3)
m.at_most_k(xs, 2, method="sequential")
found = [tuple(s[x] for x in xs) for s in m.solutions()]
print("yielded", len(found), "| distinct on the user's variables", len(set(found)))
```

## Actual output

```
yielded 17 | distinct on the user's variables 7
```

## What it should be

Enumeration gives 7 solutions. `Solver.enumerate_models` says projection is how to avoid "counting the
different internal states of its Tseitin variables"; `Model.solutions` says "distinct solutions, optionally
projected".

## Suspected cause

`cdclkit/model.py:327-336`: with `project=None`, blocking covers every variable, auxiliary ones included.

## Engines

Python only: `Model` has no engine parameter.

## Fix

A choice. Default the projection to the variables the user created, which needs the Model to record them, or
say in the docstring that `project` is needed to count.

## Proposed test

This fails today, and it applies only if the projection default is what gets chosen.

```python
import unittest

from cdclkit.model import Model


class TestUnprojectedSolutions(unittest.TestCase):
    def test_default_enumeration_counts_the_users_solutions(self):
        m = Model()
        xs = m.bool_vars(3)
        m.at_most_k(xs, 2, method="sequential")
        found = [tuple(s[x] for x in xs) for s in m.solutions()]
        self.assertEqual(len(found), len(set(found)))
```
