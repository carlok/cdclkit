# modelling-10: A repeated domain value escapes `is_`

**Proposed severity: Bug.** An encoding with the wrong solutions: `sol[x]` returns a value the model excluded. It needs a repeated
value in the domain, which `int_var` accepts without comment, and which a computed list can contain.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model

m = Model()
x = m.int_var([1, 1, 2], "x")
m.add(x != 1)
print("x != 1 over [1, 1, 2]:", sorted(s[x] for s in m.solutions(project=[x])))

m = Model()
x = m.int_var([1, 1], "x")
print("solutions over [1, 1]:", [s[x] for s in m.solutions(project=[x])])
```

## Actual output

```
x != 1 over [1, 1, 2]: [1, 2]
solutions over [1, 1]: [1, 1]
```

## What it should be

Enumeration over the set {1, 2}: `x != 1` leaves [2]. Projected solutions should be distinct, so [1, 1]
should be [1].

## Suspected cause

`cdclkit/model.py:96` makes a literal per list entry; `is_` at `model.py:103` finds the first through
`domain.index`, and `Solution.__getitem__` at `model.py:182` accepts any.

## Engines

The CNF is wrong, so every engine gives the same answer.

## Fix

Clear. Deduplicate the domain in `IntVar.__init__`, or raise `ValueError`.

## Proposed test

```python
import unittest

from cdclkit.model import Model


class TestRepeatedDomainValues(unittest.TestCase):
    def test_excluding_a_repeated_value_excludes_it(self):
        m = Model()
        try:
            x = m.int_var([1, 1, 2], "x")
        except ValueError:
            return
        m.add(x != 1)
        self.assertEqual(sorted(s[x] for s in m.solutions(project=[x])), [2])
```
