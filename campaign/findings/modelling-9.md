# modelling-9: `IntVar.ge` and `le` assume a sorted domain

**Proposed severity: Bug.** An encoding with the wrong solutions in both directions: a value is let through and a value is lost.
`int_var` takes any iterable, nothing says it must be sorted, and without `ge`/`le` an unsorted domain
works.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model

def values(domain, build):
    m = Model()
    x = m.int_var(domain, "x")
    m.add(build(x))
    return sorted(s[x] for s in m.solutions(project=[x]))

print("ge(2) on [2, 1]:", values([2, 1], lambda x: x.ge(2)))
print("le(1) on [2, 1]:", values([2, 1], lambda x: x.le(1)))
print("ge(2) on [1, 2]:", values([1, 2], lambda x: x.ge(2)))
print("le(1) on [1, 2]:", values([1, 2], lambda x: x.le(1)))
```

## Actual output

```
ge(2) on [2, 1]: [1, 2]
le(1) on [2, 1]: []
ge(2) on [1, 2]: [2]
le(1) on [1, 2]: [1]
```

## What it should be

Enumeration: `x >= 2` over {1, 2} is [2], and `x <= 1` is [1], whatever order the domain was given in.

## Suspected cause

`cdclkit/model.py:128-155`: the ladder is built in list order, and `ge` returns the first position with
`v >= value`, which only means "x >= value" if the list ascends.

## Engines

The CNF is wrong, so every engine gives the same answer.

## Fix

Clear. Sort `self.domain` in `IntVar.__init__`, keeping `lits` aligned, or raise on an unsorted domain.

## Proposed test

```python
import unittest

from cdclkit.model import Model


def values(domain, build):
    m = Model()
    x = m.int_var(domain, "x")
    m.add(build(x))
    return sorted(s[x] for s in m.solutions(project=[x]))


class TestUnsortedDomains(unittest.TestCase):
    def test_ge_does_not_depend_on_domain_order(self):
        self.assertEqual(values([2, 1], lambda x: x.ge(2)), [2])

    def test_le_does_not_depend_on_domain_order(self):
        self.assertEqual(values([2, 1], lambda x: x.le(1)), [1])
```
