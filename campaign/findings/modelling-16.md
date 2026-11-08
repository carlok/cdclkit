# modelling-16: `differential_solve` can compare a CNF with itself

**Proposed severity: Note.** No wrong answer: agreement is reported truthfully. What is overstated is what it means. The attribute's
comment says it "overrides the method argument of every cardinality constraint", which is true, and the
`_method` docstring accepts that a run varies only what the method applies to. But a model built from
`all_different`, the module's headline constraint, varies nothing, and the check passes with no information.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model

def build(m):
    m.all_different(m.int_vars(3, range(3)))

a, b = Model(encoding_method="pairwise"), Model(encoding_method="commander")
build(a)
build(b)
print("all_different, same CNF:", a.cnf.clauses == b.cnf.clauses)

def build2(m):
    xs = m.bool_vars(5)
    m.sum_leq([1] * 5, xs, 2)
    m.parity(xs)

a, b = Model(encoding_method="sequential"), Model(encoding_method="totalizer")
build2(a)
build2(b)
print("sum_leq and parity, same CNF:", a.cnf.clauses == b.cnf.clauses)
```

## Actual output

```
all_different, same CNF: True
sum_leq and parity, same CNF: True
```

## What it should be

`differential_solve`'s docstring: "Encoding a cardinality constraint two ways and requiring the same answer is
the cheapest available check on the one remaining unverified translation."  The generator counts how often this
happens as `note_differential_same_cnf`.

## Suspected cause

`cdclkit/model.py:267-270`: `all_different` calls `enc.at_most_one(lits)` without `_method`.

## Engines

Python only: `Model` has no engine parameter.

## Fix

Clear for `all_different`: route it through `_method`. `differential_solve` could also raise or warn when the
two CNFs are identical.

## Proposed test

```python
import unittest

from cdclkit.model import Model


class TestDifferentialVaries(unittest.TestCase):
    def test_all_different_follows_the_override(self):
        def build(m):
            m.all_different(m.int_vars(3, range(3)))
        a, b = Model(encoding_method="pairwise"), Model(encoding_method="commander")
        build(a)
        build(b)
        self.assertNotEqual(a.cnf.clauses, b.cnf.clauses)
```
