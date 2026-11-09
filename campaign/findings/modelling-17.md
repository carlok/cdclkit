# modelling-17: pyeq takes widths of 0 and below, and any engine name

**Proposed severity: Note.** Neither is a wrong claim that matters. At 0 bits all values coincide, so `proved=True` is vacuous, and -1 is
meaningless rather than false. An unknown engine name still answers correctly, on Python. Both are unvalidated
input, and the second is the silent downgrade the `equivalent` docstring warns against.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.pyeq import UnsupportedConstruct, equivalent

def f(a): return a + 1
def g(a): return a

for w in (0, -1):
    r = equivalent(f, g, {"a": w})
    print(w, r.proved, r.report().split(",")[0])
r = equivalent(f, g, {"a": 3}, engine="nativ")
print("engine='nativ':", r.proved, r.counterexample)
```

## Actual output

```
0 True c equivalent at 0 bits
-1 True c equivalent at -1 bits
engine='nativ': False {'a': 0}
```

## What it should be

A width below 1 is not a two's-complement integer, and `compile_function` already raises on a missing width.
The `equivalent` docstring describes a silent engine downgrade as what made an earlier test compare Python with
Python.

## Suspected cause

`cdclkit/pyeq.py:576-581` does not validate widths, so the miter clause is empty and the formula trivially
UNSAT. `cdclkit/pyeq.py:700-707` treats any string other than "native" and "auto" as Python.

## Engines

Both: the front end is shared.

## Fix

Clear. Raise on `widths[n] < 1`, and raise on an unknown engine.

## Proposed test

```python
import unittest

from cdclkit.pyeq import UnsupportedConstruct, equivalent


def f(a): return a + 1
def g(a): return a


class TestInputValidation(unittest.TestCase):
    def test_a_width_below_one_is_refused(self):
        for w in (0, -1):
            with self.assertRaises((UnsupportedConstruct, ValueError)):
                equivalent(f, g, {"a": w})

    def test_an_unknown_engine_is_refused(self):
        with self.assertRaises((UnsupportedConstruct, ValueError)):
            equivalent(f, g, {"a": 3}, engine="nativ")
```
