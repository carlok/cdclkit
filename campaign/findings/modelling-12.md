# modelling-12: pyeq reports a width the circuit does not have

**Proposed severity: Bug.** `proved=True` is right at the width the circuit really used, and wrong at the width the result states:
"equivalent at 8 bits" for functions that differ with 8-bit arithmetic. Proposed as a Bug, not Critical,
because no claim is wrong once the report is corrected. If the reported width is taken as the claim, as the
brief's "in the bit width it claims" could be read, it is a wrong `proved=True`. The orchestrator should
decide. `equivalent` also never says that it compiled a no-parameter function at 8 bits.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.pyeq import UnsupportedConstruct, equivalent

def f(a): return a * 16
def g(a): return 0

r = equivalent(f, g, {"a": 4, "unused": 8})
print(r.proved, r.width, r.report().split(",")[0])
print("a=1 at 8-bit arithmetic:", 1 * 16, "vs 0")

def c(): return 300
def d(): return 44

r = equivalent(c, d, {})
print(r.proved, r.width, r.report().split(",")[0])
```

## Actual output

```
True 8 c equivalent at 8 bits
a=1 at 8-bit arithmetic: 16 vs 0
True 0 c equivalent at 0 bits
```

## What it should be

The first circuit is 4 bits, where `a * 16` wraps to 0. At the 8 bits it reports, `a=1` gives 16 against 0.
The second is compiled at 8 bits, where 300 wraps to 44; it reports 0 bits. `r.width` should say what the
circuit used, and a key naming no parameter should be an error, as a missing one already is.

## Suspected cause

`cdclkit/pyeq.py:801` computes `r.width` from all of `widths`; `pyeq.py:576` computes the circuit's from
the parameters, with 8 when there are none.

## Engines

Both: the front end is shared.

## Fix

Clear. Set `r.width` from the same expression as `compile_function`, and raise `UnsupportedConstruct` on
a key in `widths` that names no parameter.

## Proposed test

```python
import unittest

from cdclkit.pyeq import UnsupportedConstruct, equivalent


class TestWidthClaim(unittest.TestCase):
    def test_an_unused_key_does_not_change_the_claim(self):
        def f(a): return a * 16
        def g(a): return 0
        try:
            r = equivalent(f, g, {"a": 4, "unused": 8})
        except UnsupportedConstruct:
            return
        self.assertEqual(r.width, 4)

    def test_no_parameters_reports_the_width_used(self):
        def f(): return 300
        def g(): return 44
        r = equivalent(f, g, {})
        self.assertEqual(r.width, 8)
```
