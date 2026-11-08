# modelling-13: pyeq crashes on a counterexample for positional-only parameters

**Proposed severity: Bug.** A crash with a bare TypeError, no wrong answer. Reading such a parameter is rejected with a misleading
"used before assignment", and when it is not read the functions can be proved correctly. The only failure
is the crash; the comment at the site says a TypeError here "is a bug here".

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.pyeq import UnsupportedConstruct, equivalent

def f(a, /, b): return b
def g(a, /, b): return b + 1

try:
    print(equivalent(f, g, {"b": 3}).proved)
except TypeError as e:
    print("TypeError:", e)
```

## Actual output

```
TypeError: f() missing 1 required positional argument: 'a'
```

## What it should be

`f` and `g` differ on every input, so the answer is `proved=False` with a counterexample, or
`UnsupportedConstruct` if positional-only parameters stay outside the subset.

## Suspected cause

`cdclkit/pyeq.py:534` and `pyeq.py:569` read `tree.args.args`, which leaves out `posonlyargs`.
`pyeq.py:861` then calls `f(**r.counterexample)`, and `pyeq.py:864` deliberately does not catch TypeError.

## Engines

Both: the front end is shared.

## Fix

Clear. Raise `UnsupportedConstruct` in `compile_function` on `tree.args.posonlyargs`.

## Proposed test

```python
import unittest

from cdclkit.pyeq import UnsupportedConstruct, equivalent


class TestPositionalOnly(unittest.TestCase):
    def test_positional_only_is_rejected_or_modelled(self):
        def f(a, /, b): return b
        def g(a, /, b): return b + 1
        try:
            r = equivalent(f, g, {"a": 3, "b": 3})
        except UnsupportedConstruct:
            return
        self.assertIs(r.proved, False)
```
