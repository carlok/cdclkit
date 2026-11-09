# modelling-4: pyeq accepts `range` calls Python rejects

**Proposed severity: Critical.** Wrong `proved=True` with a replayed proof: `f` raises TypeError on every input and is proved equal
to a function that does not. The brief's rule makes this Critical. In practice it needs a program that
cannot ever have run, so it should be fixed after modelling-1 to 3.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.pyeq import UnsupportedConstruct, equivalent

def identity(x): return x
def plus_one(x): return x + 1

def no_args(x):
    for i in range():
        x = x + 1
    return x

def keyword(x):
    for i in range(stop=3):
        x = x + 1
    return x

def shadowed(x):
    range = 7
    for i in range(1):
        x = x + 1
    return x

for engine in ("python", "native"):
    print(engine, equivalent(no_args, identity, {"x": 3}, engine=engine).proved,
          equivalent(keyword, identity, {"x": 3}, engine=engine).proved,
          equivalent(shadowed, plus_one, {"x": 3}, engine=engine).proved)
for fn in (no_args, keyword, shadowed):
    try:
        fn(1)
    except TypeError as e:
        print(fn.__name__, "raises TypeError:", e)
```

## Actual output

```
python True True True
native True True True
no_args raises TypeError: range expected at least 1 argument, got 0
keyword raises TypeError: range() takes no keyword arguments
shadowed raises TypeError: 'int' object is not callable
```

## What it should be

All three raise TypeError in Python on every input, so `proved` must not be True.

## Suspected cause

`cdclkit/pyeq.py:469-479`: `unroll_for` reads only `call.args`, ignores `call.keywords`, turns no
arguments into `range(0)` by `rng = range(*args) if args else range(0)`, and checks the name `range`
without looking at `self.env`.

## Engines

Both: the front end is shared.

## Fix

Clear. Require 1 to 3 positional arguments and no keywords, and reject when `range` is bound in
`env`. `range(1, 2, 0)` is worth checking at the same spot: it reaches `range(*args)` and raises a bare
ValueError from the compiler.

## Proposed test

```python
import unittest

from cdclkit.pyeq import UnsupportedConstruct, equivalent


def identity(x): return x


class TestRangeShape(unittest.TestCase):
    def test_range_with_no_arguments(self):
        def f(x):
            for i in range():
                x = x + 1
            return x
        with self.assertRaises(UnsupportedConstruct):
            equivalent(f, identity, {"x": 3})

    def test_range_with_a_keyword(self):
        def f(x):
            for i in range(stop=3):
                x = x + 1
            return x
        with self.assertRaises(UnsupportedConstruct):
            equivalent(f, identity, {"x": 3})

    def test_shadowed_range(self):
        def f(x):
            range = 7
            for i in range(1):
                x = x + 1
            return x
        def g(x): return x + 1
        with self.assertRaises(UnsupportedConstruct):
            equivalent(f, g, {"x": 3})
```
