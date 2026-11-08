# modelling-3: pyeq ignores decorators

**Proposed severity: Critical.** Wrong `proved=True` with a replayed proof, on a function returning twice the other's value. A
wrapper written with `functools.wraps`, which is the usual way, sets `__wrapped__`, and `inspect`
follows it to the undecorated source.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.pyeq import UnsupportedConstruct, equivalent
import functools


def double(fn):
    @functools.wraps(fn)
    def wrapper(x):
        return fn(x) * 2
    return wrapper


@double
def f(x): return x

def g(x): return x

for engine in ("python", "native"):
    print(engine, equivalent(f, g, {"x": 3}, engine=engine).proved)
print("f(1) =", f(1), " g(1) =", g(1))
```

## Actual output

```
python True
native True
f(1) = 2  g(1) = 1
```

## What it should be

`f(1)` is 2 and `g(1)` is 1, so `proved` must not be True. `UnsupportedConstruct` is the expected
outcome, since the decorator's body is not visible to the compiler.

## Suspected cause

`cdclkit/pyeq.py:537-548`: `_function_ast` returns the `FunctionDef` and nothing reads its
`decorator_list`. `inspect.getsource` unwraps through `__wrapped__`, so what is compiled is not the
callable `equivalent` was given. A wrapper without `wraps` gets its own source read and is handled.

## Engines

Both: the front end is shared.

## Fix

Clear. Raise `UnsupportedConstruct` when `decorator_list` is non-empty, and when `fn` has a
`__wrapped__` attribute.

## Proposed test

```python
import functools
import unittest

from cdclkit.pyeq import UnsupportedConstruct, equivalent


def double(fn):
    @functools.wraps(fn)
    def wrapper(x):
        return fn(x) * 2
    return wrapper


class TestDecorators(unittest.TestCase):
    def test_a_decorated_function_is_not_its_undecorated_body(self):
        @double
        def f(x): return x
        def g(x): return x
        with self.assertRaises(UnsupportedConstruct):
            equivalent(f, g, {"x": 3})
```
