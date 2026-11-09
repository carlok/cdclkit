# modelling-2: pyeq drops bare expression statements that are not calls

**Proposed severity: Critical.** Wrong `proved=True` with a replayed proof. The walrus case returns a different integer on every
input; the others raise or return a generator. The comment at the site says bare expressions "have
no effect", which is false for each of these, and the module docstring says "A verifier that quietly
ignores a construct is worse than no verifier".

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.pyeq import UnsupportedConstruct, equivalent

def identity(x): return x

def walrus(x):
    (x := x + 1)
    return x

def generator(x):
    yield x
    return x

def raises(x):
    x % 0
    return x

for fn in (walrus, generator, raises):
    for engine in ("python", "native"):
        print(fn.__name__, engine, equivalent(fn, identity, {"x": 3}, engine=engine).proved)
print("walrus(1) =", walrus(1), " identity(1) =", identity(1))
```

## Actual output

```
walrus python True
walrus native True
generator python True
generator native True
raises python True
raises native True
walrus(1) = 2  identity(1) = 1
```

## What it should be

Running them in Python: `walrus(1)` is 2 and `identity(1)` is 1; `generator(1)` is a generator
object; `raises(1)` raises ZeroDivisionError. Each must be `UnsupportedConstruct` or `proved=False`.
A walrus in an expression (`return (y := x)`) is already rejected; only the statement form escapes.

## Suspected cause

`cdclkit/pyeq.py:446-448`: `ast.Expr` is ignored unless its value is directly an `ast.Call`, so a
call one level down (`[print(x) for i in range(1)]`) escapes too.

## Engines

Both: the front end is shared.

## Fix

Clear. Accept only `ast.Pass` and an `ast.Expr` whose value is an `ast.Constant`, the docstring
case, and raise for every other statement expression.

## Proposed test

```python
import unittest

from cdclkit.pyeq import UnsupportedConstruct, equivalent


def identity(x): return x


class TestBareExpressions(unittest.TestCase):
    def assert_not_proved(self, fn):
        try:
            r = equivalent(fn, identity, {"x": 3})
        except UnsupportedConstruct:
            return
        self.assertIsNot(r.proved, True)

    def test_walrus_statement(self):
        def f(x):
            (x := x + 1)
            return x
        self.assert_not_proved(f)

    def test_yield_statement(self):
        def f(x):
            yield x
            return x
        self.assert_not_proved(f)

    def test_raising_expression(self):
        def f(x):
            x % 0
            return x
        self.assert_not_proved(f)

    def test_docstring_is_still_fine(self):
        def f(x):
            """A docstring."""
            return x
        self.assertIs(equivalent(f, identity, {"x": 3}).proved, True)
```
