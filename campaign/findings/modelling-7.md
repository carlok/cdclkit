# modelling-7: A Python bool in an expression constrains variable 0

**Proposed severity: Bug.** An encoding with the wrong solutions, silently, on every path below. `_as_expr` passes bools through
on purpose, so they are meant to work. `a == b` on two BoolVars is the natural way to write equality,
and it works on IntVar.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model

def solutions(build):
    m = Model()
    a, b = m.bool_var("a"), m.bool_var("b")
    build(m, a, b)
    return sorted((s[a], s[b]) for s in m.solutions(project=[a, b]))

print("add(True)  ", solutions(lambda m, a, b: m.add(True)))
print("add(False) ", solutions(lambda m, a, b: m.add(False)))
print("b | False  ", solutions(lambda m, a, b: m.add(b | False)))
print("b & True   ", solutions(lambda m, a, b: m.add(b & True)))
print("a == b     ", solutions(lambda m, a, b: m.add(a == b)))
```

## Actual output

```
add(True)   [(False, False), (False, True)]
add(False)  [(True, False), (True, True)]
b | False   [(False, True), (True, False), (True, True)]
b & True    [(False, True)]
a == b      [(True, False), (True, True)]
```

## What it should be

By enumeration over (a, b): `add(True)` has all 4 assignments; `add(False)` has none; `b | False` and
`b & True` are exactly the 2 with `b` true. `a == b` should be the 2 where they match, or an exception.
Instead `True` is literal 1 (not a) and `False` is literal 0 (a).

## Suspected cause

`cdclkit/model.py:79-84` returns a bool as is. `cdclkit/encodings.py:287` then takes it as a literal,
because `isinstance(True, int)`. `BoolVar` at `model.py:46` has no `__eq__`, so `a == b` is Python's
identity comparison and arrives as `False`.

## Engines

The CNF is wrong, so every engine gives the same wrong solutions. Checked through `Model`, and with
`check_native_cnf` on the same CNF.

## Fix

Clear for the constants: in `tseitin`, and in `_as_expr`, map a bool to `true_lit` or `false_lit`
before the int test. `BoolVar.__eq__` is a choice: return an `iff` tree as IntVar does, or raise. Raising
needs care, since `Model`'s callers may compare BoolVars by identity.

## Proposed test

```python
import unittest

from cdclkit.model import Model


def solutions(build):
    m = Model()
    a, b = m.bool_var("a"), m.bool_var("b")
    build(m, a, b)
    return {(s[a], s[b]) for s in m.solutions(project=[a, b])}


class TestBoolConstants(unittest.TestCase):
    def test_add_true_constrains_nothing(self):
        self.assertEqual(len(solutions(lambda m, a, b: m.add(True))), 4)

    def test_add_false_is_unsat(self):
        self.assertEqual(solutions(lambda m, a, b: m.add(False)), set())

    def test_or_false_is_the_operand(self):
        self.assertEqual(solutions(lambda m, a, b: m.add(b | False)),
                         {(False, True), (True, True)})

    def test_and_true_is_the_operand(self):
        self.assertEqual(solutions(lambda m, a, b: m.add(b & True)),
                         {(False, True), (True, True)})

    def test_boolvar_equality_is_equality_or_an_error(self):
        try:
            got = solutions(lambda m, a, b: m.add(a == b))
        except (TypeError, ValueError):
            return
        self.assertEqual(got, {(False, False), (True, True)})
```
