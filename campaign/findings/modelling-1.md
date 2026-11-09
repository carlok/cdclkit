# modelling-1: pyeq compiles a value-position `and`/`or` to 0/1

**Proposed severity: Critical.** A wrong `proved=True`, with the proof replayed, on functions that differ in Python
at values that fit the width with no overflow anywhere. The brief counts that as a wrong
UNSAT that passed the self-check. The miter is correctly UNSAT; the circuit is not the
function. The opposite answer is wrong too: `x and x` equals `x` on every input, pyeq says
`proved=False` and blames overflow, though nothing overflows.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.pyeq import UnsupportedConstruct, equivalent

def f(x): return x and x
def g(x): return 1 if x else 0
def h(x): return x

for engine in ("python", "native"):
    r = equivalent(f, g, {"x": 3}, engine=engine)
    print(engine, "f vs g: proved", r.proved, "proof_checked", r.proof_checked)
    r = equivalent(f, h, {"x": 3}, engine=engine)
    print(engine, "f vs h: proved", r.proved, r.counterexample, r.outputs, r.python_outputs,
          "overflow_only", r.overflow_only)
print("f(2), g(2), h(2) =", f(2), g(2), h(2))
print("f == g everywhere:", all(f(x) == g(x) for x in range(-4, 4)))
print("f == h everywhere:", all(f(x) == h(x) for x in range(-4, 4)))
```

## Actual output

```
python f vs g: proved True proof_checked True
python f vs h: proved False {'x': -4} (1, -4) (-4, -4) overflow_only True
native f vs g: proved True proof_checked True
native f vs h: proved False {'x': -4} (1, -4) (-4, -4) overflow_only True
f(2), g(2), h(2) = 2 1 2
f == g everywhere: False
f == h everywhere: True
```

## What it should be

Exhaustive Python over the 8 inputs of 3 bits: `f` and `g` differ (`f(2)=2`, `g(2)=1`), so
`proved` must not be True. `f` and `h` agree everywhere, so `proved=False` is wrong, and so is
`overflow_only=True`. The module docstring says "Every operation whose meaning would be ambiguous
is rejected rather than guessed", and the CHANGELOG says everything outside the subset raises
`UnsupportedConstruct`. Inside a condition (`if x and y:`) the compiled truth value is right; the
generator's trap-free pairs use that form and show no mismatch.

## Suspected cause

`cdclkit/pyeq.py:288-290`: `expr()` sends `ast.BoolOp` to `truth()` and selects 1 or 0.

## Engines

Both: the front end is shared.

## Fix

Clear. Either compile the value position by Python's rule (`a and b` is `b if a else a`, folded
right to left), or raise `UnsupportedConstruct` there and keep `truth()` for conditions.

## Proposed test

```python
import unittest

from cdclkit.pyeq import UnsupportedConstruct, equivalent


class TestValueBoolOp(unittest.TestCase):
    def test_and_in_a_value_position_is_an_operand_not_a_bool(self):
        def f(x): return x and x
        def g(x): return 1 if x else 0
        try:
            r = equivalent(f, g, {"x": 3})
        except UnsupportedConstruct:
            return
        self.assertIs(r.proved, False, "f(2) is 2 and g(2) is 1")

    def test_or_in_a_value_position_is_an_operand_not_a_bool(self):
        def f(x): return x or x
        def g(x): return 1 if x else 0
        try:
            r = equivalent(f, g, {"x": 3})
        except UnsupportedConstruct:
            return
        self.assertIs(r.proved, False, "f(2) is 2 and g(2) is 1")
```
