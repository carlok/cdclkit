# engines-4: after a failed re-solve the native Solver still reports the old model

**Proposed severity: Bug.** The engines disagree on a field, and it is the field a caller
reads. Python clears the model at the top of `solve`. The return value is right on both,
so code that tests the return value first is safe. It is not Critical: nothing claims the
stale model is a model.

## Minimal case

```python
from cdclkit import Solver, native
p = Solver(1); p.add_clause([0]); p.solve(); p.add_clause([1]); print(p.solve(), p.model)
n = native.require().Solver(1); n.add_clause([0]); n.solve(); n.add_clause([1])
print(n.solve(), list(n.model))
```

Actual:

```
False []
False [True]
```

Expected: `False []` on both. `oracle.satisfiable([[1], [-1]])` is False, so no model
exists, and `[True]` falsifies `(-x1)`.

It needs `add_clause` to have refuted the formula at the root. A re-solve that does the
search clears the model properly. 90 occurrences in the default run's 877 incremental solves.

## Suspected cause

`native/src/solver.rs:1427`: `if !self.ok { return Some(false); }` comes before
`self.model.clear()` at line 1430. `cdclkit/solver.py:1322` clears first. Native only.
The fix is clear: swap them.

## Proposed test

```python
class TestModelClearedOnRefutation(unittest.TestCase):
    def test_a_refuted_re_solve_leaves_no_model(self):
        n = native.require().Solver(1)
        n.add_clause([0])
        self.assertTrue(n.solve())
        self.assertFalse(n.add_clause([1]))
        self.assertFalse(n.solve())
        self.assertEqual(list(n.model), [])
```
