# encodings-5: Optimiser.best can get worse

**Proposed severity: Bug.** The result of a documented API is worse than one it already held, against
its own docstring. `optimise()` and a single `Optimiser.run()` to completion are right on every
problem in the run: this needs a second, stopped `run`.

## Minimal case

One variable, no clauses, one soft literal.

## Reproducer

Run from the repo root.

```python
from cdclkit.encodings import Optimiser
from cdclkit.solver import Solver
from dratify.lits import mk_lit, neg

s = Solver()
x = mk_lit(s.new_var())
opt = Optimiser(s, [neg(x)])
print("first run", opt.run()[0], "best", opt.best[0])
print("second run", opt.run(max_iterations=1)[0], "best", opt.best[0])
```

Actual output:

```
first run 0 best 0
second run 1 best 1
```

## What it should be

Minimising `~x` over one free variable has the optimum 0, which the first run found. The docstring of
`Optimiser.run` says "Linear SAT-UNSAT search from the current best", and "stopping early still leaves
`best` holding the best solution found". After the second run `best` holds a solution with count 1,
and the optimum-0 model is gone. The assignment with count 0 exists: `x = true` makes `~x` false, and
there is nothing else to satisfy.

```python
from campaign import oracle
oracle.satisfiable([[1]])    # True: x = true is allowed, so the optimum is 0
```

## Why this severity

The class is described as the one to use to "resume after a budget, or drive the search yourself". That
is the path that hits this: a loop which calls `run(max_iterations=...)` again is told a worse answer
on its second pass, and it has no error to see.

Two details contribute. `self.iterations` accumulates across runs, so a later `run(max_iterations=K)`
stops after its first solve once K has been used up. And `run()` with no target starts with no bound
at all, whatever is already in `best`.

`opt.run(target=best - 1)`, the pattern the class docstring shows, stays correct, and the run confirms
it on every problem.

## Suspected cause

`cdclkit/encodings.py:777`: `bound = target`, not the current best. `encodings.py:784`:
`self.best = (n, model)` is unconditional. `encodings.py:789`: `self.iterations` is compared with a
per-call limit.

Engines: Python only. `Optimiser` asserts a Python `Solver` (`encodings.py:737`), so the native engine
is unreachable here. The fix looks clear: start at `best - 1` when no target is given and `best` is
set, overwrite `best` only on an improvement, and count iterations per call. The first two are enough
for this test. An existing test, `test_optimiser_reports_progress_and_can_stop_early`, passes
`target` explicitly and would not change.

## Proposed failing test

```python
import unittest
from cdclkit.encodings import Optimiser
from cdclkit.solver import Solver
from dratify.lits import mk_lit, neg

class TestOptimiserKeepsItsBest(unittest.TestCase):
    def test_a_later_stopped_run_does_not_lose_the_best(self):
        s = Solver()
        x = mk_lit(s.new_var())
        opt = Optimiser(s, [neg(x)])
        self.assertEqual(opt.run()[0], 0)
        self.assertEqual(opt.run(max_iterations=1)[0], 0)
        self.assertEqual(opt.best[0], 0)

if __name__ == "__main__":
    unittest.main()
```
