# modelling-6: `Model.solve` after `Model.solutions` answers for the blocked problem

**Proposed severity: Bug.** A wrong UNSAT, on a satisfiable model. It is not Critical under the brief's definition because no
self-check passes: a proof passed to that `solve()` stays empty and does not replay. That wording is
narrow and this is still a wrong answer to the user, so the orchestrator may want to treat it with
modelling-5.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model
from dratify.proof import MemoryProof, check_proof

m = Model()
a = m.bool_var("a")
print("solutions:", len(list(m.solutions(project=[a]))), "| then solve():", m.solve())

m = Model()
a = m.bool_var("a")
list(m.solutions(project=[a]))
proof = MemoryProof()
print("with a proof:", m.solve(proof=proof), "| steps", len(proof.steps),
      "| replay ok:", check_proof(m.cnf, proof.steps).ok)
```

## Actual output

```
solutions: 2 | then solve(): None
with a proof: None | steps 0 | replay ok: False
```

## What it should be

One free boolean has 2 solutions, so `solve()` must return one, not None. The blocking clauses
belong to the enumeration; `Solver.enumerate_models` documents that it leaves its solver stronger,
but `Model.solutions` does not say it changes what `Model.solve` answers.

## Suspected cause

`cdclkit/model.py:327` calls `build_solver`, which stores the solver in `self.solver`
(`model.py:316`); `enumerate_models` then adds blocking clauses to it, and `solve` at `model.py:320`
reuses it. A partly consumed generator leaves the same state.

## Engines

Python only: `Model` has no engine parameter. The CNF is unaffected.

## Fix

Clear. Enumerate on a private solver in `solutions()` and leave `self.solver` alone.

## Proposed test

```python
import unittest

from cdclkit.model import Model


class TestSolveAfterSolutions(unittest.TestCase):
    def test_enumeration_does_not_change_the_problem(self):
        m = Model()
        a = m.bool_var("a")
        self.assertEqual(len(list(m.solutions(project=[a]))), 2)
        self.assertIsNotNone(m.solve())
```
