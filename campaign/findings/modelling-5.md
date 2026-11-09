# modelling-5: `Model.solve` ignores a constraint that adds no variable

**Proposed severity: Critical.** A wrong SAT model: the `Solution` violates a constraint of the model and the model's own CNF.
AGENTS.md shows `m.add(x == 3)` as the normal way to constrain, and that adds no variable. A
contradiction also reads as SAT.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.model import Model
from dratify.proof import MemoryProof, check_proof

m = Model()
x = m.int_var(range(3), "x")
first = m.solve()[x]
m.add(x != first)
second = m.solve()
print("first", first, "| added x !=", first, "| then", second[x],
      "| satisfies its CNF:", m.cnf.is_satisfied_by(second.bits))

m = Model()
a = m.bool_var("a")
m.solve()
m.add(a)
m.add(~a)
print("a and not a, after one solve: SAT =", m.solve() is not None)

m = Model()
p, q = m.bool_var("p"), m.bool_var("q")
for clause in ([p, q], [~p, q], [p, ~q], [~p, ~q]):
    m.add_clause(clause)
print("unsat:", m.solve() is None)
proof = MemoryProof()
print("second solve with a proof: unsat:", m.solve(proof=proof) is None, "| steps", len(proof.steps),
      "| replay ok:", check_proof(m.cnf, proof.steps).ok)
```

## Actual output

```
first 2 | added x != 2 | then 2 | satisfies its CNF: False
a and not a, after one solve: SAT = True
unsat: True
second solve with a proof: unsat: True | steps 0 | replay ok: False
```

## What it should be

By enumeration `x != first` leaves two values and the returned one is not among them.
`a and not a` has no solution. The comment at the site says the rebuild happens for "new constraints
since the last build", so this is the documented intent. The last lines show the related effect: a
proof passed to a later `solve()` goes nowhere, so an UNSAT from there cannot be replayed.

## Suspected cause

`cdclkit/model.py:320-322`: staleness is judged by `s.nvars < self.cnf.nvars`, so a clause with no
new variable is not noticed. Any unit on an existing literal does this: `m.add(a)`, `m.add(x == 3)`,
`m.add(x != 3)`, `add_clause`, and all pairwise encodings.

## Engines

Python only: `Model` has no engine parameter. The stale solver is the Python `Solver`, and the
CNF itself is right.

## Fix

Clear. Compare `self.cnf.nclauses` as well as `nvars` against what was loaded, and rebuild or add
the new clauses to the live solver. Rebuild also when `proof` differs from the solver's. Pair it with
modelling-6, which has the same root.

## Proposed test

```python
import unittest

from cdclkit.model import Model


class TestConstraintsAfterSolve(unittest.TestCase):
    def test_a_constraint_without_a_new_variable_is_seen(self):
        m = Model()
        x = m.int_var(range(3), "x")
        first = m.solve()[x]
        m.add(x != first)
        second = m.solve()
        self.assertNotEqual(second[x], first)
        self.assertTrue(m.cnf.is_satisfied_by(second.bits))

    def test_a_contradiction_after_solve_is_unsat(self):
        m = Model()
        a = m.bool_var("a")
        self.assertIsNotNone(m.solve())
        m.add(a)
        m.add(~a)
        self.assertIsNone(m.solve())
```
