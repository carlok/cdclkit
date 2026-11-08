# encodings-4: Inputs not yet declared to the sink collide with auxiliary variables

**Proposed severity: Bug**, "an encoding has the wrong solutions". Lower it to Note if the project
decides that declaring inputs first is a precondition, which it would then need to document: nothing
says so today, and both sinks accept undeclared literals without complaint.

## Minimal case

Two inputs, the binary method, a fresh `CNF()`. Declaring the inputs first makes it pass, and so does
any method that adds no auxiliary variable.

## Reproducer

Run from the repo root.

```python
from campaign import dpll
from dratify.cnf import CNF
from dratify.lits import mk_lit, to_dimacs
from cdclkit.encodings import at_most_one
from cdclkit.solver import Solver

xs = [mk_lit(0), mk_lit(1)]

f = CNF()
at_most_one(f, xs, "binary")
clauses = [[to_dimacs(l) for l in c] for c in f.clauses]
print("clauses", clauses, "nvars", f.nvars)
print("cnf", sorted(dpll.projected_models(clauses, [1, 2])))

s = Solver()
at_most_one(s, xs, "binary")
print("solver", [(a, b) for a in (False, True) for b in (False, True)
                 if s.solve([xs[0] ^ (not a), xs[1] ^ (not b)])])
```

Actual output:

```
clauses [[-1], [-2, 1]] nvars 2
cnf [(False, False)]
solver [(False, False)]
```

The clause list shows it: the code variable the binary encoding asked for is variable 1, the first
input, so `x1 -> ~code` became `~x1`, and `x2 -> code` became `x2 -> x1`.

## What it should be

At most one of two inputs has the solutions `(F, F)`, `(F, T)` and `(T, F)`. The encoding has one. The
same call with `f.new_var()` declared first gives all three.

Run for `at_most_one` over 1 to 8 undeclared inputs, the first size that goes wrong is 2 for `binary` and
`totalizer`, 3 for `sequential`, 4 for `commander` and 7 for `auto`, which is where it stops using
pairwise. `pairwise` never does, as it adds no variable. `at_most_k` goes wrong for `sequential` and
`totalizer` from k = 1, and for `auto` from k = 2.

The oracle agrees, on the formula as emitted and on the one the method means:

```python
from campaign import oracle
oracle.implies([[-1], [-2, 1]], [-2])   # True: x2 is forced false, so (F, T) is lost
```

## Why it is reachable

`CNF`'s docstring says "the variable count grows to cover every literal seen", and `Solver.add_clause`
calls `ensure_vars`. So undeclared literals work everywhere else. `from_dimacs` hands out exactly such
literals. A user writing `at_most_one(CNF(), [from_dimacs(d) for d in (1, 2, 3)], "binary")` gets a wrong
formula and no error. `test_encodings.py` always declares first, so the suite never sees it.

## Suspected cause

`cdclkit/encodings.py:128`, `Encoder.new_var`, takes the sink's next variable, which ignores input
literals the sink has not seen yet. `amo_binary` at line 371, `amk_sequential` at line 447, the
commander at line 396 and `Totalizer._merge` at line 621 all allocate before adding any clause.

Engines: both, since the formula is wrong before a solver sees it. With `x2` set true, `solve()` and
`solve_adaptive` with either engine answer UNSAT where SAT is right. The fix is fairly clear: grow the
sink to cover the input literals on entry to each constraint. It takes one helper called from about
five places, and `Totalizer` needs it too. Raising instead would also be defensible, but it would
break a usage that works today for pairwise.

## Proposed failing test

```python
import itertools
import unittest
from dratify.cnf import CNF
from dratify.lits import mk_lit, neg
from cdclkit.encodings import at_most_one
from cdclkit.solver import Solver

class TestUndeclaredInputs(unittest.TestCase):
    def test_auxiliary_variables_do_not_collide_with_inputs(self):
        for method in ("binary", "commander", "sequential", "totalizer"):
            xs = [mk_lit(i) for i in range(4)]
            f = CNF()
            at_most_one(f, xs, method)
            for bits in itertools.product((0, 1), repeat=4):
                s = Solver(f.nvars)
                ok = s.add_cnf(f)
                got = bool(ok and s.solve([x if b else neg(x) for x, b in zip(xs, bits)]))
                self.assertEqual(got, sum(bits) <= 1, f"{method} bits={bits}")

if __name__ == "__main__":
    unittest.main()
```
