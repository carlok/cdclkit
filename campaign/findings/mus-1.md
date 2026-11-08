# mus-1: a repeated index raises IndexError, and the solver then gives wrong UNSAT answers

**Proposed severity: Bug.** The crash needs a repeated index in `subset`, which no
document forbids. The wrong answers only follow on a solver that has already raised.
Read literally, the second half meets Critical's "wrong UNSAT that passes its own
self-check": `verify` endorses a satisfiable set. I propose Bug because the caller has
already been told something went wrong, and because `mus()`, `shrink_core()` and the CLI
cannot reach this. No repeated index and no caught exception means no wrong answer in
this campaign's runs. The orchestrator should make the final call.

## Minimal case

Removing either clause, or the repeated `0`, makes the first half pass (found by
exhaustive search over clause subsets of the four sign patterns on two variables, and
subset lists up to length 6).

```python
from dratify.cnf import CNF
from cdclkit.mus import MUSExtractor

f = CNF(0)
f.add_dimacs([1, 2])
f.add_dimacs([1, -2])
MUSExtractor(f).is_unsat([0, 0, 1])
```

```
IndexError: list index out of range
  cdclkit/mus.py:65     is_unsat  return not self.solver.solve([...])
  cdclkit/solver.py:1217 _search  learnt, bt, lbd = self._analyze(confl)
  cdclkit/solver.py:827 _analyze  lbd = self._lbd(learnt)
  cdclkit/solver.py:729 _lbd      if stamp[lv] != gen:
```

`core`, `deletion`, `quickxplain` and `verify` all raise the same way on `[0, 0, 1]`.
It is not specific to MUS. With no selector machinery at all:

```python
from cdclkit.solver import Solver
from dratify.lits import mk_lit
s = Solver(3)
for c in ([-3, 1, 2], [-3, -1, 2], [-3, 1, -2], [-3, -1, -2]):
    s.add_clause_dimacs(c)
s.solve([mk_lit(2)] * 3)    # IndexError, same line
```

### The second half: what the same extractor says afterwards

The smallest case found by a similar search (the same clause sets, repeated-index lists
of length 3 to 5, then every subset as the follow-up question):

```python
from dratify.cnf import CNF
from cdclkit.mus import MUSExtractor
from campaign import oracle

G = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
f = CNF(0)
for c in G:
    f.add_dimacs(c)
ex = MUSExtractor(f)
try:
    ex.is_unsat([0, 0, 0, 0, 2])
except IndexError:
    pass
r = ex.deletion()
print(r, ex.verify(r), oracle.satisfiable([G[i] for i in r]))
```

```
[1, 3] (True, 'verified: unsatisfiable, and all 2 clauses are necessary') True
```

## What it should be

- `is_unsat([0, 0, 1])` should be `not oracle.satisfiable([[1, 2], [1, -2]])`, which is
  `False`. `subset` is typed `Sequence[int]`, and the docstring says "the clauses indexed
  by `subset`". Clause 0 listed twice is still clause 0, so `oracle.satisfiable` on the
  set is the answer. The solver already has a branch for an assumption that is already
  true (`solver.py:1287`), so a repeat is meant to be survivable.
- `ex.deletion()` on `G` should be `[0, 1, 2, 3]`, which is what a fresh extractor
  returns. `oracle.satisfiable([G[1], G[3]])` is `True`: `[1, 3]` is not unsatisfiable,
  and `verify` should not say it is.

## Suspected cause

- `cdclkit/solver.py:449`: `_lbd_stamp` gets one slot per variable, but `_lbd` at
  `solver.py:729` indexes it by **decision level**. Those are only comparable when every
  level holds a variable. `solver.py:1287-1288` opens an empty "dummy" level for an
  assumption that is already true. A repeated literal therefore adds levels without
  adding variables, and a conflict at level >= `nvars` indexes past the end. Without
  repeats each level uses up a variable, and a conflict at level `nvars` would need a
  clause that unit propagation should already have caught, so this looks unreachable
  there. No crash without a repeat appeared in any run.
- The aftermath is at `solver.py:827-830`: `_lbd` runs before `seen` is cleared from
  `_analyze_toclear`. The exception leaves `seen` dirty (`[2, 4]` in the case above), and
  `solve()`'s `finally` does not clear it. The next `_analyze` skips those variables and
  learns a clause that does not follow. Every later answer from that solver is suspect.

**Engines:** Python only. `native/src/lib.rs` exposes `solve(max_conflicts, seconds)`
with no assumptions, and `native/src/solver.rs` has no assumption code, so there are no
dummy levels. `mus` always uses the Python `Solver` (AGENTS.md), so no native MUS path
exists to run; this was read, not executed.

**Fix:** looks clear. Either grow `_lbd_stamp` when `lv >= len(stamp)`, or size it for
levels, or drop repeats from `self.assumptions` in `solve()`. Clearing `seen` from
`_analyze_toclear` in `solve()`'s `finally` would separately stop a future exception
turning into wrong answers.

## Proposed test

```python
class TestRepeatedIndices(unittest.TestCase):
    def _formula(self, clauses):
        f = CNF()
        for c in clauses:
            f.add_dimacs(c)
        return f

    def test_a_repeated_index_means_the_same_clause(self):
        f = self._formula([[1, 2], [1, -2]])
        ex = MUSExtractor(f)
        self.assertFalse(ex.is_unsat([0, 0, 1]))
        self.assertEqual(ex.core([0, 0, 1]), [])
        self.assertEqual(ex.deletion([0, 0, 1]), [])
        self.assertEqual(ex.quickxplain([0, 0, 1]), [])

    def test_a_repeated_assumption_in_the_solver(self):
        s = Solver(3)
        for c in ([-3, 1, 2], [-3, -1, 2], [-3, 1, -2], [-3, -1, -2]):
            s.add_clause_dimacs(c)
        self.assertFalse(s.solve([mk_lit(2)] * 3))

    def test_repeated_indices_do_not_poison_the_extractor(self):
        f = self._formula([[1, 2], [-1, 2], [1, -2], [-1, -2]])
        ex = MUSExtractor(f)
        self.assertTrue(ex.is_unsat([0, 0, 0, 0, 1, 2, 3]))
        self.assertEqual(ex.deletion(), [0, 1, 2, 3])
```

Run by `campaign/gen_mus.py` as the checks `sub_*:raised`, `verify:raised` and
`post_crash_is_unsat`, labelled `mus-1`; the run exits non-zero until this is fixed.
