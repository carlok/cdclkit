# engines-1: preprocessed proofs hold only if unit deletions are ignored

**Proposed severity: Note.** Same root as `preprocess-4`, reached here through
`solve_adaptive` on both engines. No answer is wrong and dratify accepts every one of
these proofs under the rule it documents (deletions of unit clauses are ignored). It is
a two-flavours disagreement, so by the brief it is not a bug. It is the separate report
asked for: a proof that holds under one flavour only.

## Minimal case

`(x1)(-x1)`. Removing either clause makes the formula satisfiable.

```python
from campaign import oracle
from cdclkit import MemoryProof, parse_dimacs, to_dimacs
from cdclkit.pipeline import solve_adaptive
F = [[1], [-1]]
for engine in ("python", "native"):
    p = MemoryProof()
    solve_adaptive(parse_dimacs("p cnf 1 2\n1 0\n-1 0\n"), engine=engine, proof=p,
                   always_preprocess=True)
    steps = [(k, tuple(to_dimacs(l) for l in c)) for k, c in p.steps]
    for flavour in ("specified", "operational", "length-one"):
        judged, final = oracle.replay(F, steps, flavour)
        print(engine, steps, flavour, [s.acceptable for s in judged], oracle.propagate(final)[0])
```

Actual, the same on both engines, with the engine name dropped:

```
[('d', (-1,)), ('a', ())] specified   [True, False] False
[('d', (-1,)), ('a', ())] operational [True, True]  True
[('d', (-1,)), ('a', ())] length-one  [True, True]  True
```

`oracle.rup([[1]], [])` is False: once `(-x1)` is deleted, the empty clause does not follow.

## Reach in the default run

Fails under `specified`: 237 of 6,658 replayed proofs. All 237 are on paths where
preprocessing ran: `adaptive.always` 75 native and 75 Python, `probe0` 45 and 15, `probe1`
13 and 6, `probe3` 5 and 3. Failures under `operational` or `length-one`: 0. Every proof
from the search alone (`Solver`, `solve()`, the native binding, the budgeted runs, the
portfolio) holds under all three flavours, including with `first_reduce=0` and clause
deletion active.

Python's probe runs fail less often than native's, most likely because Python keeps the
abandoned probe's lemmas in the proof (engines-3), and those can stand in for the deleted
unit. That explanation is inferred, not separately tested.

## Suspected cause

The unit's own clause is in the occurrence list of its literal, so it goes out with the
satisfied clauses and is logged as a deletion, and the steps after it rely on it.

- `cdclkit/preprocess.py:240`, in `propagate`
- `native/src/preprocess.rs:235`, the same loop

Both engines. The fix looks clear: do not log the deletion when the clause is the unit
being propagated.

## Proposed test

```python
class TestPreprocessedProofUnderSpecifiedDeletion(unittest.TestCase):
    def test_unit_is_not_deleted_before_it_is_needed(self):
        for engine in ("python", "native"):
            p = MemoryProof()
            solve_adaptive(parse_dimacs("p cnf 1 2\n1 0\n-1 0\n"), engine=engine,
                           proof=p, always_preprocess=True)
            self.assertNotIn(("d", (1,)), p.steps)  # internal literal of -x1
```
