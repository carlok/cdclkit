# preprocess-3: the two engines' preprocessors disagree on everything but the answer

**Proposed severity: Bug, of low impact.** The brief lists "the Python and native engines
disagree on any field" as a Bug, and they do. No verdict differed and every model from
either engine satisfied the input, so nothing here is a wrong answer.

The bit-exactness claim is mostly about the solver, and `tests/test_pyeq.py:446` warns
against reading it too broadly. But `AGENTS.md:72` and `README.md` state "identical
conflicts", and `AGENTS.md` names `solve_adaptive()` as a native entry point, whose default
path preprocesses. On that path the conflict counts differ. So either the code or the claim
should change.

## Minimal cases

Each was shrunk until removing any clause or literal makes the fields agree, and each was
run on both engines. Run from the repo root:

```python
from dratify.cnf import CNF
from dratify.lits import from_dimacs
from cdclkit.preprocess import Preprocessor
from cdclkit.pipeline import solve_adaptive
from cdclkit import native

def cnf(n, cs):
    f = CNF(n)
    for c in cs:
        f.add([from_dimacs(d) for d in c])
    return f

def adaptive(n, cs, field):
    f = cnf(n, cs)
    return [getattr(solve_adaptive(f, engine=e, always_preprocess=True), field)
            for e in ("python", "native")]

def stats(n, cs):
    f = cnf(n, cs)
    py = Preprocessor(f, do_bce=False)   # native has no BCE: compare like with like
    py.run()
    p = native.require().Preprocessor(n)
    for c in f.clauses:
        p.add_clause(list(c))
    p.run(3)
    return py.stats, p

# model: both satisfy the formula
adaptive(2, [[2, 1], [-1, -2]], "model")
# [[False, True], [True, False]]

# conflicts, SAT, the claim AGENTS.md makes
CONFLICTS = [[-9, 2], [1, 4], [-7, 11], [-11, 5], [-2, -6], [-2, -5], [-12, 7], [-3, -12],
             [8, 6, -3], [-8, 5], [-12, -10], [3, -8], [6, 11, -1], [-4, -3], [7, -1],
             [9, 1, 3], [-8, 12], [-4, -8], [9, -6], [-9, -5], [-7, 12], [2, 10],
             [-3, 9, 8], [-2, 4]]
adaptive(12, CONFLICTS, "conflicts")          # [1, 0]
adaptive(12, CONFLICTS, "clauses_after")      # [17, 0]

# clauses_after, SAT
AFTER = [[5, 1, -7], [-5, 9], [-10, -7], [-9, 1], [4, 5, -2], [-9, -6], [-4, -3], [-8, 9, 4],
         [5, -1, 6], [-7, 6, 4], [8, 6], [3, 10, 2], [-6, 3], [-5, -2, 7], [-4, 6, 7, 1],
         [2, -6], [3, 7, 9], [7, -4, 5], [-1, -2], [7, 8, 2]]
adaptive(10, AFTER, "clauses_after")          # [9, 11]

# stats with BCE off on the Python side, and the same reduced formula
py, p = stats(3, [[-1, 2], [-1, -3], [1, 2], [1, -2], [-1, -2]])
py.strengthened, p.strengthened               # (4, 3)
py, p = stats(4, [[-1], [-3], [2, -4, 3], [4, 3], [1, -4]])
py.units, p.units                             # (3, 4)
```

## What the oracle says

Nothing against either engine on the answer. Both reduced formulas are equisatisfiable with
the input, every reduced clause is implied by it, and every sampled model reconstructs. Both
engines' proofs replay under `length-one` with every addition RUP. The two proofs are not the
same list of steps, and on some formulas not even the same multiset of clauses. With BCE off
on the Python side, the reduced formulas compared as multisets of clause sets never differed
(`parity-reduced` is at zero: see the results file).

## Suspected cause

There are two separate causes.

1. **No BCE in native.** `cdclkit/preprocess.py:316` has `block_eliminate`, and `run` calls it
   by default. `native/src/preprocess.rs:461-493` has no such pass, and its module doc does
   not list one. `cdclkit/pipeline.py:164` uses the Python defaults and `:151` the native
   ones, so `solve_adaptive` compares different preprocessors. `README.md:105` lists BCE with
   no mention of the engine. This accounts for the `clauses_after`, `conflicts` and `model`
   cases above: rerun with `Preprocessor(f, do_bce=False)`, and the search run by the Python
   solver on each reduced formula, all three cases agree on all three fields. BCE is also not
   always a reduction: on `CONFLICTS` it leaves 17 clauses and one conflict where BCE off
   leaves none. The likely reason, not traced, is that removing a blocked clause changes what
   BVE can then afford.
2. **Iteration order.** Python's occurrence lists are `set`s (`preprocess.py:153`), and
   native's are `Vec`s with `swap_remove` (`preprocess.rs:65`, `:172`). Subsumption and
   propagation visit clauses in a different order, so the counters and the proof differ,
   and on UNSAT inputs the early exit is reached at a different point.

Both engines are involved by definition. The fix is not clear, because it is a choice: port BCE
and match the iteration order, which is a real piece of work, or say in `AGENTS.md`, the
README and `solve_adaptive`'s docstring that bit-exactness stops at the search and that a
preprocessing run may differ. The second is cheap and honest.

## Proposed test

For `tests/test_pipeline.py`, in `TestNativePreprocessorAgreesWithPython`. It fails today, and
it should be replaced by a statement of the narrower claim if that is the choice made:

```python
def test_conflicts_are_identical_through_the_preprocessing_path(self):
    """AGENTS.md: 'identical conflicts, decisions and propagations'."""
    cs = [[-9, 2], [1, 4], [-7, 11], [-11, 5], [-2, -6], [-2, -5], [-12, 7],
          [-3, -12], [8, 6, -3], [-8, 5], [-12, -10], [3, -8], [6, 11, -1],
          [-4, -3], [7, -1], [9, 1, 3], [-8, 12], [-4, -8], [9, -6], [-9, -5],
          [-7, 12], [2, 10], [-3, 9, 8], [-2, 4]]
    f = CNF(12)
    for c in cs:
        f.add([from_dimacs(d) for d in c])
    py = solve_adaptive(f, engine="python", always_preprocess=True)
    rs = solve_adaptive(f, engine="native", always_preprocess=True)
    self.assertEqual(py.conflicts, rs.conflicts)
```

This needs `from dratify.lits import from_dimacs` at the top of that file if it is not already
there.
