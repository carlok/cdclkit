# engines-2: the preprocessors are not bit-exact

**Proposed severity: Bug.** The brief: "the Python and native engines disagree on any
field". AGENTS.md says the native engine "is bit-exact with the Python engine" and "the
engine changes the speed, never the answer", and `solve_adaptive`, `--adaptive` and the
CDCLKIT_ENGINE switch rest on that. The verdict never differed and every model satisfied
the formula, so this is not Critical. It does break the advice in AGENTS.md: switching
`CDCLKIT_ENGINE` to rule the native engine in or out changes the search on these paths.

The search engines themselves are bit-exact: no counter differed on any path that does
not preprocess, over 600 direct runs, the budgeted runs, jobs=1 and the n=205 instance
that crosses the default reduction, rephasing and blocking thresholds.

## Minimal cases

Each is shrunk: removing a clause or a literal makes that field agree.

```python
from cdclkit import parse_dimacs
from cdclkit.pipeline import solve_adaptive

def both(text):
    for engine in ("python", "native"):
        r = solve_adaptive(parse_dimacs(text), engine=engine, always_preprocess=True)
        print(engine, r.sat, r.conflicts, r.clauses_after, r.model)

# the model
both("p cnf 9 4\n8 5 7 0\n-5 -6 0\n5 6 -7 0\n-8 9 0\n")
# conflicts and clauses_after
both("p cnf 7 16\n-3 -1 0\n4 -1 0\n7 -3 0\n-7 -4 0\n-6 1 -5 0\n3 -7 0\n6 3 0\n-5 -2 -6 0\n"
     "6 7 -2 0\n5 -6 -4 0\n-4 3 -5 0\n2 7 4 0\n-7 -1 0\n-5 6 -1 0\n-4 3 2 0\n-2 5 1 0\n")
```

Actual, with the models abbreviated:

```
python True 0 0  [F F F F T F F F F]
native True 0 0  [F F F F F F F T T]
python True 1 15 [F F T F F F T]
native True 0 0  [F F T F F F T]
```

Past the real 1000-conflict probe, the default path, n=205 at ratio 4.35 with seed 6:
identical probe (1003 conflicts) and `clauses_after` (880), then 31,049 conflicts and a
66,045-step proof on Python against 28,424 and 58,345 on native.

Oracle: all of these answers and models are right. `oracle.satisfiable` agrees and every
model satisfies the formula. Only the parity claim fails.

## Reach in the default run

Tiny formulas, `solve_adaptive`, always_preprocess: `model` differs 15 times, `clauses_after`
5, `conflicts` 1, proof 291, out of 300.

## Suspected cause

Two independent ones:

- Python has blocked clause elimination, on by default (`cdclkit/preprocess.py:138`, `:423`),
  and `native/src/preprocess.rs:461` `run` has none.
- Python's occurrence lists are sets (`preprocess.py`, `self.occ`), native's are vectors,
  so clauses are visited and logged in a different order, which also orders the
  reconstruction stack.

The fix is a decision rather than a patch: port BCE and the iteration order, or narrow the
claim in AGENTS.md and README.md to the search and say the preprocessors differ.

## Proposed test

```python
class TestPreprocessingParity(unittest.TestCase):
    def test_engines_agree_when_preprocessing_runs(self):
        text = "p cnf 9 4\n8 5 7 0\n-5 -6 0\n5 6 -7 0\n-8 9 0\n"
        a = solve_adaptive(parse_dimacs(text), engine="python", always_preprocess=True)
        b = solve_adaptive(parse_dimacs(text), engine="native", always_preprocess=True)
        self.assertEqual(a.model, b.model)
```
