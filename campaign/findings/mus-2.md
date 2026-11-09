# mus-2: "Exactly |M| solver calls after the initial core" is false when the core is not minimal

**Proposed severity: Note.** A docstring overstates a cost. Every returned set in the
campaign was still a MUS. It has no soundness consequence, so it does not fail the run.
`gen_mus` only counts it, as `doc_deletion_calls_more_than_M`.

## Minimal case

Removing any clause or literal loses the property (shrunk by a search that tries each).

```python
from dratify.cnf import CNF
from cdclkit.mus import MUSExtractor

f = CNF(0)
for c in ([2, -1], [-3, -2], [1, 2], [-2, 1], [3, -2]):
    f.add_dimacs(c)
ex = MUSExtractor(f)
r = ex.deletion()
print(r, ex.calls)
```

```
[0, 1, 2, 4] 6
```

## What the documentation says

`cdclkit/mus.py:26-27`, of the deletion algorithm: "Exactly `|M|` solver calls after the
initial core", where line 11 defines `M` as the MUS. Here `|M| = 4`, and the calls after
the initial core are `6 - 1 = 5`. The oracle agrees that the core of all five clauses is
not minimal:

```python
oracle.satisfiable([[2, -1], [-3, -2], [1, 2], [3, -2]])   # False: clause 3 is not needed
```

## Suspected cause

The loop at `cdclkit/mus.py:98-102` makes one call per candidate, so the cost is
`|core|`, not `|M|`. With `use_core=False` it is `|F|`. The code is right and the
sentence is wrong. Python only; there is no native MUS path.

**Fix:** clear, and it is one word: "Exactly `|core|` calls after the initial core".

## Proposed test

```python
def test_deletion_spends_one_call_per_core_clause(self):
    f = CNF()
    for c in ([2, -1], [-3, -2], [1, 2], [-2, 1], [3, -2]):
        f.add_dimacs(c)
    core = MUSExtractor(f).core()
    ex = MUSExtractor(f)
    ex.deletion()
    self.assertEqual(ex.calls, 1 + len(core))
```

This passes today. It pins the behaviour the corrected sentence would describe.
