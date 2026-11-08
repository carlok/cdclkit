# engines-3: the proof streams differ even where the search is identical

**Proposed severity: Bug**, by the brief's "disagree on any field", and a low one: every
stream on both sides is valid under all three flavours, and the docstrings do not promise
equal streams. AGENTS.md promises conflicts, decisions and propagations, which do match.

## Minimal cases

Three separate differences. The search-phase steps match in all of them.

```python
from cdclkit import MemoryProof, Solver, from_dimacs, native, parse_dimacs, to_dimacs
from cdclkit.pipeline import solve_adaptive

# 1. add_clause strengthening: x2, then (-x2 x3) arrives with -x2 already false
p = MemoryProof(); s = Solver(3, proof=p)
for c in ([2], [-2, 3]): s.add_clause_dimacs(c)
s.solve()
n = native.require().Solver(3); n.enable_proof()
for c in ([2], [-2, 3]): n.add_clause([from_dimacs(l) for l in c])
n.solve()
print([(k, [to_dimacs(l) for l in c]) for k, c in p.steps], n.proof_steps())

# 2. a contradiction while loading
p = MemoryProof(); s = Solver(1, proof=p)
for c in ([1], [-1]): s.add_clause_dimacs(c)
n = native.require().Solver(1); n.enable_proof()
for c in ([1], [-1]): n.add_clause([from_dimacs(l) for l in c])
print(len(p.steps), len(n.proof_steps()))

# 3. a satisfiable run through the pipeline
text = "p cnf 2 2\n1 0\n-1 2 0\n"
for engine in ("python", "native"):
    p = MemoryProof()
    solve_adaptive(parse_dimacs(text), engine=engine, proof=p, never_preprocess=True)
    print(engine, p.steps)
```

Actual:

```
[('a', [3])]  []
2 1
python [('a', (2,))]
native []
```

A fourth, needing the probe to run out: with `probe=0` or `probe=1`, Python's proof keeps
the abandoned probe's lemmas and deletions in front of the preprocessing steps, and
native's has only what follows. 

The oracle has no objection to any of them: `replay` accepts each stream.

## Reach in the default run

`solver` 152, `raw` 73, and on `adaptive`: strengthening 211, SAT steps dropped 310, probe
prefix 2 (where the two preprocessors otherwise agreed).

A consequence worth noting: native later logs `d` for a strengthened clause it never
logged adding, so `d` names a clause the checker does not hold (`steps.del_absent`, 304
in the run). dratify tolerates it and the proofs still check.

## Suspected cause

- `cdclkit/solver.py:518` logs the strengthened clause, and `native/src/solver.rs:668` has
  no matching `proof_add`.
- `cdclkit/pipeline.py:124-127`: the native branch drains only on UNSAT, and the Python
  branch shares the caller's sink, so everything it logged stays.

Both are one-line fixes once somebody picks which side is right.

## Proposed test

```python
class TestProofStreamParity(unittest.TestCase):
    def test_add_clause_strengthening_is_logged_by_both(self):
        p = MemoryProof()
        s = Solver(3, proof=p)
        n = native.require().Solver(3)
        n.enable_proof()
        for c in ([2], [-2, 3]):
            s.add_clause_dimacs(c)
            n.add_clause([from_dimacs(l) for l in c])
        s.solve(); n.solve()
        self.assertEqual([(k, tuple(to_dimacs(l) for l in c)) for k, c in p.steps],
                         [(k, tuple(c)) for k, c in n.proof_steps()])
```
