# preprocess-4: preprocessing proofs delete a unit before relying on it

**Proposed severity: Note.** dratify documents that deletions of unit clauses are
ignored, and under that rule every proof the generator replayed passed. This is a
disagreement between the two flavours of DRAT, not a dratify bug and not a wrong answer.
It is recorded because `cdclkit/preprocess.py` says more than holds under `specified`.

## Minimal cases

An unsatisfiable one. Removing either clause makes the formula satisfiable and the
empty clause never appears:

```python
from campaign import oracle
from dratify.cnf import CNF
from dratify.lits import from_dimacs, to_dimacs
from dratify.proof import MemoryProof, check_proof
from cdclkit.preprocess import Preprocessor

cs = [[1], [-1]]
f = CNF(1)
for c in cs:
    f.add([from_dimacs(d) for d in c])
proof = MemoryProof()
Preprocessor(f, proof=proof).run()
steps = [(k, [to_dimacs(l) for l in c]) for k, c in proof.steps]
print(steps)                                     # [('d', [-1]), ('a', [])]

for flavour in ("specified", "operational", "length-one"):
    judged, _ = oracle.replay(cs, steps, flavour=flavour)
    print(flavour, [s.acceptable for s in judged])
# specified   [True, False]   the empty clause is not RUP: only (x1) is left
# operational [True, True]
# length-one  [True, True]

print(check_proof(f, proof, engine="python").ok) # True
```

A satisfiable one, where the first bad step is an ordinary lemma:

```python
cs = [[-3, 2], [3], [-1, -2]]
# steps: d 3, a 2, d -3 2, d 2, a -1, d -1 -2, d -1
# under `specified`, (x2) is neither RUP nor RAT once (x3) is gone
```

## How often

Over the default run the counters `proof_fails_under_specified_flavour` and
`proof_passes_under_specified_flavour` record this: see
`campaign/results/preprocess.json`. Under `length-one` and `operational` no step of any
proof failed, and every addition was also implied by the input.

## Cause

`propagate` removes every clause containing the literal it has just fixed, and that
includes the unit clause itself, before it strengthens the clauses containing the
complement: `cdclkit/preprocess.py:239-240` and then `251`, and
`native/src/preprocess.rs:234-236` and then `249`. Both engines do the same.

The module docstring at `cdclkit/preprocess.py:54-57` says "a plain DRAT checker verifies
the entire preprocessing phase with no special support". That holds for a checker that
ignores unit deletions, which dratify documents and which drat-trim does by default. It
does not hold for one that honours them. drat-trim itself was not run: it is not installed
here, so `operational` above is the oracle's approximation of it.

The fix is clear if anyone wants it: do not log the deletion of the unit being
propagated, or log it after the strengthening. Either passes under all three flavours.

## A related wording problem

`CHANGELOG.md:177`, `CHANGELOG.md:347` and the docstring of
`tests/test_adaptive_proof.py` say bounded variable elimination "adds clauses that do not
follow from the input". The generator checks the opposite on every run, with
`oracle.implies(input, clause)` over every proof addition and every reduced clause, and
found no exception. `cdclkit/preprocess.py:34` has it right: "The resolvents are logically
implied". It is *removing the parents* that loses equivalence. The conclusion those passages
draw, that the preprocessing steps must be logged, is still correct, because a refutation
of the reduced formula may use resolvents that are not RUP against the input.

## Proposed test

Only worth adding if the proofs are changed to pass under `specified`. For
`tests/test_preprocess.py`:

```python
def test_a_unit_is_not_deleted_before_it_is_used(self):
    f = CNF(2)
    f.add([mk_lit(0)])
    f.add([neg(mk_lit(0)), mk_lit(1)])
    proof = MemoryProof()
    Preprocessor(f, proof=proof).run()
    unit_deletions = [i for i, (k, c) in enumerate(proof.steps)
                      if k == "d" and len(c) == 1]
    last_addition = max(i for i, (k, _) in enumerate(proof.steps) if k == "a")
    self.assertGreater(min(unit_deletions), last_addition,
                       "a later step leans on a checker ignoring a unit deletion")
```

Today the steps are `d 1`, `a 2`, `d -1 2`, `d 2`, so it fails with `0 not greater than 1`.
