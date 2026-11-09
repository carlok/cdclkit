# modelling-14: `proof_steps` differs between the engines

**Proposed severity: Note.** The brief lists any field disagreement as a Bug, and this is one, but it is documented and harmless, so
this proposes Note. Both proofs replay, and the conflict counts match. The generator counts it as
`note_proof_steps_differ` and does not fail on it. If the orchestrator prefers the literal reading, the fix
is to log nothing in Python or to log the same step in Rust.

## Reproducer

Save it to a file and run it with the campaign venv. pyeq reads source through `inspect`, so piping to
`python -` does not work.

```python
from cdclkit.pyeq import UnsupportedConstruct, equivalent

def f(a, b): return a * b
def g(a, b): return b * a

p = equivalent(f, g, {"a": 4, "b": 4}, engine="python")
n = equivalent(f, g, {"a": 4, "b": 4}, engine="native")
print("proof_steps", p.proof_steps, n.proof_steps, "| conflicts", p.conflicts, n.conflicts,
      "| checked", p.proof_checked, n.proof_checked)
```

## Actual output

```
proof_steps 413 337 | conflicts 112 112 | checked True True
```

## What it should be

`tests/test_pyeq.py:442-457` documents it: the contract is "every proof verifies", not "every proof
matches". README and AGENTS.md scope bit-exactness to conflicts, decisions and propagations.

## Suspected cause

`cdclkit/solver.py:518-522` logs a root-strengthened input clause as an addition; the Rust engine does not.

## Engines

Differs by engine, by design.

## Fix

Nothing to fix. A line in `EquivalenceResult`'s `proof_steps` comment would stop a reader comparing them.

## Proposed test

This one passes: it pins the documented contract, since there is no bug to fail on.

```python
import unittest

from cdclkit.pyeq import equivalent


class TestProofStepsAcrossEngines(unittest.TestCase):
    def test_the_same_search_and_two_valid_proofs(self):
        def f(a, b): return a * b
        def g(a, b): return b * a
        p = equivalent(f, g, {"a": 4, "b": 4}, engine="python")
        n = equivalent(f, g, {"a": 4, "b": 4}, engine="native")
        self.assertEqual(p.conflicts, n.conflicts)
        self.assertTrue(p.proof_checked and n.proof_checked)
```
