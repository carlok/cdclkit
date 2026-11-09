# preprocess-1: `solve --preprocess --adaptive` prints an unreconstructed model

**Proposed severity: Critical.** The brief's definition is "cdclkit returns a wrong
SAT model". It also meets the Bug line "a preprocessed model does not satisfy the
original formula".

## Minimal case

The formula is the single unit clause `(x1)`. Removing the clause leaves a formula no
assignment can falsify, so the case is minimal.

```sh
printf 'p cnf 1 1\n1 0\n' > d.cnf
cdclkit solve d.cnf --preprocess --adaptive
```

Actual output, ending:

```
c 0 conflicts in 0.000s
s SATISFIABLE
v -1
v 0
```

Exit status 10. The printed model sets `x1` false, which falsifies the only clause.
Same output with `CDCLKIT_ENGINE=python` and with `CDCLKIT_ENGINE=native`.

With `--check-model` the same input reports a failure on a satisfiable formula:

```
c MODEL CHECK FAILED
```

Exit status 1. So the check catches the wrong model, but nothing else does, and it is off by
default.

## What the oracle says

```python
from campaign import oracle
oracle.satisfiable([[1]])                 # True: the verdict is right
model = [False]                           # what the CLI printed
any(model[abs(l) - 1] == (l > 0) for c in [[1]] for l in c)   # False: the model is wrong
```

`python -m campaign.gen_preprocess` labels this `cli-model-wrong` (printed model judged
by the harness) and `cli-exit-code-wrong` (exit 1 where 10 is right).

## Suspected cause

`cdclkit/cli.py`. Line 108 replaces `f` with the reduced formula when `--preprocess`
is set. The `--adaptive` branch then solves that reduced formula (`solve_adaptive`, line
141) and uses `pr.model` directly at lines 153 and 159, without `pre.reconstruct`. The
non-adaptive path does call it, further down: `model = pre.reconstruct(model)`.

`solve_adaptive` reconstructs its *own* preprocessing correctly. The missing step is
the outer `Preprocessor` from the CLI, which `solve_adaptive` cannot know about. So the
library is unaffected and both engines are, because the bug is in the shared CLI branch.

The fix looks clear: in the adaptive branch, apply `pre.reconstruct` to `pr.model` when
`pre is not None`, before the model check and before printing. Refusing the flag
combination would also be honest. UNSAT answers on this route are fine: their proof
was replayed against the original and passed.

## Proposed test

For `tests/test_adaptive_proof.py`, in its CLI style:

```python
class TestPreprocessThenAdaptive(unittest.TestCase):
    def test_the_printed_model_satisfies_the_input(self):
        """--preprocess reduces the formula before --adaptive sees it, so the
        adaptive branch has to reconstruct too."""
        with tempfile.TemporaryDirectory() as d:
            path = pathlib.Path(d) / "f.cnf"
            path.write_text("p cnf 1 1\n1 0\n")
            r = subprocess.run(
                [sys.executable, "-m", "cdclkit", "solve", str(path),
                 "--preprocess", "--adaptive"],
                capture_output=True, text=True)
        self.assertEqual(r.returncode, 10, r.stdout)
        values = [int(t) for line in r.stdout.splitlines()
                  if line.startswith("v ") for t in line[2:].split()]
        self.assertIn(1, values, r.stdout)
```
