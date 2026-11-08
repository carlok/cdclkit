# engines-5: `solve --preprocess --adaptive` prints a model that falsifies the input

**Proposed severity: Critical.** The brief: "cdclkit returns a wrong SAT model". Same bug
as `preprocess-1`, reached independently here by the CLI round robin, on both engines.

## Minimal case

```sh
printf 'p cnf 1 1\n1 0\n' > /tmp/u.cnf
python -m cdclkit solve /tmp/u.cnf --preprocess --adaptive                 # exit 10
python -m cdclkit solve /tmp/u.cnf --preprocess --adaptive --check-model   # exit 1
CDCLKIT_ENGINE=python python -m cdclkit solve /tmp/u.cnf --preprocess --adaptive  # exit 10
python -m cdclkit solve /tmp/u.cnf --preprocess                            # exit 10, right
```

Actual on the first and third:

```
s SATISFIABLE
v -1
v 0
```

The formula is `(x1)`, so `x1=false` falsifies it. The fourth prints `v 1`. The second
says `c MODEL CHECK FAILED`, so `--check-model` catches it, and without that flag nothing
does. `--self-check` does not help: it only checks UNSAT answers.

## Suspected cause

`cdclkit/cli.py:125`, the `--adaptive` branch: `solve_adaptive` solves the reduced formula
and line 159 prints `pr.model`. Only the path below it reconstructs (`pre.reconstruct`, line
202), and the branch returns before reaching that. `solve_adaptive`'s own reconstruction
handles only its own preprocessing. Both engines. The library is not affected. The fix
looks clear: apply `pre.reconstruct` in the branch, before the model check and the print.

## Proposed test

```python
class TestPreprocessAndAdaptive(unittest.TestCase):
    def test_the_printed_model_satisfies_the_input(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "u.cnf")
            with open(path, "w") as fh:
                fh.write("p cnf 1 1\n1 0\n")
            out = subprocess.run(
                [sys.executable, "-m", "cdclkit", "solve", path, "--preprocess", "--adaptive"],
                capture_output=True, text=True)
        self.assertEqual(out.returncode, 10)
        values = [t for l in out.stdout.splitlines() if l.startswith("v ")
                  for t in l[2:].split()]
        self.assertIn("1", values)
```
