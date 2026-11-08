# engines-6: `--adaptive` and `-j N` ignore `--conflicts`

**Proposed severity: Bug.** CHANGELOG 0.1.3 lists `--conflicts` among the flags
`--adaptive` ignored and describes the fix, and the current code still drops it. AGENTS.md
ties exit 0 to "a conflict budget that ran out". The answer given is correct, so it is not
Critical, but a caller who sets a budget gets an unbounded run.

## Minimal case

```sh
printf 'p cnf 6 9\n1 2 0\n3 4 0\n5 6 0\n-1 -3 0\n-1 -5 0\n-3 -5 0\n-2 -4 0\n-2 -6 0\n-4 -6 0\n' > /tmp/php.cnf
python -m cdclkit solve /tmp/php.cnf --conflicts 0              # s UNKNOWN, exit 0
python -m cdclkit solve /tmp/php.cnf --conflicts 0 --adaptive   # s UNSATISFIABLE, exit 20
python -m cdclkit solve /tmp/php.cnf --conflicts 0 -j 2         # s UNSATISFIABLE, exit 20
```

The plain run shows what the flag means. Removing clauses is irrelevant: any formula that
needs a conflict shows it.

## Suspected cause

`args.conflicts` is read only at `cdclkit/cli.py:193`, the plain path. `solve_adaptive`
and `solve_portfolio` take no conflict budget at all, so this needs a parameter, not only
wiring. Engine-independent.

In the same family, not counted as separate findings:
- `--prep-rounds` does nothing under `--adaptive` (`pipeline.py` always runs 3).
- `-j N` drops every search flag (`cli.py` calls `solve_portfolio` with no configs).
- `solve_adaptive(jobs>1, config=...)` drops the config (`pipeline.py:243`).

The docs do not claim otherwise for the last two, but nothing says so either.

## Proposed test

```python
class TestConflictBudgetEverywhere(unittest.TestCase):
    PHP = "p cnf 6 9\n1 2 0\n3 4 0\n5 6 0\n-1 -3 0\n-1 -5 0\n-3 -5 0\n-2 -4 0\n-2 -6 0\n-4 -6 0\n"

    def test_a_budget_of_zero_is_unknown_on_every_path(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "php.cnf")
            with open(path, "w") as fh:
                fh.write(self.PHP)
            for flags in ((), ("--adaptive",), ("-j", "2")):
                with self.subTest(flags=flags):
                    out = subprocess.run(
                        [sys.executable, "-m", "cdclkit", "solve", path,
                         "--conflicts", "0", *flags], capture_output=True, text=True)
                    self.assertEqual(out.returncode, 0)
```
