# mus-3: `cdclkit mus --method core --verify` exits 1 on a correct core

**Proposed severity: Note.** The behaviour matches the `--verify` help text, which says
it checks "that the result is unsatisfiable and minimal", and `core()`'s docstring says
"Not minimal". So nothing contradicts the documentation, and the core returned is correct.
It is recorded because exit 1 means "error" (AGENTS.md), and the run prints neither the
clauses nor an `s` line for a formula it has just shown to be unsatisfiable.
`gen_mus` expects this behaviour and counts it as `cli_core_verify_not_minimal`.

## Minimal case

Removing any clause or literal stops the core being larger than the MUS, so the run no
longer exits 1.

```
$ printf 'p cnf 3 5\n2 -1 0\n-3 -2 0\n1 2 0\n-2 1 0\n3 -2 0\n' > core.cnf
$ python -m cdclkit.cli mus core.cnf --method core --verify; echo "exit $?"
c core: 5 of 5 clauses, 1 solver calls, 0.000s
c clause 3 is redundant: the rest is still unsatisfiable
exit 1
$ python -m cdclkit.cli mus core.cnf --method core; echo "exit $?"
c core: 5 of 5 clauses, 1 solver calls, 0.000s
c   clause 0: 2 -1 0
c   clause 1: -3 -2 0
c   clause 2: 1 2 0
c   clause 3: -2 1 0
c   clause 4: 3 -2 0
s UNSATISFIABLE
exit 20
```

## What the oracle says

```python
F = [[2, -1], [-3, -2], [1, 2], [-2, 1], [3, -2]]
oracle.satisfiable(F)                                   # False: the answer is unsatisfiable
oracle.satisfiable([c for c in F if c != [-2, 1]])      # False: clause 3 is indeed redundant
```

The message is true and the core is a correct unsatisfiable core. Only the exit status
and the missing output are in question.

## Suspected cause

`cdclkit/cli.py:330-334` applies `ex.verify`, which tests minimality, to every method,
and returns `EXIT_ERROR` on any failure. For `core`, the only meaningful half of `verify`
is "unsatisfiable". Python only; there is no native MUS path.

**Fix:** a choice for the author, not a clear bug fix. Either keep it and say so in the
help text, or have `--method core --verify` check only unsatisfiability and exit 20.

## Proposed test

Only if the author takes the second option:

```python
def test_verify_on_a_core_does_not_demand_minimality(self):
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "core.cnf")
        with open(path, "w") as fh:
            fh.write("p cnf 3 5\n2 -1 0\n-3 -2 0\n1 2 0\n-2 1 0\n3 -2 0\n")
        self.assertEqual(main(["mus", path, "--method", "core", "--verify"]), 20)
```
