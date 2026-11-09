# preprocess-2: the empty clause crashes both preprocessors

**Proposed severity: Bug.** No wrong answer is given, so it is not Critical. But the
input is valid, the answer is simply UNSAT, and the run ends with an exception and no
verdict. `CNF.add` documents that "The empty clause is kept", and the preprocessor
itself returns one as its UNSAT result, so it can be fed its own output.

## Minimal cases

The formula with only the empty clause, in the library:

```python
from dratify.cnf import CNF
from cdclkit.preprocess import Preprocessor
from cdclkit import native

f = CNF(1); f.add([])
Preprocessor(f).run()              # ValueError: min() iterable argument is empty

p = native.require().Preprocessor(1)
p.add_clause([])
p.run(3)                           # PanicException: called `Option::unwrap()` on a `None` value
```

A panic is a `BaseException`, so `except Exception` does not stop it.

The route that needs no empty clause in the input, only two contradictory units:

```sh
printf 'p cnf 1 2\n1 0\n-1 0\n' > g.cnf
cdclkit solve g.cnf --preprocess -j 2
```

Actual output, ending:

```
    p.run(3)
    ~~~~~^^^
pyo3_runtime.PanicException: called `Option::unwrap()` on a `None` value
```

Exit status 1, no `s` line. Expected `s UNSATISFIABLE`, exit 20, which is what
`solve g.cnf --preprocess` and `solve g.cnf --preprocess -j 2 --self-check` give. The
second works only because a proof run forces `preprocess_workers = 0`.

Other routes, all run:

| call | result | right answer |
|---|---|---|
| `solve_adaptive(f, engine="python", always_preprocess=True)` | ValueError | `sat=False` |
| `solve_adaptive(f, engine="native", always_preprocess=True)` | PanicException | `sat=False` |
| `solve_portfolio(f, jobs=2, engine="native", preprocess_workers=1)` | PanicException | `sat=False` |
| `cdclkit solve e.cnf --preprocess`, where e.cnf is `p cnf 1 1` / `0` | `c error: min() iterable argument is empty`, exit 1 | exit 20 |
| `cdclkit prep e.cnf` | same error, exit 1 | a reduced formula |
| `cdclkit solve e.cnf -j 3` | PanicException traceback | exit 20 |
| `Preprocessor(red).run()` where `red` is the result of an UNSAT `Preprocessor.run` | ValueError | still UNSAT |

The same inputs work with `never_preprocess=True`, with the default probe (which
refutes first), with `solve e.cnf --adaptive`, and with the Python portfolio, whose
worker catches the exception.

## What the oracle says

```python
from campaign import oracle
oracle.satisfiable([[]])           # False
oracle.satisfiable([[1], [-1]])    # False
```

## Suspected cause

`subsume` picks the rarest literal of each clause without allowing for a clause
having none:

- `cdclkit/preprocess.py:267`, `best = min(c, key=...)`
- `native/src/preprocess.rs:271-274`, `.min_by_key(...).unwrap()`

`propagate` and `to_cnf` both let an empty clause through, and `self.unsat` is not set
for one in the input. `tests/test_preprocess.py::test_preprocessing_is_idempotent_enough`
skips the case with `if pre1.unsat: continue`, which is how it stayed hidden.

`cdclkit/portfolio.py:470` is `except Exception`, so the fallback meant for a failing
preprocessor misses a Rust panic. `cdclkit/cli.py:556` turns the Python `ValueError`
into an error that reads as malformed DIMACS.

Both engines are affected. The fix looks clear: at the start of `run`, if any clause
is empty, set `unsat`, log the empty clause, and return. Do it in both. Catching
`BaseException` in the portfolio would hide the cause rather than fix it.

## Proposed test

For `tests/test_preprocess.py`:

```python
class TestEmptyClause(unittest.TestCase):
    def _f(self):
        f = CNF(2)
        f.add([])
        f.add([mk_lit(0), mk_lit(1)])
        return f

    def test_python_reports_unsat(self):
        pre = Preprocessor(self._f())
        red = pre.run()
        self.assertTrue(pre.unsat)
        self.assertIn((), red.clauses)

    def test_a_reduction_can_be_preprocessed_again(self):
        f = CNF(1)
        f.add([mk_lit(0)])
        f.add([neg(mk_lit(0))])
        red, first = preprocess(f)
        self.assertTrue(first.unsat)
        _, second = preprocess(red)
        self.assertTrue(second.unsat)

    @unittest.skipUnless(native.available(), "native engine not built")
    def test_native_reports_unsat(self):
        p = native.require().Preprocessor(2)
        p.add_clause([])
        p.add_clause([0, 2])
        self.assertFalse(p.run(3))
        self.assertTrue(p.unsat)
```

This needs `from cdclkit import native` added to that file's imports.
