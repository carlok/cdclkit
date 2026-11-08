# engines-8: the empty clause crashes both preprocessors, so `--preprocess -j 2` dies on UNSAT

**Proposed severity: Bug.** Same root as `preprocess-2`. What this corner adds is the
engine split and an ordinary route to it: no empty clause in the input is needed, because
`--preprocess` produces one when it refutes the formula. No wrong answer is given.

## Minimal cases

```sh
printf 'p cnf 1 2\n1 0\n-1 0\n' > /tmp/c.cnf
python -m cdclkit solve /tmp/c.cnf --preprocess -j 2                        # exit 1, panic
CDCLKIT_ENGINE=python python -m cdclkit solve /tmp/c.cnf --preprocess -j 2  # exit 20
python -m cdclkit solve /tmp/c.cnf -j 2                                     # exit 20
```

Native prints:

```
thread '<unnamed>' panicked at src/preprocess.rs:274:18:
called `Option::unwrap()` on a `None` value
pyo3_runtime.PanicException: called `Option::unwrap()` on a `None` value
```

So the engine changes the outcome: 20 on Python, a crash on native. The oracle:
`oracle.satisfiable([[1], [-1]])` is False, and 20 is right.

In the library, with the empty clause in the input:

```python
from cdclkit import parse_dimacs
from cdclkit.pipeline import solve_adaptive
from cdclkit.portfolio import solve_portfolio
f = parse_dimacs("p cnf 1 1\n0\n")
solve_adaptive(f.copy(), engine="python", always_preprocess=True)  # ValueError: min() iterable argument is empty
solve_adaptive(f.copy(), engine="native", always_preprocess=True)  # PanicException
solve_portfolio(f.copy(), jobs=2)                                  # PanicException
```

The default `solve_adaptive` path is safe, because the probe answers first.

## Suspected cause

- `cdclkit/preprocess.py:267`: `min(c, ...)` with an empty `c`.
- `native/src/preprocess.rs:274`: the same with `.unwrap()`.
- `cdclkit/portfolio.py:470`: `except Exception` is there to make preprocessing failure
  non-fatal, and it does not catch pyo3's `PanicException`, which derives from
  `BaseException`. The Python process path survives because its exception is a `ValueError`,
  caught at `portfolio.py:288`.

The fix looks clear: both `run` loops should treat an empty clause as `unsat`.

## Proposed test

```python
class TestEmptyClauseThroughPreprocessing(unittest.TestCase):
    def test_both_engines_answer_unsat(self):
        for engine in ("python", "native"):
            with self.subTest(engine=engine):
                f = parse_dimacs("p cnf 1 1\n0\n")
                r = solve_adaptive(f, engine=engine, always_preprocess=True)
                self.assertIs(r.sat, False)
```
