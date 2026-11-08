# engines-7: `solve_portfolio` crashes on its own defaults

**Proposed severity: Bug.** The signature says `jobs: int | None = None`, the docstring of
the module says "The default is the performance-core count", and the default raises. It is
a crash and not a wrong answer. `cdclkit.portfolio` is documented as internal, and the CLI
and `solve_adaptive` always pass `jobs`, which is why nothing caught it.

## Minimal cases

```python
from cdclkit import parse_dimacs
from cdclkit.portfolio import solve_portfolio
f = parse_dimacs("p cnf 1 1\n1 0\n")
solve_portfolio(f)                     # TypeError: '>' not supported between 'NoneType' and 'int'
solve_portfolio(f, jobs=2, configs=[]) # RecursionError, after spawning at every level
```

Passing `preprocess_workers=0` gets past the first. Passing a non-empty `configs` avoids the
second.

## Suspected cause

- `cdclkit/portfolio.py:547` computes `jobs * 2 // 5` from `jobs`, and line 555 is where
  `None` becomes the core count. The fix is clear: swap them.
- `configs=[]`: `jobs = min(jobs, len(cfgs))` gives 0, no worker starts, and the fallback at
  line 675 calls itself with `configs=cfgs[:1]`, still empty. The fix is clear: raise
  `ValueError` on empty `configs`.

Engine-independent. Both happen before an engine is chosen.

## Proposed test

```python
class TestPortfolioDefaults(unittest.TestCase):
    def test_jobs_defaults_to_the_core_count(self):
        self.assertIs(solve_portfolio(parse_dimacs("p cnf 1 1\n1 0\n")).sat, True)

    def test_empty_configs_are_refused(self):
        with self.assertRaises(ValueError):
            solve_portfolio(parse_dimacs("p cnf 1 1\n1 0\n"), jobs=2, configs=[])
```
