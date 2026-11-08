# engines-9: a configuration one engine takes, the other refuses

**Proposed severity: Bug**, a minor one, under "the engines disagree". AGENTS.md says the
engine changes the speed and never the answer, and here it changes whether there is an
answer. None of this gives a wrong verdict.

## Minimal cases

```python
from cdclkit import Config, parse_dimacs
from cdclkit.pipeline import solve_adaptive
from cdclkit.portfolio import solve_portfolio
f = parse_dimacs("p cnf 1 1\n1 0\n")
for kw in (dict(rnd_seed=2**32 + 1), dict(rnd_seed=-1), dict(glue_keep=-1),
           dict(restart="bogus"), dict(ccmin="bogus")):
    for engine in ("python", "native"):
        try:
            print(kw, engine, solve_adaptive(f.copy(), engine=engine, config=Config(**kw)).sat)
        except Exception as e:
            print(kw, engine, type(e).__name__)
print(solve_adaptive(f.copy(), engine="quantum").sat)          # True, on Python, silently
solve_portfolio(f.copy(), jobs=1, engine="quantum")            # ValueError
```

Actual: every Python run prints `True`. Native raises `OverflowError` on the three numeric
cases and `ValueError` on the two names.

A seed at or above 2^32 is the case that matters, since `--seed` takes any int:
`cdclkit solve f --adaptive --seed 4294967297` is fine on Python and raises on native.
Python's xorshift masks to 32 bits only after its first step, so masking the seed on the
native side would not by itself reproduce the Python stream. Seeds inside u32, including 0
and 2^32-1, were bit-exact in the run.

`restart="bogus"` on Python silently means Glucose restarts (`cdclkit/solver.py:1168`, the
fall-through), so the typo goes unnoticed. Native's refusal is the better behaviour.

## Suspected cause

- `native/src/lib.rs:89,92`: `glue_keep: u32`, `rnd_seed: u32`.
- `cdclkit/solver.py:166`, `Config.__init__`, validates names and no values.
- `cdclkit/pipeline.py:194`: `solve_adaptive` tests only for `"native"`, and anything else
  is Python. `solve_portfolio` raises, at `portfolio.py` near its first line.

The fix is clear: validate in `Config` and in `solve_adaptive`, for both engines.

## Proposed test

```python
class TestConfigAcceptance(unittest.TestCase):
    def test_config_is_validated_before_either_engine_sees_it(self):
        with self.assertRaises(ValueError):
            Config(restart="bogus")

    def test_solve_adaptive_refuses_an_unknown_engine(self):
        with self.assertRaises(ValueError):
            solve_adaptive(parse_dimacs("p cnf 1 1\n1 0\n"), engine="quantum")
```
