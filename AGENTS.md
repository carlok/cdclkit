# Notes for coding agents

Everything here is a mistake that has actually been made against this API, not
a hypothetical. If you are generating code that uses `cdclkit`, read this
first; it is shorter than debugging the same four things again.

## `solve()` returns a tuple

```python
sat, model = solve(formula)      # correct
if solve(formula): ...           # ALWAYS TRUE - a 2-tuple is truthy
```

`solve(formula, proof=None, config=None)` returns `(True, model)` or
`(False, None)`. `model` is a list of booleans indexed by variable number minus
one.

## Internal literals are non-negative

DIMACS uses signed integers. This library does not. Variable `v` has literals
`2v` (positive) and `2v + 1` (negated), because that makes array indexing
direct in the solver's hot loops.

```python
enc.add([neg(a), neg(b)])        # correct
enc.add([-a, -b])                # ValueError: internal literals are non-negative
```

Use `from_dimacs()` / `to_dimacs()` to convert signed input, and `neg()` to
negate. This is the single most common error.

## Prefer the modelling layer

For most problems do not touch literals at all:

```python
from cdclkit.model import Model
m = Model()
x = m.int_var(range(1, 5), "x")
m.all_different([x, y, z])
m.add(x == 3)
sol = m.solve()                  # Solution or None
sol.value(x)
```

Drop to `Encoder` when you need a constraint it does not offer
(`exactly_one`, `at_most_k`, `assert_pb_leq`, Tseitin gates), and to raw
clauses almost never.

## `pyeq.proved` is three-valued

`True`, `False`, or `None` when the conflict budget ran out. `None` is falsy,
so `if result.proved:` silently treats "undecided" as "differs". Test
`is True` / `is False` / `is None` explicitly. `pyeq` is **experimental** — see
the 0/105 result in `experiments/pyeq-llm-refactor/report.md` before building
on it.

## CLI exit codes are not 0

SAT competition convention: `10` satisfiable, `20` unsatisfiable, `30` proof
rejected, `1` error. A shell script expecting `0` will read success as failure.

## The native engine is opt-in

`pip install "cdclkit[native]"`. It is never selected implicitly for solving —
a caller asks for it (`engine="native"`, or `CDCLKIT_ENGINE=native`). It is
bit-exact with the Python engine: identical conflicts, decisions and
propagations, and there are tests that fail if that drifts.

Proof *checking* is the exception: installing the extra registers the Rust
checker with `dratify`, so `engine="auto"` starts using it. That is a pure
speedup, not a behaviour change.

## Where to look

- `docs/tutorial/` — start here if the task involves explaining SAT to someone.
- `examples/` — six worked programs, all runnable.
- `docs/ALGORITHMS.md` — the mathematics, including what is deliberately absent.
- `BENCHMARKS.md` — performance, with the caveats that belong to each number.
