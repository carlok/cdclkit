# cdclkit

**A conflict-driven clause-learning SAT solver, a preprocessor, an encoding
library and a modelling layer — written from scratch in readable Python.**

Every answer comes with a certificate, and the certificate gets checked.

```bash
pip install cdclkit              # pure Python
pip install "cdclkit[native]"    # plus the Rust engine, ~18x faster
```

Three packages, and no third-party code:
[`cdclkit`](https://pypi.org/project/cdclkit/),
[`dratify`](https://pypi.org/project/dratify/) (the proof checker, zero
dependencies), and optionally
[`cdclkit-native`](https://pypi.org/project/cdclkit-native/) (abi3 wheels for
Linux and macOS).

```bash
python3 -m cdclkit solve instance.cnf --self-check --check-model
```

- **SAT** → the model is re-evaluated against the input formula, clause by clause.
- **UNSAT** → the solver emits a DRAT proof and [`dratify`](https://github.com/carlok/dratify)
  replays it, confirming every derived clause really follows and the empty
  clause is reached.

A solver that says "unsatisfiable" and offers nothing else is asking to be
trusted. This one hands you the proof — and the checker that reads it shares no
code with the solver that wrote it.

## Quick start

```python
from cdclkit import parse_dimacs, solve

formula = parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n")
sat, model = solve(formula)
print(sat)          # False -- and `solve` returns (False, None)
```

Note the shape: `solve()` returns a **tuple**, so `if solve(f):` is always
true. Unpack it.

Worked examples live in `examples/` — Sudoku with a uniqueness proof, the zebra
puzzle, graph colouring, bounded model checking, circuit equivalence.

## What's in it

| module | what it does |
|---|---|
| `solver` | CDCL: two watched literals, first-UIP learning, LBD, Luby restarts, phase saving, target phases, probSAT rephasing |
| `preprocess` | subsumption, self-subsumption, blocked-clause elimination, pure literals, bounded variable elimination with model reconstruction |
| `encodings` | at-most-one (pairwise, binary, commander), cardinality (sequential, totalizer), pseudo-Boolean |
| `model` | a modelling layer — integer variables, all-different, differential encoding |
| `mus` | minimal unsatisfiable subsets, deletion-based and QuickXplain |
| `portfolio` | parallel configurations |
| `pyeq` | **experimental** — bounded equivalence of two Python integer functions |

An optional Rust engine ([`cdclkit-native`](https://pypi.org/project/cdclkit-native/))
is roughly 18x faster
and **bit-exact** with the Python one: identical conflicts, decisions and
propagations on every instance. The pure-Python path has zero third-party
dependencies and is the one that must never break.

## Relationship to dratify

Proof checking lives in a separate package,
[`dratify`](https://pypi.org/project/dratify/)
([source](https://github.com/carlok/dratify), also a
[Rust crate](https://crates.io/crates/dratify)), which `cdclkit` depends on.
That split is deliberate:

- You should not have to install a SAT solver to verify a proof someone else
  produced.
- The checker stays small enough to audit, which is the point of a checker.
- `cdclkit` exercises it on every test run, so the checker is dogfooded by the
  solver rather than only by its own suite.

`dratify` has no dependencies of its own, so installing `cdclkit` pulls in no
third-party code. With `[native]`, `cdclkit-native` hands its compiled checker
to `dratify` through `register_native()`, so proof checking gets the Rust
implementation too rather than only the solver.

## Performance

See [BENCHMARKS.md](BENCHMARKS.md). Read the caveats there before quoting any
number — in particular, all figures come from a single machine, and the
comparison against `kissat` is against its default configuration on a public
benchmark suite whose instances are small enough that process startup is part
of what is being measured.

If you need raw speed, install [PySAT](https://pypi.org/project/python-sat/):
it ships kissat, CaDiCaL and Glucose as binary wheels on every platform. This
project is not trying to beat them. It is trying to be a complete, readable,
self-checking implementation you can audit.

## Honest limitations

- **No Windows.** Never tested; the classifiers say so rather than implying support.
- Pure Python is ~18x slower than its own Rust port, which is itself far from
  kissat. Not a tool for competition-scale instances.
- No inprocessing, no XOR/Gaussian reasoning. Parity families are a known
  weakness and `bench/` includes one to keep that visible.
- `pyeq` models a small subset of Python and is **experimental**. Measured
  against CrossHair on a 48-function corpus it found nothing CrossHair missed
  (0 of 105). See `experiments/pyeq-llm-refactor/report.md` for the full
  negative result.
- Every performance figure comes from one machine.

## Documentation

- [docs/tutorial/](docs/tutorial/) — **start here if you are new to SAT.** A
  tutorial for a working programmer who knows boolean logic and has never used
  a solver: the theory you need, then Python, then Rust. Every example runs.
- [docs/ALGORITHMS.md](docs/ALGORITHMS.md) — the mathematics, from resolution
  through first-UIP, LBD, DRAT, encodings and preprocessing, including a
  section on what is deliberately absent.
- [docs/ROADMAP.md](docs/ROADMAP.md) — what is planned, in sprints.
- [docs/RELEASING.md](docs/RELEASING.md) — the release checklist.

## Licence

Apache-2.0. See [LICENSE](LICENSE).
