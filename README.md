# cdclkit

**A conflict-driven clause-learning SAT solver, a preprocessor, an encoding
library and a modelling layer — written from scratch in readable Python.**

Every answer comes with a certificate, and the certificate gets checked.

```bash
pip install cdclkit              # pure Python
pip install "cdclkit[native]"    # plus the Rust engine, ~20x faster
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

## Why you would want this

**Use this if:**

- ✅ You have constraints and need any assignment satisfying all of them
- ✅ You need to know **why** something is infeasible, not just that it is
- ✅ You need to *verify* an "impossible" answer rather than trust it
- ✅ You want to read the solver, or teach how CDCL works
- ✅ You want zero third-party dependencies

**Use something else if:**

- ❌ You need raw speed on industrial instances → [PySAT](https://pypi.org/project/python-sat/) ships kissat and CaDiCaL
- ❌ Your problem is numeric optimisation over real numbers → an LP or MIP solver
- ❌ You need Windows → never tested here, and the classifiers say so

---

You have a pile of constraints and need any assignment satisfying all of them:

- **Rostering and scheduling** — six nurses, three shifts, nobody works two
  nights running, everyone gets a weekend off a month.
- **Configuration** — which package versions can coexist, which hardware
  options are compatible.
- **Assignment** — exams to rooms and slots with no clashes, frequencies to
  transmitters that must not interfere.
- **Puzzles** — Sudoku, nonograms, the zebra puzzle. Genuinely the same shape
  as the three above.

The alternative is writing backtracking search yourself. That is slow to write,
and what you produce in an afternoon will be far slower than a solver with
thirty years of engineering in the same loop.

Two things you get that a hand-rolled search does not:

- **When there is no solution, you learn why.** A minimal unsatisfiable subset
  names the handful of constraints that actually conflict, instead of reporting
  "infeasible" and leaving you to bisect a thousand of them.
- **When it says "no", you can check it.** A "yes" verifies itself in linear
  time; a "no" is an assertion about every one of 2^n assignments. This one
  hands you a proof.

**When not to.** Numeric optimisation over real numbers wants an LP or MIP
solver, not this. Raw throughput on millions of clauses wants
[PySAT](https://pypi.org/project/python-sat/), which ships kissat and CaDiCaL
as binary wheels and will be much faster.

New to this? [docs/tutorial/](docs/tutorial/) starts from boolean logic and
assumes nothing else.

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
puzzle, graph colouring, bounded model checking, circuit equivalence, and
checking a refactored Python function against the original.

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
is **bit-exact** with the Python one — identical conflicts, decisions and
propagations on every instance — and about **20x faster**: the geometric mean
of per-instance ratios over the 17 benchmark instances is 20.1x, ranging from
11x to 51x. Regenerate it with `make history` (the `python` and `native`
checkpoints in `bench/history.jsonl`); see [BENCHMARKS.md](BENCHMARKS.md) for
the method. The pure-Python path has zero third-party
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
project is not trying to beat them, and will lose badly on large instances.

The difference worth naming is narrower than "readable": PySAT can emit DRUP
proofs and ships nothing to check them, and its solvers are third-party C++ in
a compiled extension. Here the proof gets checked by default, by a package you
can read. That matters if you are about to act on "no solution exists", and not
otherwise.

## Honest limitations

- **No Windows.** Never tested; the classifiers say so rather than implying support.
- Pure Python is ~20x slower than its own Rust port, which is itself far from
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

## Generating code against this?

[AGENTS.md](AGENTS.md) lists the API's sharp edges — the mistakes that have
actually been made, not hypothetical ones. Worth reading before writing a line.

## Licence

Apache-2.0. See [LICENSE](LICENSE).
