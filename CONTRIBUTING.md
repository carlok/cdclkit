# Contributing

## Running things

The one runtime dependency is [`dratify`](https://github.com/carlok/dratify),
the proof checker. Without it the suite stops with import errors.

```bash
pip install dratify        # or: pip install -e .
make test                  # the full suite, no Rust needed
make coverage              # statement coverage, floor 72%
make gate                  # tests, examples, and the conflict baselines
```

`make gate` is what CI runs, and it is what to run before opening a PR.

The Rust engine is optional and must be bit-exact with the Python one:

```bash
make native                # build it into .venv (needs cargo)
make test-native           # the same suite against it
cd native && cargo test --release --no-default-features
cd native && cargo clippy --all-targets -- -D warnings
```

## What a change needs

**A test that fails without it.** For a bug fix, write the test first and watch
it fail. This matters more here than usual: several past "fixes" in this
repository were verified by tests that passed before the change too.

**Both engines, if you touch the search.** `cdclkit/solver.py` and
`native/src/solver.rs` must produce identical conflicts, decisions and
propagations on every instance. `tests/test_native_solver.py` compares eleven
counters; a change to one engine without the other will show up there.

**The baseline, if you touch the heuristics.** `make gate` compares conflict
counts against `bench/baseline.json`. Those counts are deterministic, so a
change is either intended — rerecord it and say why in the commit — or a bug.
CI runs this too.

**Numbers regenerated, not edited.** Any performance figure must be a geometric
mean of per-instance ratios from one session on one machine, never a sum of
wall times. `docs/RELEASING.md` has the full rules, each of which exists
because ignoring it produced a wrong conclusion here at least once.

## What goes where

- `solver`, `preprocess`, `encodings`, `model`, `mus`, `portfolio` — the toolkit.
- `pyeq` — experimental, and labelled that way. Bounded equivalence of two
  Python integer functions.
- `lits`, `cnf`, `proof` — **not here.** They live in `dratify`, which this
  package depends on. Changes to the literal encoding, the DIMACS parser or the
  checker belong in that repository.

Semantic versioning applies to the names in `cdclkit/__init__.__all__` and
nothing else; `pipeline`, `portfolio` and `native` are internal.

## Reporting a vulnerability

See [SECURITY.md](SECURITY.md). Do not open a public issue for one.
