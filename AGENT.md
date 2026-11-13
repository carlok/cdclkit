# Notes for agents changing this repository

This file is for **coding agents and contributors** who edit `cdclkit` itself.
For API pitfalls when *using* the solver from generated code, read
[AGENTS.md](AGENTS.md) instead. Humans may also use [CONTRIBUTING.md](CONTRIBUTING.md).

## Setup

Python 3.10 or newer. The only runtime dependency is
[`dratify`](https://github.com/carlok/dratify) (also pulled in by an editable
install):

```bash
pip install dratify
# or, from the repository root:
pip install -e .
```

Optional: the Rust engine (`pip install "cdclkit[native]"` or `make native`) and
a reference SAT solver on `PATH` for `make gate` — see CONTRIBUTING.md.

## Before each commit

Run the suite and coverage. Coverage is slow (~20× a normal test run); still run
it when you change `cdclkit/` or tests.

```bash
python -m unittest discover -s tests -v
python tests/coverage_report.py
# same check as CI (use the floor documented in coverage_report.py):
python tests/coverage_report.py --min 75
```

**Always try to increase test coverage** when you add or change behaviour. Do
not lower the coverage floor to make CI green — add tests instead.

**Never commit** API keys, tokens, credentials, or machine-specific paths,
hostnames, or usernames. Keep user-facing docs and comments **general** (no
“on my laptop”, no private URLs).

For a substantial PR, `make gate` matches much of what CI runs (tests,
baselines, agreement with a reference solver). CI also runs lint, examples,
packaging, and the native matrix — see `.github/workflows/ci.yml`.

## Scope

Do not refactor unrelated product code. Do not change the licence. Changes to
literal encoding, DIMACS I/O, or the proof checker belong in
[`dratify`](https://github.com/carlok/dratify), not here.

## Conduct and templates

Follow [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md). Use the GitHub issue and pull
request templates when opening work on the forge.
