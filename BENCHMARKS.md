# Benchmarks

**Read this section before quoting anything below.**

Every figure here was measured on **one machine**. Nothing has run on a second
host, and nothing has run on SAT Competition instances. A number measured once,
on one laptop, against one competitor configuration, is a data point and not a
ranking.

The comparison against `kissat` in particular deserves scepticism:

- It is against kissat's **default** configuration. `kissat --sat` beats the
  pre-walk configuration here by 1.28x on satisfiable random instances.
- SATLIB instances are small. At these sizes a meaningful share of a modern
  solver's wall time is process startup and preprocessing, not search. The
  harness subtracts measured startup, which helps and does not eliminate this.
- PySAT ships kissat 4.0.4 as a binary wheel, so anyone can reproduce this in
  about ten minutes. That is a feature — but assume they will.

If you want the fastest solver, use kissat or CaDiCaL. This project is a
readable, self-checking, auditable implementation. Speed is not its claim.

## Method

Rules the harness enforces, each learned from getting it wrong first:

- **Geometric mean of per-instance ratios**, never a sum of wall times. One
  heavy-tailed random instance faked a large win three separate times in this
  project's history.
- **`--repeat 3` minimum**, with the run-to-run spread reported alongside. A
  difference smaller than the spread is noise; kissat's own speed varied 35%
  between two runs of the same binary here.
- **No per-run absolute-time exclusion.** An earlier rule dropped anything the
  competitor solved in under 50 ms, which moved half a family in and out of the
  sample — dropping exactly the instances where the competitor was fastest.
- **No comparison on instances both solvers failed.** The ratio is 1.0 by
  construction and dilutes toward parity while measuring nothing.
- **Holdout reported separately.** Configurations are chosen against the tune
  families; only the holdout families say whether that generalised, and
  `bench/sweep.py` refuses to load them so it stays that way.
- **Run under `caffeinate -i`, alone.** A suspended host and a concurrent build
  have each corrupted a run here, and both look like a hard instance afterwards.

Corpus: 344 public SATLIB instances across 18 families, 11 of them holdout.
Ground truth is threefold — the `uf`/`uuf` family convention, a brute-force
oracle below ~12 variables, and agreement among five installed solvers.

## Against kissat (default configuration)

Geometric mean of per-instance ratios, lower is better for cdclkit:

| group | ratio |
|---|---|
| tune families | 0.26 |
| holdout families | 0.21 |

The holdout number being *better* than the tune number is the result worth
having: the configuration was chosen against random 3-SAT and generalised to
planning, circuit fault analysis, parity and all-interval series, which it had
never been measured against.

## Where it loses

Stated because a benchmark section that only lists wins is marketing.

- **MiniSat beats it 1.55x** single-threaded.
- **`kissat --sat` beats the pre-walk configuration 1.28x** on satisfiable
  random instances.
- **Parity families are exponential** for resolution without XOR reasoning,
  which this does not have. `bench/` includes a parity family specifically to
  keep that visible.
- The portfolio's speedup comes from running more searches, not from one faster
  search.

## Python against Rust

The Rust engine is **bit-exact** with the Python one — identical conflicts,
decisions and propagations — and about **20x faster**: geometric mean 20.1x of
per-instance ratios over 17 instances, spread 11x to 51x. Both are complete
implementations; the Rust is a port, not a core with bindings.

The figure comes from the `python` and `native` checkpoints in
`bench/history.jsonl`, recorded 34 seconds apart at the same commit on one
machine against the same competitors; `make history` prints them. It is one
sample per instance, so treat the geometric mean as the result and any single
ratio as an illustration — in the sibling project's harness, individual ratios
moved by a third between runs while the mean held to within 0.2x. A sum of wall times
over the same data gives 22.5x, which is why this document quotes the geometric
mean instead — see the rules in `docs/RELEASING.md`.

## Proof checking

Proof checking now lives in [`dratify`](https://github.com/carlok/dratify), and
its numbers are in that repository, reproducible with `python bench/repro.py`
there. Summary: the Rust checker averages roughly 15x over pure Python (per-run
geometric mean; individual instances range 11x-22x and move between runs),
growing with proof size, and is slower than `drat-trim` because it checks
*forward*
against drat-trim's backward checking — it verifies every step, including the
ones a backward pass never visits.

## Reproducing

```bash
python3 bench/fetch_satlib.py
caffeinate -i python3 bench/compare.py --repeat 3 --group all
```

`bench/baseline.json` is the conflict-count reference the harness checks
against, so a regression in search behaviour shows up as a diff rather than as
a timing wobble.
