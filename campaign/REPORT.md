# Soundness campaign: cdclkit

Tiny formulas and brute force, an oracle that shares no code with this repository
(`campaign/oracle.py`, reviewed by a second agent), a small DPLL for encodings past 16 variables
(`campaign/dpll.py`), and one seeded generator per corner.

**Seven Critical defects were found and fixed on this branch, none yet released.** Since Critical
findings appeared, no README sentence is proposed.

## Corners

Numbers are from the final run after the fixes, recorded in `campaign/results/`. All five generators
and their self-tests exit 0, with no regressions or unexplained mismatches. Reinstating one fixed
bug per corner in a scratch copy made all five fail with REGRESSION. The engines corner needs its
default 300 instances for that: a 40-instance run missed it.

| Corner | Instances | Checks | Seed | Open mismatches at the end |
|---|---:|---:|---|---|
| Encodings | 15,134 | 3,876,255 | 20261108 | none |
| Preprocessing | 600 | 225,475 | 20261108 | preprocess-3 ×103 |
| MUS | 1,003 | 215,989 | 20261108 | none |
| Modelling | 6,000 | 97,059 | 20261108 | none |
| Engines | 300 | 236,463 | 20261108 | engines-1 ×237, engines-2 ×767, engines-3 ×748 |
| **Total** | **23,037** | **4,651,241** | | |

The encodings grid visited 1,551 of 1,551 cells, with 7 sign and order patterns each. Every accepted
cell has exactly the combinatorial solution set, projected on the original variables. `optimise`
always matched brute force. The preprocess-3 count moved by one between runs (`parity-adaptive` 20
or 21), which was not investigated: winner-dependent counts are expected in the race, and no verdict
differs.

Full suite at the end: `make test` 446 tests, OK, 1 skipped; native tests 46 run with none skipped;
campaign tests 47; `cargo test` 26; clippy clean. Without the native engine, and against the released
dratify 0.1.10, 446 run with 56 skipped; the only 2 failures came from the partial source export used
for that run, which left out `LICENSE` and `.github/`. All files parse under the Python 3.10 grammar;
3.10 itself is not installed here. The native engine in these runs was built against dratify's
`campaign/soundness` checkout.

## Findings

### Critical

Each was checked by a second agent, by brute force and by hand: `campaign/findings/VERIFICATION.md`.

| Defect | Findings | Fix | Test |
|---|---|---|---|
| `solve --preprocess --adaptive` never reconstructs: `1 0` prints `v -1`, exit 10, and `--self-check` did not catch it | preprocess-1, engines-5 | 3d040f8 | `TestPreprocessThenSearch` |
| `Model.solve` ignores a constraint that adds no variable: `add(x == 3)` returned `x=4` | modelling-5 | 62fdb85 | `TestModelSolvesWhatItHolds` |
| pyeq compiles value-position `and`/`or` to 0/1: `x or 5` proved equal to `1` | modelling-1 | 26be4d2 | `test_boolean_operators_as_values` |
| pyeq drops bare expressions: a walrus returning `x+1` proved equal to `x` | modelling-2 | 0688931 | `TestRejection` |
| pyeq ignores decorators: `f(1)=2` proved equal to `g(1)=1` | modelling-3 | e5a1804 | `TestRejection` |
| pyeq accepts `range()`, `range(stop=3)` and a shadowed `range`, including a module-level `def range` | modelling-4 | bfe6973 | `TestRange` |
| A call cut short leaves `seen` dirty, and the MUS extractor returns a satisfiable set that `verify` endorses | mus-1 | dd0419d | `TestRepeatedIndices`, `TestAnInterruptedCall…` |

mus-1 needs no repeated index: a `KeyboardInterrupt` does it, as the second agent showed. On a plain
`Solver` the wrong UNSAT answers are rejected by DRAT replay, so only `verify` was fooled.

**A rating to overrule if you read it differently.** The brief lists "a wrong UNSAT that passes its
own self-check" as Critical and "an encoding has the wrong solutions" as Bug. modelling-7, modelling-9,
encodings-2 and encodings-4 fit the first in its literal words and the second by name, because the
UNSAT answer is correct for the CNF the wrong encoding produced. They are rated Bug here, following
the list's explicit mention of encodings. All four are fixed either way.

"A preprocessed model does not satisfy the original formula" is also listed as Bug, and preprocess-1
is rated Critical. The answer is judged against the formula cdclkit was handed: a wrong final verdict
from the command line is Critical, and the Bug line covers a library caller driving `reconstruct`.

### Bug, fixed

| Defect | Findings | Fix | Test |
|---|---|---|---|
| `solve` after `solutions` answers for the blocked problem | modelling-6 | 62fdb85 | `TestModelSolvesWhatItHolds` |
| A Python bool constrains variable 0, so `m.add(a == b)` silently asserts `a` | modelling-7 | 45813dc | `TestPythonBooleansInExpressions` |
| Truncated `Totalizer` bounds past the cut are wrong, 876 of 876 | encodings-2 | 020855b | `TestTruncatedTotalizer…` |
| Undeclared inputs collide with auxiliary variables | encodings-4 | a61bdb5 | `TestUndeclaredInputs` |
| An empty `Totalizer` raises RecursionError | encodings-1, modelling-11 | 90625c8 | `TestNoInputs` |
| k < 0 keeps the all-false assignment | encodings-3, modelling-8 | 6330a1a | `TestNegativeK` |
| A later stopped `Optimiser.run` makes `best` worse | encodings-5 | 33a8d06 | `TestOptimiserKeepsItsBest` |
| `ge`/`le` assume a sorted domain, and a repeated value escapes `is_` | modelling-9, modelling-10 | 5f6643d | `TestDomainsAreSets` |
| pyeq reports a width the circuit does not have | modelling-12 | e615b19 | `TestWidthClaim` |
| pyeq crashes on positional-only parameters | modelling-13 | ff873b3 | `TestPositionalOnly` |
| The empty clause crashes both preprocessors, and `--preprocess -j 2` panics | preprocess-2, engines-8 | 8472cd9 | `TestEmptyClause` |
| Native keeps a stale model after a failed re-solve | engines-4 | 1c59f79 | `TestModelCleared…` |
| `--adaptive` and `-j` ignore `--conflicts` | engines-6 | dcec3c8, 22753aa | `TestConflictBudgetEverywhere` |
| `solve_portfolio` crashes on `jobs=None`, `configs=[]` | engines-7 | 7602c2f | `TestPortfolioDefaults` |
| Engines accept different Configs; unknown names run as Python | engines-9 | b13e26d | `TestBothEnginesTake…` |
| pyeq takes widths below 1 and any engine name (moved up from Note) | modelling-17 | cffe729 | `TestInputValidation` |
| No soft literals: `Optimiser` ignores a negative bound (moved up from Note) | encodings-6 | d4ae4cd | `TestOptimiserNoSoft…` |

### Open

| Finding | Severity | Why |
|---|---|---|
| preprocess-3, engines-2 | Bug, low | The preprocessors are not bit-exact, and native has no blocked clause elimination. No verdict differs. README, AGENTS.md and the docstrings now limit bit-exactness to the search. |
| engines-3 | Bug, low | Proof streams differ on search-only routes. Each replays under all three flavours, and nothing promises equal streams. |
| preprocess-4, engines-1 | Note | Preprocessed proofs delete a unit before relying on it, so `specified` rejects them. See below. |
| mus-2, mus-3 | Note | A docstring overstated a cost, now fixed; `--method core --verify` exits 1 on a correct core that is not minimal, as its help now says. |
| modelling-14, -15, -16 | Note | `proof_steps` differs by engine, and both replay; `solutions()` without `project` repeats solutions; `differential_solve` varies nothing with no cardinality constraint. Documented. |

Also not fixed: encodings-4 covers a constraint's own inputs, not a later constraint's; `(x == 3) and
(y == 4)` on `IntVar` literals cannot be refused; `-j` still drops search flags; `--adaptive` still
ignores `--prep-rounds`. Details and the status logic: `campaign/findings/STATUS.md`,
`campaign/status.py`.

**The proofs, under dratify's reading of deletion.** On 2,500 random formulas of up to 9 variables,
2,115 of them unsatisfiable, on four routes: all 2,115 refutations on each route pass dratify's
`campaign/soundness` branch on Python and Rust. On the preprocessed routes 926 fail the `specified`
flavour. Only 3 formulas needed a deletion actually ignored; the rest are refuted by propagation at the
root, which dratify notices before reading the proof.

## Behaviour that changes

Everything below raises or answers differently where it used to give an answer, often a wrong one.

- **pyeq raises on:** bare expressions except constants; decorators or `__wrapped__`; a non-builtin or
  malformed `range`; a parameter named `range`; positional-only parameters; a stray `widths` key; widths
  below 1. An unknown engine raises `ValueError`.
- **Model:** `and`, `or`, `not` and `if a:` on variables raise. `a == 1` raises. `a in list` raises when
  it must compare with another variable. A bool as a cardinality item raises. `a == b` now builds a
  constraint. Domains are sorted and deduplicated.
- **Solver:** `solve`, `add_clause` and `new_var` raise `RuntimeError` after an interrupted call.
- **Other:** `Config` raises on values either engine refuses, including seeds outside u32 and
  `walk_interval=0`. `Totalizer` past its cut raises `ValueError`. `solve_adaptive` refuses unknown
  engines. A negative `--conflicts` is an error. `--self-check` can now exit 1 on a wrong model.
  `on_improve` fires only on improvement.

The Python package and native engine must ship together: 8 tests fail with this branch's Python and the
released `cdclkit-native` 0.1.7, as they need its Rust changes.

The generators here exit 0 with open findings, and only a regression or an unexplained mismatch fails.
dratify's generators exit 1 on an open Note. The two repositories were not made to match.

## What was not checked

- drat-trim, in this repository's corners: `operational` here is the oracle's approximation of it.
  dratify's drat-trim corner runs the tool itself, on generated and solver proofs, not on these.
- Only 7 of the 2^n · n! sign and order patterns per grid cell; `Solver` sinks past n = 6 on one pattern.
- `at_most_k`'s `auto` switch at k·n > 20,000; proof logging through an encoding; `Optimiser` on native,
  which it refuses.
- `optimise` on anything but random problems; `Optimiser.run(target=...)` and resuming, in the
  modelling corner.
- pyeq past 9 input bits or width 7; `Model(config=...)`; `examples/` and `docs/tutorial/` programs.
- Search options crossed with preprocessing, past default `Config`.
- MUS on native, where no path exists; formulas past 60 variables.
- Reference solvers in the preprocessing corner: every verdict there is the oracle's, none is from
  minisat, cadical or kissat.
- The crates.io dratify 0.1.10 in the native build, which embedded the checkout's crate.

Each corner's full list is under `not_checked` in `campaign/results/<corner>.json`.
