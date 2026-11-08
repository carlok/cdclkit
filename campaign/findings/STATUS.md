# Where the findings stand

The generators read this from `campaign/status.py`. A mismatch of a fixed finding is a
regression and fails the run. An open one is reported and does not.

## Fixed

| Finding | Filed as | Commit | What changed |
|---|---|---|---|
| preprocess-1 | Critical | 3d040f8 | `--preprocess --adaptive` reconstructs; `--self-check` judges models |
| engines-5 | Critical | 3d040f8 | the same bug, reached from the engines corner |
| modelling-5 | Critical | 62fdb85 | staleness compares clauses and the proof sink, not only variables |
| modelling-6 | Bug | 62fdb85 | enumeration runs on a solver of its own |
| modelling-7 | Bug | 45813dc | booleans are constants; `==` on `BoolVar` builds a constraint; `and`/`or`/`not` raise |
| modelling-1 | Critical | 26be4d2 | value-position `and`/`or` return an operand |
| modelling-2 | Critical | 0688931 | the subset is an allowlist of AST nodes; bare expressions raise |
| modelling-3 | Critical | e5a1804 | decorators and `__wrapped__` raise |
| modelling-4 | Critical | bfe6973 | `range` must be the builtin and well formed, by source and by function object |
| mus-1 | Critical | dd0419d | a call cut short marks the solver broken; the extractor rebuilds; `verify` has its own solver; repeats dropped |
| encodings-2 | Bug | 020855b | a bound past the cut raises `ValueError` |
| encodings-4 | Bug | a61bdb5 | inputs are covered before any auxiliary is taken |
| encodings-1 | Bug | 90625c8 | a totalizer over nothing counts zero |
| modelling-11 | Bug | 90625c8 | the same, through the model |
| encodings-3 | Bug | 6330a1a | a negative k adds the empty clause |
| modelling-8 | Bug | 6330a1a | the same, through the model |
| encodings-5 | Bug | 33a8d06 | `best` only improves; `max_iterations` is per call |
| modelling-9 | Bug | 5f6643d | a domain is sorted |
| modelling-10 | Bug | 5f6643d | a domain is deduplicated |
| modelling-12 | Bug | e615b19 | the report names the circuit's width; a stray key raises |
| modelling-13 | Bug | ff873b3 | positional-only parameters raise |
| preprocess-2 | Bug | 8472cd9 | the empty clause means UNSAT in both preprocessors |
| engines-8 | Bug | 8472cd9 | the same, through `--preprocess -j 2` |
| engines-4 | Bug | 1c59f79 | native clears the model before the `ok` test |
| engines-6 | Bug | dcec3c8, 22753aa | `max_conflicts` on `solve_adaptive` and `solve_portfolio` |
| engines-7 | Bug | 7602c2f | `jobs=None` works; `configs=[]` raises |
| engines-9 | Bug | b13e26d | `Config.validate`; `solve_adaptive` refuses an unknown engine |
| modelling-17 | Note, nearer Bug | cffe729 | a width below 1 and an unknown engine raise |
| encodings-6 | Note, nearer Bug | d4ae4cd | a negative bound with no soft literals is None |

## Open

| Finding | Filed as | Why it stays |
|---|---|---|
| preprocess-3 | Bug, low | Native has no blocked clause elimination and visits clauses in another order. Unifying them is real work and nobody needs it: no verdict differs. README, AGENTS.md and the docstrings now limit bit-exactness to the search. |
| engines-2 | Bug, low | The same as preprocess-3, seen through `solve_adaptive`. |
| engines-3 | Bug, low | Proof streams differ on search-only routes. Each one replays under all three flavours, and no document promises equal streams. |
| preprocess-4 | Note | A unit's deletion is logged before the steps relying on it, so `specified` rejects those proofs. See below for dratify. |
| engines-1 | Note | The same as preprocess-4, through `solve_adaptive`. |
| mus-2 | Note | The docstring overstated a cost, and now states it. Results were always MUSes. |
| mus-3 | Note | `--method core --verify` exits 1 on a correct core that is not minimal. Matches its help, which now says so. |
| modelling-14 | Note | `pyeq`'s `proof_steps` differs by engine, as `tests/test_pyeq.py` documents. Both replay. |
| modelling-15 | Note | `solutions()` without `project` repeats user-level solutions. The docstring now says so and how to avoid it. |
| modelling-16 | Note | `differential_solve` varies nothing on a model with no cardinality constraint. The docstring now says so. |

## preprocess-4 and engines-1 under dratify's deletion rule

Rechecked against dratify's `campaign/soundness` branch, still numbered 0.1.10 but not released
as such, whose rule is that deleting a clause unit under the root assignment is ignored. On 2500 random formulas of up to 9 variables, of which 2115 are
unsatisfiable, `solve_adaptive` was run with `always_preprocess=True` and with a probe of 0
conflicts, on each engine. Every refutation went through dratify's Python and Rust checkers.

| Route | Refutations | Rejected by dratify, Python | Rejected by dratify, Rust | Failing `specified` |
|---|---|---|---|---|
| Python, preprocessed | 2115 | 0 | 0 | 926 |
| native, preprocessed | 2115 | 0 | 0 | 926 |
| Python, probe | 2115 | 0 | 0 | 1 |
| native, probe | 2115 | 0 | 0 | 3 |

So all of them pass. Only 3 formulas needed a deletion actually ignored; the rest of the 926 are
refuted by propagation at the root, which dratify's checker notices before reading the proof.
drat-trim was not run.
