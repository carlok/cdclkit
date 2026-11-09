# Changelog

Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versions follow [semantic versioning](https://semver.org/), applied to the
public API declared in `cdclkit/__init__.py` — see "Public API" there for what
that covers and what it does not.

## [Unreleased]

## [0.2.1] — 2026-11-09

Use this release, not 0.2.0, if you want the native engine.

### Fixed

- **`cdclkit-native` 0.2.0 was never published.** GitHub retired the macOS image its
  wheels were built on, so the release stopped after `cdclkit` 0.2.0 reached PyPI.
  `cdclkit[native]==0.2.0` cannot be installed, and `cdclkit-native` 0.1.7 and earlier
  embed a checker that accepts refutations of satisfiable formulas. Wheels are now built
  on `macos-latest`. Nothing else in the package changes from 0.2.0.
- The coverage report read low because a test's timer switched its tracer off.

## [0.2.0] — 2026-11-09

A minor bump, because code that used to run now raises: mostly code that was getting
a wrong answer. Requires dratify 0.1.11, which fixes a refutation of a satisfiable
formula accepted by every earlier release, and which this package's native engine
embeds. Upgrade `cdclkit` and `cdclkit-native` together.

### Fixed

- **`solve --preprocess --adaptive` printed a model of the reduced formula.**
  `(x1)` gave `s SATISFIABLE`, `v -1`, exit 10, and `-j N` on top of it did the
  same. The adaptive branch returned before the only `pre.reconstruct`. Every
  route now goes through one function that reconstructs before checking or
  printing. The library's `solve_adaptive` was never affected. UNSAT answers on
  this route were right.
- `--self-check` now evaluates a model against the input before reporting SAT,
  as `--check-model` does. It only ever looked at refutations, so it could not
  have caught the above.
- **`Model.solve` answered for a problem the model no longer held.** It rebuilt
  its solver only when a *variable* had been added, so a constraint that adds
  none was ignored: `add(x != first)` could return `first`, `add(x == 3)` could
  return `x = 4`, and `add(a)`, `add(~a)` could return a solution. It now
  compares clauses and the proof sink as well. A proof passed to a later
  `solve()` also went nowhere, and now receives the refutation.
- **`Model.solutions` poisoned later solves.** Its blocking clauses stayed on
  `self.solver`, so `solve()` after an enumeration returned None on a
  satisfiable model. Enumeration now has a solver of its own.
- **A Python boolean in a model constrained variable 0.** `True` is the int 1,
  which the encoder read as a literal. `add(True)` asserted the first variable
  false, and `add(a == b)` on two `BoolVar`s, which Python evaluated to `False`,
  asserted it true. `Encoder.tseitin` and `Model.add_clause` now take booleans
  as constants. `BoolVar` has `==` and `!=`, which build constraints as they do
  on `IntVar`, and are a `TypeError` against anything but a `BoolVar` or a bool.
  **Refused now, where before they compiled to something else:** `a and b`, `a or
  b` and `not a` on a `BoolVar` or `IntVar`; `if a:`; `a in list` when it has to
  compare `a` with another variable; a bool as a cardinality item.
- **`pyeq` compiled `and` and `or` in a value position to 0 or 1.** `x or 5` was
  proved equal to `1`, with the proof replayed, while `x and x` was reported
  different from `x` and blamed on an overflow that never happens. They now
  return an operand, as Python's do. Conditions were always right, and comparisons
  as values still compile to 0 and 1, because `True == 1`.
- **`pyeq` dropped bare expression statements.** Any that was not directly a call
  was taken for a no-op, so `(x := x + 1)` was proved equal to a function that
  returns `x`, and `yield x` and `x % 0` proved a function that never returns an
  integer. The subset is now an allowlist of AST nodes checked over the whole
  body, including code that never runs. **Now refused:** every bare expression
  statement but a constant (a docstring, `...`).
- **`pyeq` ignored decorators.** With `functools.wraps` the undecorated source was
  what compiled, so a function that doubles its result was proved equal to one
  that does not. **Now refused:** any decorator, and anything with `__wrapped__`.
- **`pyeq` took `range` by name and read only its positional arguments.**
  `range()` unrolled as `range(0)`, `range(stop=3)` lost its keyword, and any
  other `range`, local or at module level, unrolled as Python's: with `def
  range(n): return (0, 0, 0)` in the module, a loop adding 3 was proved to add 1.
  **Now refused:** those, a parameter named `range`, a step of zero (it was a bare
  `ValueError`) and a length past `sys.maxsize` (an `OverflowError`).
- **A failed or interrupted solve poisoned later answers from the same `Solver`.**
  An exception out of the search left its state half changed, and the next solve
  could return a wrong UNSAT. `MUSExtractor.deletion` then returned a satisfiable
  set and `verify` endorsed it. A repeated index was one trigger, through an
  `IndexError` in `_lbd`, and a `KeyboardInterrupt` was another, with no repeats
  at all. Now a `Solver` a call was cut short on says so through `Solver.broken`,
  and **`solve`, `add_clause` and `new_var` raise `RuntimeError`** on it, because
  there is no formula to rebuild from. `MUSExtractor` and `Model` build a new one
  and carry on. `MUSExtractor.verify` runs on a solver of its own. Budgets and
  deadlines are not exceptions and are unaffected.
- A repeated assumption, or a repeated index in `MUSExtractor`, means the same as
  one, instead of raising `IndexError`.
- **A truncated `Totalizer` answered bounds past its cut wrongly.** `sum <= 1`
  over two inputs with `max_count=1` constrained nothing, and `sum >= 2` refuted a
  feasible problem. All 876 such bounds in the campaign were wrong. **They now raise
  `ValueError`.** `at_most_k` and `Optimiser` never asked for one.
- **An undeclared input could collide with an auxiliary variable.** `CNF` and
  `Solver` grow to cover a literal they have not seen, but an encoding that needed
  a fresh variable took the sink's next one, which could be one of its own inputs:
  the binary encoding of two undeclared inputs read `x1 -> ~x1`. Every encoding
  with auxiliary variables now covers its inputs first. It cannot foresee the inputs
  of a later constraint, so a program numbering its own variables should still
  declare them up front, as the `Encoder` docstring now says.
- `Totalizer` over no inputs raised `RecursionError`, and so did `at_most_one([])`
  and `exactly_one([])` with `method="totalizer"`. The other methods always took
  the empty list. It now counts zero.
- **`at_most_k` and `exactly_k` took a negative k for zero.** They forced every
  input false and answered SAT. No count is negative, so they now add the empty
  clause, as `at_least_k` does above the far end.
- **A later `Optimiser.run` could make `best` worse.** It searched from no bound
  whatever `best` held and overwrote it regardless, so a loop resuming after a budget
  was told a worse answer than it had. `best` now only improves, `run()` starts
  below it, and `max_iterations` is per call. `optimise()` was not affected.
- **`IntVar` assumed an ascending domain with no repeats.** On `[2, 1]`, `x.ge(2)`
  let 1 through and `x.le(1)` lost it, and on `[1, 1, 2]`, `x != 1` still allowed 1.
  A domain is now sorted and deduplicated, so `x.domain` may differ from what was
  passed in.
- **`pyeq` could report a width the circuit did not have.** The report took the
  largest value in `widths` and the circuit the largest among the parameters, so
  `{"a": 4, "unused": 8}` said "equivalent at 8 bits" of functions that differ at
  8, and a function with no parameters, compiled at 8, said "at 0 bits".
  `result.width` is now the circuit's. **A `widths` key naming no parameter now
  raises `UnsupportedConstruct`.**
- `pyeq` crashed with a bare `TypeError` on a counterexample for positional-only
  parameters, which it also left out of the circuit. **They now raise
  `UnsupportedConstruct`.**
- **The empty clause crashed both preprocessors.** It was a `ValueError` in Python
  and a panic in Rust, which is a `BaseException` and went past the portfolio's
  fallback, so `cdclkit solve g.cnf --preprocess -j 2` died on a formula as plain as
  two contradictory units, while `CDCLKIT_ENGINE=python` answered. Both now report
  UNSAT, and a preprocessor can be handed its own output.
- After a re-solve refuted at the root, the native `Solver` still reported the old
  model, where the Python one reports none. The verdict was always right.
- **`--adaptive` and `-j N` ignored `--conflicts`**, despite what 0.1.3 says here:
  the budget never reached the pipeline, and neither it nor the portfolio could
  take one. `solve_adaptive` and `solve_portfolio` now have `max_conflicts`, and out
  of budget is `s UNKNOWN`, exit 0, on every route. It bounds an adaptive run as a
  whole and each `-j` worker on its own. `--conflicts` with `-j` runs on processes
  rather than threads, because a native thread cannot be stopped on a budget. A
  negative budget is now an error.
- `solve_portfolio(f)` raised `TypeError` on its own default `jobs=None`, and
  `configs=[]` ended in `RecursionError` after spawning at every level. The first
  now uses the core count, as the module docstring says, and the second raises
  `ValueError`.
- **The engines accepted different configurations.** Python took `rnd_seed=2**32 + 1`,
  a negative `glue_keep` and `restart="bogus"`, which silently meant Glucose, and
  native raised on all three, so `--seed 4294967297 --adaptive` worked or failed by
  engine. **`Config` now raises `ValueError` on anything either engine would refuse,**
  including a seed outside u32 and `walk_interval=0`. `solve_adaptive` also refuses an
  unknown engine name, which used to run as Python.
- **`pyeq` proved anything at a width of 0 or below.** No bits means an empty miter,
  so `a + 1` was "equivalent" to `a`, with the proof replayed. **Such a width now
  raises `UnsupportedConstruct`.** An unknown `engine` name, which used to run on
  Python, raises `ValueError`.
- `Optimiser` with no soft literals ignored a negative bound, and returned a model
  for `count <= -1`. It now returns None, as it does with soft literals.

### Known, and left open

Found by the same campaign, reviewed, and not changed.

- The preprocessors are not bit-exact, so the model, conflict count and proof can
  depend on the engine once preprocessing runs. Porting blocked clause elimination
  is real work, so AGENTS.md, the README and the docstrings now say bit-exactness
  stops at the search. No verdict has differed.
- Proof streams differ between the engines on search-only routes too. Each replays.
- Preprocessed proofs delete a unit and then rely on it. They check under dratify's
  rule and not under a literal reading of DRAT deletion.
- `Model.solutions()` without `project` and `differential_solve` on a model with no
  cardinality constraint do what their docstrings now say, which is less than they
  appeared to promise. `pyeq`'s `proof_steps` still differs by engine, as
  `tests/test_pyeq.py` documents, and `mus --method core --verify` still exits 1 on a
  correct core that is not minimal, as its help now says.

### Tests

- CI now runs `make lint` and `bench/compare.py --quick`, the part of
  `make gate` it had been skipping although CONTRIBUTING said it ran all of it.
  The reference solvers are MiniSat and CaDiCaL.
- `cargo audit` over `native/Cargo.lock`, when the lockfile changes and weekly.
- Dependabot watches the Python build tooling. `dratify` and `cdclkit-native`
  are excluded, because their versions move only with a release.

## [0.1.7] — 2026-10-24

### Fixed

- **Requires dratify 0.1.9**, in both halves: `dratify>=0.1.9` for the
  Python package, and the `dratify` crate 0.1.9 embedded in `cdclkit-native`.
  Both of dratify's checkers misread a proof step that repeats a literal:
  `1 1 0` never became unit at the root, so a valid proof that relied on it
  was rejected, and `d 1 1 0` deleted a unit that should have been ignored.
  A false rejection only. cdclkit's own solvers do not write repeated
  literals, so their self-checks were not affected. The checker that
  `cdclkit-native` hands to `dratify` is the Rust one, though, and it gets
  the fix only from this release.

### Tests

- The target-phase scaling test steps by 16x with a limit of 64, not 4x with
  a limit of 8. A macOS runner measured 8.3x for 4x on native runs of 4 and
  32 ms, while linear is about 4.5x at that step. At 16x, linear is about 20x
  and quadratic about 256x, and run against 0.1.4 the test still fails at
  252x (native) and 218x (Python).
- CI can be re-run by hand (`workflow_dispatch`).

## [0.1.6] — 2026-10-14

### Fixed

- **`CDCLKIT_ENGINE` did nothing.** AGENTS.md and the `cdclkit.native`
  docstring said it selected the engine and that the native engine was "never
  selected implicitly". Neither was true: nothing read the variable, and
  `cdclkit solve --adaptive` and `-j N` used native whenever it was installed.
  Both paths now honour `CDCLKIT_ENGINE=python|native`. An unknown value, or
  `native` without the build, exits 1 with a message instead of being
  ignored. Both paths also print `c engine: ...`, so a result says which
  engine produced it. Defaults are unchanged: native when installed for
  `--adaptive` and `-j`, Python for plain `solve`. The engines are bit-exact,
  so the choice changes the speed and not the answer.
- AGENTS.md and the `cdclkit.native` docstring now describe which entry point
  uses which engine, and drop the `--engine` flag, which never existed.
- `BitVec.slt()` and `_Compiler.assign()` in `pyeq` have docstrings that match
  the code. Behaviour is unchanged.

### Tests

- `make test` prints a note when the native engine is not built for the
  interpreter, because its tests skip and the run still says OK.
- The portfolio's Python-vs-native agreement test skips without native
  instead of comparing Python with itself.

## [0.1.5] — 2026-10-09

### Fixed

- **The search was quadratic in the number of variables whenever it made
  decisions without conflicts**, in both engines. With target phases on --
  the default -- every new deepest trail copied the *whole* trail into the
  target, on the theory that improvements "become rare quickly". They do once
  conflicts start; a search that makes many decisions without one improves on
  every decision, and n of them cost O(n²). Now only the part of the trail the
  target does not already hold is copied, which leaves the target, and so
  every conflict, decision and propagation, exactly as before: the
  conflict-count baseline is unchanged to the last conflict, and the fixed
  Python engine was bit-exact with the *unfixed* Rust one before Rust was
  touched.

  | | before | after |
  |---|---|---|
  | Python, 65,536 declared variables | 144 s | 0.48 s |
  | Python, 2^20 declared variables | hours (extrapolated) | 10.2 s |
  | native, 131,072 declared variables | 4.2 s | 0.01 s |

  Any large formula with an easy search paid this; the benchmark corpus, at
  250 variables or fewer, was too small to show it. It became a
  denial-of-service when dratify 0.1.7 began accepting headers that declare up
  to 2^20 variables from a file of any length -- a correct fix for real
  instances that declare variables they never use, which turned a 22-byte file
  into hours of CPU here. `tests/test_target_scaling.py` checks that
  quadrupling the variables costs closer to 4x than 16x, on both engines.

### Documentation

- `SECURITY.md` says where "slow" ends: cost out of proportion to a formula's
  size *and* difficulty is a bug worth reporting, and time limits remain the
  caller's protection against genuinely hard input.
- Python 3.15 classifier; CI has tested it since its release candidates.
- Seven roadmap items that were done are marked done, and the CaDiCaL/PySAT
  entry records what the investigation found.

## [0.1.4] — 2026-10-04

Requires dratify 0.1.7, in both halves, for three checker fixes that matter
here: `--self-check` and every proof check in this package run through it.

### Fixed

- **`--self-check` could report a valid proof as rejected (exit 30).** The
  checker, Python and Rust alike, lost the root implication of a lemma that was
  already unit at the root when added, and then rejected later lemmas that
  depended on it. That is the safe direction -- nothing invalid was accepted
  -- but a solver whose answer is right was told otherwise. Fixed in dratify
  0.1.7; this release requires it from Python (`dratify>=0.1.7`) and compiles
  it into the native engine (`dratify = "0.1.7"`).
- **The pure-Python checker accepted refutations of satisfiable formulas given
  negative literals in a list of steps.** Not reachable from this package's
  own solver, which writes internal literals, but reachable by anyone handing
  `check_proof` a hand-built list. Fixed in dratify 0.1.7.
- A DIMACS header declaring more variables than the file had characters was
  refused as malformed, and a short proof naming a variable beyond its own
  length likewise. Both are in dratify's parser; fixed there.

The rest of this release is the release pipeline and the checks that stand
between a commit and a visitor; nothing else a user installs has changed.

### Security

- **A branch could publish a release.** `release.yml` also accepted
  `workflow_dispatch`, which runs the workflow file from whichever branch is
  selected. The tag-must-match-version check applied only `if` the ref was a
  tag, so a dispatch skipped it and published whatever version the branch
  declared, and the branch could delete the check besides. The `pypi`
  environment had no ref policy to stop it. It is now restricted to `v*` tags
  in the repository settings, the dispatch trigger is gone, and the build job
  fails outright for any ref that is not a tag.

### Fixed

- **The post-install smoke test had failed on every run since the dratify
  split.** It still listed `cnf`, `lits` and `proof` as `cdclkit` modules. It
  only ran by hand (`make smoke`), so nobody saw. It now checks those three in
  `dratify`, a test asserts its module list matches `cdclkit/*.py`, and a CI
  `packaging` job builds the wheel, installs it into a clean virtualenv and
  runs it from `/`.

### Added

- `tests/test_readme.py` runs every Python example in the README and checks
  that it prints what its comments promise. Nothing had ever executed them.
- CI runs Python 3.15 (currently a release candidate), including a native
  engine leg, so the final release finds nothing new.

### Documentation

- Sigstore attestations were listed as missing in `RELEASING.md` and the
  roadmap. Every file on PyPI has carried a PEP 740 attestation since the first
  Trusted Publishing release; the publish action adds them by default.

## [0.1.3] — 2026-09-03

### Fixed

- **`--adaptive` ignored `--self-check`, `--proof`, `--conflicts` and every
  search flag.** The branch built a `Config`, a proof sink and a conflict
  budget, passed none of them to a pipeline that had no `proof` parameter at
  all, then printed `s UNSATISFIABLE` and exited 20 having checked nothing.
  `--check-model` *was* handled, which is what made the omission read as
  deliberate. `README.md`, `SECURITY.md` and the `demo` target all rest on
  `--self-check` being honoured.

  Fixing it required logging preprocessing steps, since BVE adds clauses that
  do not follow from the input — a refutation of the reduced formula is not one
  of the original. Writing that test found a second, latent bug: the native
  `Preprocessor` takes a `with_proof` flag that nothing ever passed, so it
  logged zero steps where Python logged twelve. Anyone wiring this up would
  have produced an invalid proof. Both engines now agree, and the test asserts
  the combined proof verifies against the **original** formula.
- **The CLI ran a different solver than the library.** `--restart` defaulted to
  `"glucose"` while `Config.restart` had moved to `"luby"`, so the headline
  benchmark below never described `cdclkit solve`. Every CLI default now
  derives from `Config()`, with a test asserting it.
- `solve_adaptive` dropped its deadline on the parallel path, the one parameter
  that exists because a par32 instance once ran 77 minutes past a 120s budget.
- `pyeq.equivalent` documented "both functions must take the same parameters"
  and never checked it, so comparing `f(a, b)` with `g(a)` compiled constants
  at different widths and reported a false counterexample on identical source.
  A bare `except Exception` then swallowed the `TypeError` that would have
  exposed it. `engine="native"` also fell back to Python silently; it now
  raises, matching `dratify`.
- `dpll` raised `IndexError` on a formula containing the empty clause.
- **The Rust checker was pinned two releases behind the Python one.**
  `native/Cargo.toml` asked for `dratify 0.1.0` while `pyproject.toml` required
  0.1.2 — two implementations, two releases apart, in one process, sold as
  cross-checking each other. Both now require 0.1.4, and a test fails if they
  diverge again.

### Documentation

The prose had drifted from the program in ways a reader would have caught.

- `docs/RELEASING.md` — the document consulted while performing this project's
  one irreversible action — opened by saying the repository is private and
  unlicensed, and linked a `docs/LICENSING.md` that was never written. The repo
  is public and Apache-2.0, and publishing is automated.
- `AGENTS.md` was wrong in its two most load-bearing sections: the heading "CLI
  exit codes are not 0" sat above an enumeration omitting 0, while
  `EXIT_UNKNOWN` is 0; and the section titled "the single most common error"
  gave the doubled-index formula without introducing the 0-based internal index
  it is stated over. `tests/test_agent_docs.py` now guards both.
- `ALGORITHMS.md` §8 listed rephasing as absent and target phases as off by
  default; both ship on by default. The Luby docstring sold the optimality
  theorem while `block_restart` — on by default, and policy-independent though
  documented only under Glucose — defers the restarts the sequence asks for.
- **The native speedup is 20.1x, not 18x**: geometric mean of per-instance
  ratios over 17 instances, spread 11x to 51x. The figure was recoverable only
  after fixing `make history`, which printed `0.00` for all fifteen recorded
  checkpoints because it read `totals["cdclkit"]` with a `0.0` default while
  the file stores `"sable"`.

### Added

- A CI job running the conflict-count baseline. `make gate` had always run it;
  CI never did, so the only guard against a change altering search behaviour
  fired when a human remembered to type it.
- The coverage floor is enforced at 72% against a measured 75.9%. `--min`
  defaulted to `0.0` and the guard tested truthiness, so the documented floor
  existed nowhere.
- Both release workflows run the suite on the tagged commit and refuse a tag
  naming a different version. `ci.yml` does not trigger on tags, so nothing had
  tested a released ref.
- `CONTRIBUTING.md`. `make test` on a fresh clone failed with 24 import errors,
  because the Makefile still said "No dependencies" from before this package
  depended on `dratify`.

### Changed

- **Default search is Luby restarts with target phases**, replacing Glucose EMA
  with saved phases. Measured against kissat over 200 public instances: uf250
  3.25 -> 1.02, uuf250 0.84 -> 0.72. The old default's stated rationale --
  "unsatisfiable instances dominate the hard cases" -- was wrong on its own
  terms, since the change improved the unsatisfiable half too.
- **Local-search rephasing (probSAT)**, on by default behind two guards. Walk
  the original clauses from the current phases; the best assignment found
  becomes the phases the search branches from. It decides nothing, so proofs
  are unaffected.

  Ungated it is 37x on large random satisfiable instances *and* 5.2x slower on
  small random unsatisfiable ones, 1.55x on graph colouring, 1.68x on planning.
  That configuration is fitted to a benchmark rather than better at solving, so
  the default gates it on 5000 conflicts already spent (`walk_min_conflicts`)
  and stops after three non-improving walks (`walk_patience`). The ungated
  setting is available as a portfolio worker.
- **Benchmark comparisons subtract each external solver's measured process
  startup** instead of discarding instances it solved quickly. The old 50 ms
  threshold sat inside kissat's uf250 distribution, and kissat's own speed
  varied 35% between runs of the same binary, so half a family moved in and out
  of the sample -- dropping precisely the instances where the competitor was
  fastest.

### Added

- `Config.target_phase`, `target_reset`, `walk_flips`, `walk_interval`,
  `walk_patience`, `walk_min_conflicts` -- all mirrored bit-for-bit in the Rust
  engine.
- The public SATLIB corpus is 344 instances, from 164. `uf250`/`uuf250` were
  capped at 10 where SATLIB ships 100, and the cache check made raising the cap
  a silent no-op.
- Benchmark harnesses detect host suspension by comparing wall clock against
  the monotonic clock, and runs go under `caffeinate -i`.

- **Differential encoding.** `differential_solve(build, methods=...)` builds
  the same model twice under different cardinality encodings and requires the
  same verdict. This is the one class of bug the proof machinery cannot reach:
  a DRAT refutation certifies the clauses it was handed, not that they mean the
  constraint someone wrote. Every verified solver and checker in the field
  takes CNF as its input, so the translation *into* CNF is the last unchecked
  step in the whole pipeline.
- **A held-out corpus.** 11 structurally different SATLIB families, marked
  holdout, which `bench/sweep.py` refuses to load. Measured: 0.21x against
  kissat on families nothing was ever tuned against, against 0.26x on the tune
  families -- the configuration generalised.
- **`--repeat N`** with median aggregation and a spread report split by
  instance duration. The solver is deterministic, so all run-to-run variation
  is the machine: 1.02x on instances doing real work, and meaningless jitter
  below 50 ms.
- Both engines take an optional wall-clock deadline. The benchmark harness had
  been bounding the competitors and not itself.

### Known limitations

- Performance is measured on one machine. Repeats give an error bar now
  (1.02x on substantial instances), but nothing here has run on a second
  machine or on SAT Competition instances.
- `kissat --sat` beats the pre-walk configuration on satisfiable random
  instances by 1.28x. The walk changes that, but the walk is a specialised
  tool: gated off, it does nothing; ungated, it is 5.2x slower on small random
  unsatisfiable instances.
- Differential encoding covers cardinality constraints. The Tseitin circuit
  encodings and the pseudo-Boolean BDD have one implementation each and so
  cannot be cross-checked this way.

## [0.1.0]

First release. Everything below existed before this version in some form; what
0.1.0 adds is that it is installable, that the versions agree with each other,
and that the one remaining place where an answer rested on trust no longer
does.

### Added

- **`pip install cdclkit`.** Two distributions: `cdclkit`, a pure-Python
  `py3-none-any` wheel with zero dependencies, and `cdclkit-native`, an optional
  Rust accelerator installed as `cdclkit[native]`. A `cdclkit` console script
  replaces `python3 -m cdclkit`, which still works.
- **`cdclkit --version`**, which also reports whether the native engine loaded.
  "Which build is this" and "was the accelerator actually in use" are the same
  question when a benchmark number looks wrong.
- **`cdclkit.pyeq` in the public API**: `equivalent`, `EquivalenceResult`,
  `UnsupportedConstruct`, `ProofRejected`. Resolved lazily, because `pyeq`
  needs `inspect` and importing it eagerly was 5.5 ms of an 8.8 ms
  `import cdclkit`.
- **`max_conflicts` for `equivalent()`**, so a check can be bounded. Without it
  the tool could only finish or hang, which is not something anyone can put in
  CI.
- **`make dist` and `make smoke`**: build both wheels, then install them into a
  clean virtualenv and run the CLI and `pyeq` from `/`, with no checkout on the
  path. Testing the repository is not testing the artefact.
- CI matrix across Python 3.10–3.14 on Linux and macOS, and a packaging job on
  both. The `>=3.10` claim was previously tested on 3.12 alone.

### Changed

- **`equivalent()` now proves what it claims.** It emits a DRAT proof of the
  unsatisfiable miter and an independent checker replays it before `proved` is
  allowed to be `True`; the result carries `proof_checked` and `proof_steps`.
  Passing `verify=False` restores the old behaviour and says `UNVERIFIED` in
  the report, so it cannot be switched off quietly.
- **`EquivalenceResult.proved` is three-valued**: `True`, `False`, or `None`
  for an exhausted budget. `__bool__` returns `proved is True`, so undecided
  can never read as proved.
- The verified path does not preprocess. Bounded variable elimination adds
  clauses that do not follow from the input, so a refutation of the
  preprocessed miter is not a refutation of the miter the caller asked about.
- The CLI reports malformed input as `c error: line 2: bad token 'x'` and exits
  `1`, instead of printing a traceback. Also handles directories, permission
  errors, non-text files and broken pipes.
- Clippy can fail the build. It ran with `-D warnings` *and*
  `continue-on-error: true`, which is a check that cannot fail.
- `cdclkit/__init__.py` states which names are public and which modules
  (`pipeline`, `portfolio`, `native`) are internal despite being importable.

### Fixed

- **`equivalent()` could report an exhausted budget as a proof.** The verdict
  came from `if not res.sat`, and the pipeline returns `None` on exhaustion;
  `None` is falsy. No live path returned `None` before `max_conflicts` existed,
  so this was latent rather than exploitable — but it went live the moment a
  budget did, in this same release. There is a regression test whose only job
  is that distinction.
- Dead code in `native/src/solver.rs`: `BinWatch` and `bin_watches` survived
  the reverted binary-clause specialisation and were allocating two `Vec`s per
  variable that nothing ever read. Also `Heap::is_empty`, zero callers.
  Conflict counts unchanged on every baseline instance.
- `cdclkit/__init__.py` said `1.0.0` while `native/Cargo.toml` said `0.1.0`.
  `tests/test_packaging.py` now fails if they drift again.

### Removed

- **The CC0 dedication.** It came from the scratch phase, before anything
  commercial was discussed, and it is the one licensing choice with no path
  back: irrevocable, no patent grant, no trademark reservation. Nothing had
  been published under it, so removing it cost nothing; after a first public
  release it would have been permanent.

  The replacement is not another licence. It is silence: no licence means no
  rights granted, which is the only position from which every option is still
  reachable, including a permissive release later.

  > **Superseded.** That position was reversed before the first public
  > release: the project ships under **Apache-2.0** (see [LICENSE](LICENSE)),
  > which was one of the options the silence was preserving. The `COPYRIGHT`
  > and `docs/LICENSING.md` files this entry once pointed at were never
  > written; `LICENSE` is the only licence document.

### Known limitations

Stated here rather than discovered later. The README expands on each.

- **No Windows.** Never tested, and the classifiers say so rather than
  implying support.
- The equivalence checker models a small subset of Python. Everything outside
  it raises `UnsupportedConstruct` with a line number rather than being
  approximated.
- The DRAT checker is forward-only: correct and complete for RUP and RAT, but
  it verifies every step rather than working backwards from the empty clause.
  Roughly the cost of the solve with the native checker.
- No inprocessing, and no XOR/Gaussian reasoning.
- Single-threaded, the engine loses to kissat on public SATLIB instances.

  *(Corrected after release preparation: this originally said "1.10x geometric
  mean". That figure came from a 14-instance corpus in which one instance
  decided the ranking. On the 344-instance corpus the honest number for this
  configuration is 1.62x. Left visible rather than quietly overwritten -- the
  number was wrong, and the reason it was wrong is the more useful fact.)*
