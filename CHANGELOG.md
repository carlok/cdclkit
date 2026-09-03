# Changelog

Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).
Versions follow [semantic versioning](https://semver.org/), applied to the
public API declared in `cdclkit/__init__.py` — see "Public API" there for what
that covers and what it does not.

## [Unreleased]

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
