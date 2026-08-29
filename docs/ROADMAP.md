# Roadmap

Written 2026-08-29, after three independent audits (code, ecosystem, adoption),
a 288-pair experiment on `pyeq`, and a head-to-head against `drat-trim`.

Everything here is chunked into sprints that can be done one at a time. Each
sprint states what "done" means, so it can be closed without judgement calls.

---

## The finding this roadmap is built on

The repository contains four things. They do **not** have equal prospects, and
the evidence for that is measured rather than assumed:

| component | verdict | evidence |
|---|---|---|
| DRAT stack | **the asset** | the only empty niche in the ecosystem; strongest module in the code audit; within 1.75x of drat-trim while checking *forward* |
| CDCL solver | credible, no niche | PySAT ships wheels everywhere and bundles kissat 4.0.4 |
| `pyeq` | experiment | 0/105 marginal catch rate against CrossHair; four false-proof paths found |
| encodings / model | supporting | fine, but not a reason anyone installs anything |

**The DRAT stack is the only part with a defensible reason to exist.** PySAT
emits DRUP proofs from six solver families (`with_proof=True` / `get_proof()`)
and ships nothing to check them. The only DRAT checker on PyPI is `drup`:
Linux-x86_64, Python <= 3.10, last released May 2023. `drat-trim` is C you must
compile and is not packaged at all.

So: there is no way today to check a DRAT proof inside a Python process on
macOS, on Windows, or on any current Python. This repository already does that,
on both engines.

**The plan is a repackaging, not a pivot.** No code is deleted. The Rust engine
is what makes the checker competitive at all -- pure Python takes 41s on a
209,367-step proof where Rust takes 2.27s. Python gives reach, Rust gives
usability, and the fact that *both* exist and agree is the selling point:
proof checking is the one domain where two independent implementations agreeing
is the entire epistemics.

### Measured, for reference

Checker, this machine, 2026-08-29:

| instance | steps | Python | Rust | drat-trim |
|---|---|---|---|---|
| uuf100-01 | 774 | 0.01s | 0.01s | 0.05s |
| uuf100-010 | 1,103 | 0.05s | 0.00s | 0.06s |
| uuf250-01 | 209,367 | 41.47s | 2.27s | 1.30s |

Rust is 18x over Python. It beats drat-trim 7-22x on small proofs (drat-trim
pays process startup and cannot be called in-process) and loses 1.75x on the
large one -- while doing *forward* checking against drat-trim's backward
checking. That gap is the honest headline, and closing it is not required to
ship.

Cross-validation against the reference checker, 10 proofs from two solvers:
**drat-trim and cdclkit agreed on all 10**, including four rejections.

---

## Sprint 0 -- Decisions  [DONE 2026-08-29]

- [x] **Name: `dratify`.** DRAT + "ratify" (to formally confirm), which is what
      a proof checker does. Verified free on **both** PyPI and crates.io.
      `cdclkit` was not an option: PyPI's `cdclkit` is an unrelated abandoned SQL
      testing tool that pulls in numpy, pandas and typer, so `pip install cdclkit`
      installs a stranger's package.
- [x] **Licence: Apache-2.0.** Patent grant, permissive, and it keeps every
      later option open except relicensing other people's contributions.
- [x] **Two packages.** A small checker (`dratify`) with zero dependencies and
      an optional Rust accelerator, plus the existing toolkit under its own
      name. Nobody should install a SAT solver to verify a proof.
- [x] **`pyeq`**: fix the width divergence, then ship labelled as an experiment
      with the 0/105 result stated.
- [x] **kissat number**: moves to `BENCHMARKS.md` with its caveats.

### Built and awaiting publication

Both distributions exist, are tested, and are cross-validated against
`drat-trim`. Neither is a name squat -- they work.

    packages/dratify/       Python, zero deps, 9 tests, wheel + sdist, twine OK
    packages/dratify-rs/    Rust crate, no dependencies, 6 tests + doctest

Publishing needs registry credentials, so it is a manual step. See
`docs/RELEASING.md`.

Note: extracting the checker into a standalone crate incidentally fixes the
"`cargo test` cannot link on macOS" problem for this code -- the standalone
crate has no pyo3, so its tests run everywhere.

## Sprint 1 -- Soundness and honest documentation

The tree must not contain a known false proof or a claim the code does not
support.

- [x] `pyeq` fall-through: a guarded last return was used as an unconditional
      fallback. Fixed, `_definitely_returns` guard.
- [x] `pyeq` bare `return`: modelled as `0` while `return None` was rejected.
      Inconsistent and unsound. Fixed.
- [x] `pyeq` body with no return: short-circuited before the guard. Fixed.
- [x] `pyeq` default arguments: silently dropped, so `f(a, b=3)` and
      `g(a, b=99)` proved equivalent. Fixed.
- [x] 6 regression tests, verified by reinstating a bug and watching them fail.
- [ ] **`pyeq` per-function width divergence.** `compile_function` computes
      `width = max(widths[n] for n in names)` over *each function's own*
      parameters, so comparing `f(a, b)` with `g(a)` at
      `widths={"a": 4, "b": 16}` compiles constants at different widths and
      reports a **false counterexample** on identical source. The bare
      `except Exception` at `pyeq.py:778` swallows the Python re-simulation
      that would have caught it. Needs a signature-compatibility check.
- [ ] **Phantom documentation.** `pyeq.py:295` tells users to "pass it through
      `helpers=`"; no such parameter exists. The uncommitted `encodings.py`
      documents `xor_direct()` and `assert_expr_expanded()`; neither exists.
- [ ] **Docstrings that describe code that isn't there.**
      `_Compiler.assign()` (`pyeq.py:447-452`) describes a select that happens
      elsewhere; `BitVec.slt()` claims a signed-overflow XOR where the code
      widens by a bit. Both behave correctly; only the prose is wrong.
- [ ] **`ALGORITHMS.md` section 8** lists rephasing as absent and target phases
      as "off by default until measured". Both ship on by default.
- [ ] **The Luby docstring.** `solver.py:50-54` sells Luby's optimality
      theorem, but `block_restart=True` is also default and suppresses restarts
      14x (619 -> 44 on a 194,756-conflict run), so the schedule that executes
      is not Luby. Blocking *wins* -- 1.62x faster, 25% fewer conflicts -- so
      this is a prose fix, not a code fix. Defend it empirically.
- [ ] **`Config.special_inc`** is declared, defaulted to 1000, and never read.

**Done when:** `grep` finds no reference to a symbol that does not exist, no
known false proof survives, and every default is described accurately.

---

## Sprint 2 -- Repackage: the checker leads

Nothing is rewritten. The front page changes.

- [ ] **README reorder**: checker first, solver second, `pyeq` third and
      explicitly labelled an experiment.
- [ ] **Drop or heavily caveat the kissat comparison.** PySAT bundles kissat
      4.0.4, so a reviewer reproduces the number in ten minutes on a suite
      where SATLIB instances are small enough to be partly measuring process
      startup -- and having discounted it, discounts the DRAT work with it.
      This is the highest-leverage edit in the document: the feature you are
      proudest of is undermining the feature with a future.
- [ ] **Correct the Rust framing.** The README says the Rust engine "is being
      added" and is "never selected automatically". It is 3,741 lines, bit-exact
      with Python, and the pipeline defaults to it.
- [ ] **A `check` quickstart that runs in four lines**, taking a proof from
      PySAT and verifying it. That is the entire pitch and it should be the
      first code block anyone sees.
- [ ] **Document the two-engine agreement property.** Python and Rust rejected
      exactly the same corrupted proofs across 16,000 comparisons (93/93,
      125/125, 13/13) with 1,542 RAT steps exercised. Nobody else offers this;
      drat-trim is one implementation and `drup` is one implementation.

**Done when:** a stranger reading the README top-to-bottom understands within
30 seconds that this checks proofs, and can run it.

---

## Sprint 3 -- Close the test-infrastructure gaps

The audit found the headline claims weaker than they sound. None of these are
correctness bugs today; all of them are how a correctness bug would get in.

- [ ] **`rnd_freq` and `rnd_seed` have no Rust counterpart** and are silently
      ignored. This one *is* a live bug: `portfolio.py:157-201` builds worker
      diversity from exactly those two knobs, and `portfolio.py:199` sets a
      per-worker seed "so duplicated recipes still diverge". On the native path
      they are dropped, so duplicate recipes become bit-identical duplicate
      workers. Measured divergence: Python 4,987 conflicts vs Rust 3,171.
      Either implement them in Rust or make the native path reject them.
- [ ] **Bit-exactness tests cannot reach most of the solver.** Instances peak at
      748 conflicts, but `first_reduce=2000`, `walk_min_conflicts=5000` and
      `block_restart` needs 10,000. So `reduce_db`, probSAT rephasing and
      restart blocking are **never** compared between engines. One long
      instance fixes this.
- [ ] **`restart="glucose"` and `ccmin="basic"` are never compared** across
      engines at all. Since the default restart is now `luby`, the `default` and
      `luby` entries in `CONFIGS` are the same configuration.
- [ ] **`brute.py` has no test file** and is the oracle for 1,732 comparisons
      per suite run. Its only check compares `dpll` against `exhaustive_solve`,
      both defined in `brute.py`. That is self-consistency, not independence.
- [ ] **"Fuzzing" is a fixed corpus.** All 41 `random.Random(N)` calls use
      hardcoded literal seeds; mean 6 variables, max 59. `tests/util.py`
      already has `fuzz_seed()` / `fuzz_cases()` with `CDCLKIT_FUZZ_SEED` and
      **zero call sites**, plus a docstring pointing at `tests.fuzz_dimacs`,
      which does not exist. Wire it up or stop calling it fuzzing.
- [ ] **`make test` uses the system interpreter**, so the default developer
      command skips all 37 native tests and reports green. Make it say so.
- [ ] **`cargo test` cannot link on macOS** -- `native/Cargo.toml:11,14`
      declares `crate-type = ["cdylib"]` with unconditional pyo3
      `extension-module`, so ~25 Rust unit tests are unrunnable outside Linux
      CI.
- [ ] **Vacuous assertions**: `test_mus.py:114` is `assertTrue(... or True)`;
      `test_integration.py:93` accepts either exit code in a test named for
      rejecting a corrupted proof; `test_packaging.py:77-79` guards on a file
      that does not exist so `main()` is never called.
- [ ] **Three cross-engine tests degenerate to single-engine** when native is
      absent (`test_pyeq.py:420`, `test_portfolio.py:153`, `test_pipeline.py:131`)
      -- on the dependency-free CI matrix they run the same engine twice and
      report PASS.
- [ ] **Coverage floor margin is 0.0 points** (75% against a floor of 75).
      Statement-only, no branch coverage.

**Done when:** the bit-exactness suite exercises clause reduction, rephasing and
restart blocking; `brute.py` has an independent oracle; and no test can pass
without testing something.

---

## Sprint 4 -- Publish

- [ ] Reserve the name on PyPI **before** announcing anywhere.
- [ ] Trusted publishing via GitHub OIDC, no long-lived token.
- [ ] Make the repo public; the URL in `pyproject.toml` currently 404s.
- [ ] Tag a signed release with wheels, `tex/cdclkit.pdf`, and
      `bench/baseline.json` attached (see `docs/RELEASING.md`).
- [ ] Sigstore attestations on the wheels. For a project whose pitch is
      verifiable provenance of *answers*, unverifiable provenance of the
      *artefact* is the obvious hole, and CI already builds them.

**Done when:** `pip install <name>` works from a clean machine and the
quickstart runs.

---

## Sprint 5 -- The product

- [ ] **Extract the checker as its own distribution**: pure-Python wheel,
      optional Rust accelerator, both engines exposed so a caller can demand
      agreement rather than trust one.
- [ ] **File the CaDiCaL/PySAT proof bug.** Reproducible and confirmed: proofs
      obtained through PySAT's `get_proof()` from CaDiCaL153 failed to verify on
      4 of 5 `uuf100` instances, and **drat-trim agrees on all 10 cases tested**.
      Every individual step verifies; the empty clause is never derived, and it
      is not RUP at the end. Deterministic across runs (1,815 lines each time).
      One probe still needed to say whether the gap is in PySAT's binding or in
      CaDiCaL's DRUP emission -- that decides who to file with.
- [ ] **PySAT cannot parse standard SATLIB files** (`ValueError: invalid integer
      token` on the trailing `%`), and this parser can. Small, but it is the
      kind of thing that makes a tool feel solid on first contact. Worth a line
      in the README and possibly a patch upstream.
- [ ] **LRAT output**, which is what `cake_lpr` consumes. That is the bridge
      from "carefully written checker" to "feeds a formally verified one", and
      it is the single strongest addition available to the trust story.
- [ ] **Backward checking**, optional. Would close the 1.75x gap against
      drat-trim on large proofs. Not required to ship.
- [ ] **Second-machine benchmark validation.** Every performance figure in this
      repository comes from one host.

---

## Open questions

Sprint 0 is closed. What remains undecided:

1. **What is the toolkit renamed to?** `dratify` is the checker. The solver,
   preprocessor, encodings and modelling layer still live under a name that is
   taken on PyPI. Free on both registries as of 2026-08-29: `sablesat`,
   `cdclkit-sat`, `certisat`, `refutex`, `nosat`, `unsatproof`. This only needs
   deciding before the *toolkit* is published, not before `dratify` is.
2. **Does the toolkit get published at all**, or does it stay a public repo
   without a PyPI release? A repo people can read and audit is most of the
   reputational value; a package is a maintenance commitment.
3. **Does `dratify` vendor its own copy of the checker, or import it?** Today
   `packages/dratify/src/dratify/{lits,cnf,proof}.py` is a copy of the files in
   `cdclkit/`. That is fine for one release and becomes a divergence bug by the
   third. Either the toolkit depends on `dratify`, or the files get a single
   home and a sync check in CI.
4. **Does the Rust accelerator ship as `cdclkit-native` or its own wheel?**
   `dratify[native]` currently points at `cdclkit-native`, which is the wrong
   name for a dependency of a package called `dratify`.
5. **LRAT priority.** It is the bridge to `cake_lpr` (CakeML-verified) and the
   strongest available addition to the trust story. Sprint 5 as written, but it
   could reasonably jump ahead of the toolkit rename.
