# The mathematics behind cdclkit

This document explains *why* the implementation is shaped the way it is. It is
written for someone reading the source and wanting to know which parts are
forced by theory and which are engineering choices that could have gone
differently.

---

## 1. Resolution, and what a CDCL solver is actually doing

The resolution rule is the whole foundation:

```
    C ∨ x        D ∨ ¬x
    ─────────────────────
         C ∨ D
```

**Soundness.** Any assignment satisfying both premises satisfies the conclusion:
if it sets `x` true then `D ∨ ¬x` needs `D`; if false, `C ∨ x` needs `C`.

**Refutation completeness.** If a CNF formula `F` is unsatisfiable, repeated
resolution derives the empty clause. (Not *completeness* — resolution does not
derive every consequence — but refutation completeness is what matters.)
`cdclkit/brute.py::resolution_refute` implements the saturating version and the
test suite uses it as ground truth: everything the CDCL solver refutes must be
refutable there.

The connection to CDCL: **every clause a CDCL solver learns is a resolvent
chain over the clauses it already has.** Conflict analysis starts from the
conflicting clause and repeatedly resolves it against the reason clause of the
most recently assigned literal at the current level. So a CDCL run *is* a
resolution derivation, discovered by a search heuristic rather than by
saturation. This is why:

- CDCL inherits resolution's exponential lower bounds. Haken's 1985 result says
  pigeonhole formulas `PHP(n+1, n)` require resolution refutations of size
  `2^Ω(n)`. `bench/run_bench.py` shows the curve directly: 650 → 3025 → 13216
  conflicts for n = 6, 7, 8. No heuristic escapes this; only a stronger proof
  system does (which is what the RAT rule opens the door to).
- Every learnt clause is **RUP** (section 4), so the proof format needs no
  justification data — just the clause.

---

## 2. Unit propagation and two watched literals

A clause is *unit* under a partial assignment when exactly one literal is
unassigned and the rest are false; that literal must then be true. Propagating
to fixpoint is the single hottest operation in the solver — typically 80–90% of
runtime.

The naive scheme visits every clause containing a literal that just became
false. Two-watched literals is the standard improvement:

> **Invariant.** Each clause of length ≥ 2 watches two of its literals. As long
> as neither watched literal is false, the clause cannot be unit or conflicting.

So a clause needs attention only when one of its *watched* literals becomes
false. On that event we look for a replacement watch among the others; if none
exists, the clause is unit (or conflicting) and we act.

Three consequences that shape `Solver._propagate`:

1. **Backtracking costs nothing.** Unassigning a literal cannot violate the
   invariant (it only makes literals *less* false), so watch lists are never
   repaired on backtrack. This is the property that makes the scheme beat
   counter-based propagation.
2. **The watched pair is unordered and mutable**, so `lits[0]` and `lits[1]` are
   swapped freely. The one exception the code depends on: when a clause is the
   *reason* for an assignment, `lits[0]` is the propagated literal. That holds
   because a reason clause has `lits[0]` true, and the propagation loop only
   swaps position 0 when it holds the newly-false literal.
3. **Blockers.** Each watcher caches a second literal of the clause inline. If
   that literal is already true, the clause is satisfied and can be skipped
   without dereferencing the clause object at all — a large constant-factor win
   in any language, and an especially large one in Python where attribute
   access is expensive.

---

## 3. First-UIP conflict analysis

When propagation hits a conflict, the *implication graph* has nodes for assigned
literals and edges from the antecedents of each propagation. A **unique
implication point** (UIP) at the current decision level is a node every path
from the decision to the conflict passes through. The decision itself is always
a UIP; the **first** UIP is the one closest to the conflict.

The algorithm (`Solver._analyze`):

```
counter ← number of current-level literals in the conflicting clause
clause  ← the rest of its literals
while counter > 1:
    p ← most recently assigned literal on the trail that is marked
    resolve the reason of p into the clause, updating counter
learnt ← ¬p ∨ clause
```

Why first-UIP is the standard choice:

- **The learnt clause is asserting.** After backjumping to the second-highest
  level in the clause, every literal but one is false, so it immediately
  propagates. Search never repeats the failed assignment.
- **It is the *closest* such cut**, giving the shortest clause among the UIP
  cuts, and short clauses propagate more often.
- Backjumping is **non-chronological**: it can skip many levels at once, which
  is where the exponential separation from DPLL comes from.

### Clause minimisation

The first-UIP clause frequently contains literals implied by the others. If
literal `l` has a reason whose other literals are all already in the clause (or
root-level), then `l` is redundant: resolving it away yields a clause that
subsumes the original. `Solver._lit_redundant` walks the implication graph
backwards to test this transitively.

The `abstract_levels` bitmask is a bloom filter over decision levels: a 32-bit
word with bit `level mod 32` set for each level in the clause. A literal whose
level is not represented cannot be redundant, and it is rejected without
touching its reason clause. Cheap and very effective.

Measured effect in this implementation: **11711 conflicts without minimisation
versus 5914 with**, on a 200-variable random 3-SAT instance.

---

## 4. LBD, and why clause length is the wrong metric

**Literal block distance** of a clause is the number of distinct decision
levels among its literals. Glucose's insight: a clause with LBD 2 links only
two decision levels, so once one of them is fixed the clause behaves like a
short constraint. LBD predicts future usefulness far better than length does.

cdclkit uses it in three places:

- clauses with LBD ≤ 2 ("glue clauses") are never deleted;
- database reduction ranks by LBD first, activity second;
- restarts are driven by LBD moving averages.

The LBD of a learnt clause is also **recomputed on every use** (`_analyze`): if
a clause's LBD has dropped since it was learnt, it has become more useful, and
its score is improved in place.

### Restarts

Two policies, both implemented:

**Luby.** Restart budgets follow `1,1,2,1,1,2,4,1,...` scaled by a base. The
sequence is optimal to within a log factor for any distribution of runtimes
when nothing is known about it (Luby, Sinclair, Zuckerman 1993) — the right
choice when runtimes are heavy-tailed, which satisfiable instances are.

**Glucose EMA.** Track a fast (α = 1/50) and a slow (α = 1/5000) exponential
moving average of learnt-clause LBD. Restart when
`fast × 0.8 > slow`: recent clauses are markedly worse than the long-run norm,
so the current region is unproductive. A *blocking* rule suppresses the restart
when the trail is much deeper than usual (`|trail| > 1.4 × trail_ema`), on the
theory that an unusually deep trail means a model may be close.

Both EMAs use Biere's bias correction: the smoothing factor starts at 1 and
halves on a schedule until it reaches α, so the average is usable immediately
instead of spending thousands of conflicts crawling away from zero.

Glucose EMA **was** the default, on the reasoning that unsatisfiable instances
dominate the hard cases. Measurement retired both the default and the
reasoning.

Against kissat over 203 public instances, Luby restarts paired with target
phases move the geometric mean from **1.62x behind to 0.84x ahead**, and they
improve both halves rather than trading one for the other:

| | Glucose + saved phases | Luby + target phases |
|---|---|---|
| uf250 (satisfiable) | 3.25x behind | **1.02x** |
| uuf250 (unsatisfiable) | 0.84x ahead | **0.72x ahead** |
| all 203 | 1.62x behind | **0.84x ahead** |

The satisfiable half is the expected direction: restarting aggressively when
recent LBD degrades can abandon a branch that was descending towards a model.
The unsatisfiable half is not — the refutation argument for Glucose was wrong
on its own terms here, not merely outweighed.

### Phase selection

When the heuristic picks a variable, something has to pick its polarity.

**Saved phases** (default). Remember the value a variable last held when it was
unassigned, and reuse it. Cheap, and it keeps the search near where it just
was, which preserves work that backtracking would otherwise discard.

Its weakness is the same property: it follows the search *wherever it went*,
including into the region a conflict has just pushed it out of. After a
backjump the saved phases describe a failure.

**Target phases** (`Config.target_phase`, off by default). Remember instead the
assignment from the **deepest conflict-free trail ever reached**, and branch
from that. Saved phases follow where the search has just been; target phases
follow the best place it has ever been. On satisfiable instances that is a
different and usually better bet, because depth without conflict is evidence of
being near a model.

The update is O(|trail|) but only fires on a strict improvement, and
improvements become rare quickly, so the amortised cost is small.

### Local-search rephasing (probSAT)

CDCL is weak on satisfiable uniform-random instances; local search is strong on
exactly those. `cdclkit/solver.py::_walk` runs probSAT over the *original*
clauses from the current phases, and the best assignment it finds becomes the
phases the search branches from. It decides nothing — the search still has to
find and verify a model — so proofs are unaffected.

Measured against kissat over 100 uf250 and 100 uuf250 instances, no threshold:

| | uf250 | uuf250 |
|---|---|---|
| Luby + target | 1.017 | 0.725 |
| + walk, ungated | **0.027** | 0.814 |
| + backoff and gate | 0.400 | 0.747 |

The first row of walking looks like a 37x win and is a trap. Ungated, the same
setting is **5.2x slower on small random unsatisfiable instances**, 1.55x on
graph colouring and 1.68x on planning — its fixed cost dominates whenever the
instance was going to be solved quickly anyway. A configuration that wins 37x
on one family and loses 5x on another is fitted to the benchmark, not better.

Two guards make it a defensible default:

**Backoff** (`walk_patience`). Stop after three walks that fail to reduce the
best unsatisfied-clause count. On a satisfiable instance probSAT keeps
improving until it lands a model; on an unsatisfiable one it plateaus at once.

**Effort gate** (`walk_min_conflicts`). Do not walk until CDCL has spent 5000
conflicts. This asks *is CDCL losing?* rather than *does this look like a
random instance?*, which is the question that generalises. It returns every
structured family to neutral or better and costs most — not all — of the
random-SAT win.

The ungated setting survives as a **portfolio worker**, where the cost is one
core and the other workers are untouched.

Two implementation notes that were bugs first. The occurrence index cannot be
cached: root simplification mutates the original clause set mid-search, and it
went stale *differently* in the two engines, which showed up as the walk
diverging on exactly the instances that run long enough to simplify.  And the
probSAT weights are shared `f64` literals rather than each language calling its
own `pow` — a one-ULP disagreement silently flips a comparison mid-walk.

**Neither half is worth much alone.** Measured against the old default over the
same corpus: target phases alone 0.97, Luby alone 0.75, the pair **0.46**. A
target is only useful if the restart schedule leaves the search long enough to
reach it, and long restart intervals are only useful if there is somewhere
worth returning to. This is the pairing CaDiCaL and kissat call *stable mode*,
arrived at here from the measurement rather than from the literature.

Both engines implement it identically — this is a Tier 2 change under
`PLAN.md` §6, so Python remains the reference and the Rust port must reproduce
its conflict counts bit-for-bit.

Note what target phases do **not** touch: which clauses get derived. Phase
selection changes the order the search explores, never the resolution steps it
records, so DRAT proofs stay valid and the certification claim is unaffected.
That is what makes this safe in a way vivification was not.

---

## 5. DRAT: what a proof of UNSAT actually is

### RUP

Clause `C` is **RUP** (reverse unit propagation) w.r.t. formula `F` when
assigning every literal of `C` false and running unit propagation on `F`
produces a conflict. Equivalently: `F ∧ ¬C ⊢₁ ⊥`, where `⊢₁` is propagation
alone.

RUP implies `F ⊨ C`, and it is checkable in time linear in the formula — no
proof structure needed beyond the clause itself. Every CDCL learnt clause is
RUP by construction, which is why a solver can emit a proof by just printing
what it learns.

### RAT

Clause `C` is **RAT** on pivot `p ∈ C` when, for every clause `D ∈ F` containing
`¬p`, the resolvent `C ∪ (D \ {¬p})` is RUP.

RAT clauses need not be entailed — they only preserve satisfiability. That is
strictly more powerful, and it is what allows a proof to justify:

- **blocked clause addition** (every resolvent on the pivot is a tautology, so
  the RAT condition holds vacuously);
- **extended resolution**: introducing a fresh variable `d` with `d ↔ (a ∧ b)`.
  The three defining clauses are all RAT on `d` / `¬d`. Extended resolution has
  *polynomial* refutations of the pigeonhole principle, so DRAT can express
  proofs that no resolution proof — and therefore no CDCL run — can produce.

Both rules are implemented in `proof.py`, RUP first because it succeeds for
essentially every solver-generated line.

### Deletion, and one subtlety

Deletion lines keep the checker's database from growing to the size of the
whole proof. Applying them is safe for RUP because **RUP is monotone in the
formula**: more clauses can only make propagation stronger. Ignoring a deletion
therefore cannot turn an invalid step valid.

Unit deletions are ignored, as in every mainstream checker: a unit already
propagated into the root assignment cannot be cleanly retracted without
restarting propagation, and the cost is not worth the fidelity.

RAT, unlike RUP, is *not* monotone — adding clauses can destroy the RAT
property, since the condition quantifies over all clauses containing `¬p`. So
RAT steps are checked against exactly the clauses present at that moment.

### Forward vs backward checking

cdclkit checks **forward**: replay the proof in order, verify each addition
against the current database. Production checkers (drat-trim) work backwards
from the empty clause and skip lines that never contribute, which is much
faster on large proofs. Forward checking is the right choice here because the
purpose is to validate *the solver*, and a trimmed check silently skips the
rarely-exercised inferences where bugs live.

---

## 6. Encodings: size against propagation strength

An encoding of constraint `C` is **arc consistent** (GAC) when unit propagation
on the encoding fixes every literal that `C` itself would fix, for every partial
assignment. The gap between GAC and non-GAC encodings is regularly worth orders
of magnitude, because a non-GAC encoding forces the solver to *search* for
information the constraint already contains.

| constraint | encoding | aux vars | clauses | notes |
|---|---|---|---|---|
| at-most-1 | pairwise | 0 | n(n−1)/2 | best up to n ≈ 6 |
| at-most-1 | binary/bimander | ⌈log n⌉ | n log n | small, but adds aux vars to the branching space |
| at-most-1 | commander | ~n/2 | ~3.5n | linear *and* arc consistent |
| at-most-k | sequential (Sinz) | nk | ~2nk | `s[i][j] ≡ "≥ j of the first i"` |
| at-most-k | totalizer | ~n log n | O(n²), O(nk) truncated | arc consistent, **incremental** |
| Σ wᵢxᵢ ≤ b | BDD | \|BDD\| | 6·\|BDD\| | exact, arc consistent |
| XOR of n | chain of 3-XOR gates | n−2 | 4(n−2) | direct form needs 2^(n−1) clauses |

Two entries deserve elaboration.

**Totalizer.** A binary tree of unary counters; the root's output `o[i]` is true
iff at least `i+1` inputs are true. The bound is then a *unit clause on an
existing variable* — `¬o[k]` for `≤ k` — so it can be tightened at any later
point without re-encoding anything, or supplied as an assumption to keep it
retractable. That is exactly what an optimisation loop needs, and it is why
`optimise()` in `encodings.py` can tighten the bound repeatedly while the solver
keeps every clause it has learned.

**BDD for pseudo-boolean.** Build the reduced decision diagram of
`Σ wᵢ xᵢ ≤ b` top-down with memoisation on `(index, remaining slack)`, and turn
each node into an ITE gate. Negative weights are handled by
`w·l = w − w·¬l`, moving the constant into the bound. Sorting by decreasing
weight before building keeps the diagram small, since large weights resolve the
constraint earlier.

### Symmetry breaking

Not an encoding of a constraint but of a *quotient*: when a problem has a
symmetry group acting on solutions, the solver re-proves the same thing once per
group element. Graph colouring has the full `k!` colour-permutation symmetry;
constraining vertex `i` to use only colours `1..i+1` removes it. Measured in
`examples/coloring.py` on the 4-colour refutation of M(5): **105 conflicts with,
2067 without**.

---

## 7. Preprocessing changes the model space

Every technique in `preprocess.py` is satisfiability-preserving, but only some
are *equivalence* preserving. The distinction decides whether reconstruction is
needed.

| technique | preserves | reconstruction |
|---|---|---|
| unit propagation | equivalence | assignment recorded |
| subsumption | equivalence | none |
| self-subsuming resolution | equivalence | none |
| pure literal | satisfiability | stack |
| blocked clause elimination | satisfiability | stack |
| bounded variable elimination | satisfiability | stack |

**BVE** (bounded Davis–Putnam) replaces all clauses containing `v` with all
their non-tautological resolvents on `v`. Adding the resolvents is sound
(they are implied); *removing the originals* is what loses equivalence. Without
a bound this is exponential — that is precisely why DPLL replaced Davis–Putnam
in 1962 — so elimination only proceeds when the resolvent count does not exceed
the original clause count.

**Reconstruction.** Walk the elimination stack backwards. For each recorded
variable, if any of its stored clauses is unsatisfied under the current model,
flip the variable to the polarity that satisfies it. This always works, and the
argument is worth stating because the implementation asserts it: clauses of
*both* polarities cannot be simultaneously unsatisfied, since their resolvent on
`v` would then also be unsatisfied — and that resolvent is still in the reduced
formula, which the model satisfies.

**Proof logging.** BVE resolvents are RUP: negate the resolvent, and both
parents become unit on opposite polarities of the pivot, so propagation
conflicts. Preprocessing therefore needs no special proof support — the same
DRAT stream carries preprocessing and search, and
`tests/test_preprocess.py::test_end_to_end_proof_verifies_against_the_original`
checks exactly that on random instances.

---

## 8. What is deliberately absent

- **Gaussian elimination over XOR constraints.** Parity systems are polynomial
  by linear algebra and exponential for resolution. `bench` includes a parity
  family to make the weakness visible rather than hide it.
- **Cardinality detection.** Recognising an at-most-k constraint encoded as
  clauses and reasoning about it natively (as in cardinality-CDCL) is a large
  win on some families and a large implementation.
- **Inprocessing.** Modern solvers interleave preprocessing with search.
  Doing that soundly requires care with proof logging and with the elimination
  stack under learnt clauses.
- **Chronological backtracking**, **vivification**, **rephasing** — post-2018
  refinements that would each need their own correctness argument and their own
  benchmark evidence to justify. Vivification was implemented, measured and
  removed (§9 and the paper record why). **Target phases** are now implemented
  and documented in §4; they are off by default until measured.

---

## 9. Compiler settings, measured

The native engine builds with `opt-level = 3`, fat LTO and `codegen-units = 1`.
Two further levers were tried and **rejected on measurement** (minimum of 5
runs over the five benchmark instances that take real time; the baseline was
re-measured afterwards and reproduced to within 0.05%, so these differences are
real rather than noise):

| build | total | delta |
|---|---|---|
| baseline | 4.5745 s (re-measured 4.5723 s) | — |
| `+ target-cpu=native` | 4.6322 s | +1.3% |
| `+ PGO` | 4.6299 s | +1.2% |

Both are slightly *worse*, and both cost something — `target-cpu=native` makes
the artifact non-portable, PGO needs a two-stage build.

The reason neither helps is worth stating, because it is the same reason the
binary-clause specialisation failed: **a CDCL solver is bound by memory
latency, not by instruction throughput.** The hot loop chases watch lists and
clause offsets through an arena far larger than L1; instruction selection and
branch layout do not address a cache miss. And profile-guided branch layout has
little to work with, because the decisive branch in propagation is "is this
literal false", whose outcome is close to random per execution rather than
consistently biased.

If you want to retry this on different hardware or a workload with more
structure:

```bash
rustup component add llvm-tools-preview
cd native
RUSTFLAGS="-Cprofile-generate=/tmp/pgo-data" ../.venv/bin/maturin develop --release
python3 bench/run_bench.py                     # any representative workload
~/.rustup/toolchains/*/lib/rustlib/*/bin/llvm-profdata \
    merge -o /tmp/pgo-data/merged.profdata /tmp/pgo-data
RUSTFLAGS="-Cprofile-use=/tmp/pgo-data/merged.profdata" \
    ../.venv/bin/maturin develop --release
```

## References

The algorithms are due to their authors; the implementation here is written
from scratch.

- Davis, Putnam (1960); Davis, Logemann, Loveland (1962) — DP and DPLL.
- Haken (1985) — exponential lower bound for resolution on pigeonhole formulas.
- Marques-Silva, Sakallah (1996) — GRASP: conflict analysis and learning.
- Moskewicz et al. (2001) — Chaff: two-watched literals and VSIDS.
- Luby, Sinclair, Zuckerman (1993) — optimal restart schedules.
- Eén, Sörensson (2003) — MiniSat.
- Eén, Biere (2005) — SatELite: subsumption and variable elimination.
- Audemard, Simon (2009) — Glucose: LBD and dynamic restarts.
- Sinz (2005) — sequential counter encoding.
- Bailleux, Boufkhad (2003) — totalizer encoding.
- Klieber, Kwon (2007) — commander encoding.
- Heule, Hunt, Wetzler (2013) — DRAT and drat-trim.
- Järvisalo, Heule, Biere (2012) — inprocessing rules and blocked clauses.
