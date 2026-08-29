# Do LLM refactors preserve behaviour, and does `pyeq` earn its keep?

**Run 2026-08-29. `cdclkit` at `402d8d6`, Python 3.14.6, Hypothesis 6.165.10,
CrossHair 0.0.110, macOS arm64. Every number below is from `results.jsonl` and
`results_phase2.jsonl` in this directory.**

## Verdict

**The product hypothesis, as stated, is not supported.**

`pyeq`'s marginal catch rate over an equally-informed competitor is **0 of 105
pairs, 95% CI [0.00%, 3.53%]**. CrossHair, given the same fixed-width semantics,
found every single difference `pyeq` found — 9 differs and 96 same, with zero
disagreement across all 105 pairs. There is no bug in this corpus that `pyeq`
catches and a competent free tool does not.

**But the experiment found something else, and it is more useful than the thing
it was looking for.**

The variable that decides whether a refactor bug is found is **not the tool. It
is the semantics you declare.**

| | refactors flagged | 95% CI |
|---|---|---|
| change behaviour at **fixed width** (8 or 16 bits) | **9 / 105  (8.57%)** | [4.57, 15.49] |
| change behaviour in **Python's unbounded integers** | **2 / 105  (1.90%)** | [0.52, 6.68] |
| **invisible to any amount of Python-semantics testing** | **7 / 105  (6.67%)** | [3.27, 13.13] |

Seven of nine real bugs are undetectable by a correct, exhaustive,
arbitrary-precision Python test suite, because at arbitrary precision the two
functions **are** equal. They differ only once the values live in an `int8`, an
`int16`, a C `int`, a Java `int`, or a database column.

## The evidence that this is not hypothetical

The refactoring agents were not told a verifier existed. Two of them
volunteered their own verification, unprompted:

- One reported **362,642 comparisons, 0 mismatches**.
- Another reported **483,020 comparisons, 0 mismatches**, plus an exact
  return-type check.

Both were run in Python semantics. Both passed. **Both models had, in that same
output, changed fixed-width behaviour.**

One stated the reasoning explicitly:

> "Dead saturation logic removed. Python ints don't wrap, so the guards are
> unreachable: `a > 0 and b > 0` forces `s > 0`."

That is correct about Python and false about every fixed-width target. It
deleted the entire body of `f_sat_add`, `f_sat_sub` and `f_double_clamped` —
functions whose *only reason to exist* is the clamp at ±127. At width 8,
`f_sat_add(-128, -64)` returns `-128` before and `64` after: a saturating add
that wraps is worse than no saturating add at all.

This is not a slip to be fixed by a better prompt or a larger sample. It is
sound reasoning from an unstated premise. A model asked to preserve behaviour
will preserve *Python's* behaviour unless the width is part of the question.

The contrast is sharp. A second pass from the same model tier kept those
branches and said why:

> "the saturation branches are mathematically unreachable under Python's
> unbounded ints... I kept them... that stays equivalent under **both**
> unbounded-int and fixed-width-bitvector interpretations"

Same model family, same corpus, opposite outcome — decided entirely by whether
the fixed-width reading was considered.

## Full cross-tabulation

288 pairs = 48 functions × 6 passes (3 model tiers × 2 prompt conditions).
183 were returned byte-identical and are excluded from every rate above;
**105 were substantively changed**. Adjudicated at widths 8 and 16 → 210 verdicts.

| outcome | count |
|---|---|
| proved equivalent, DRAT certificate emitted **and replayed** | 192 |
| refuted, with a counterexample | 18 |
| undecided (budget exhausted) | **0** |
| `UnsupportedConstruct` | **0** |
| counterexamples that failed independent re-simulation | **0** |
| pairs excluded by the fall-off-the-end guard | **0** |

The nine refuted pairs, and who else found them:

| function | pass | Python-semantics sampling | CrossHair (fixed-width) | CrossHair (Python) |
|---|---|---|---|---|
| `f_clamp` | haiku-2 | all four caught it | differs | differs |
| `f_min2` | haiku-2 | all four caught it | differs | differs |
| `f_max2` | haiku-2 | **missed by all** | differs | same |
| `f_max3` | haiku-2 | **missed by all** | differs | same |
| `f_cond_swap_hi` | haiku-2 | **missed by all** | differs | same |
| `f_diff_or_zero` | haiku-2 | **missed by all** | differs | same |
| `f_sat_add` | opus-1 | **missed by all** | differs | same |
| `f_sat_sub` | opus-1 | **missed by all** | differs | same |
| `f_double_clamped` | opus-1 | **missed by all** | differs | same |

"Python-semantics sampling" is 200 random vectors, 20 random vectors, the full
edge-case product, and Hypothesis at 1000 examples — all four, all passing.

Four of six passes (`sonnet-1`, `sonnet-2`, `haiku-1`, `opus-2`) produced
**zero** behaviour changes at either width. The failures concentrate in the
cheap model under an aggressive prompt, and in one frontier-model pass that
reasoned its way into an unstated-premise error.

## What `pyeq` actually has that CrossHair does not

Not catch rate. Two things:

1. **A certificate.** All 192 "equivalent" verdicts emitted a DRAT proof that an
   independent checker replayed — median 510 steps, max 399,424. CrossHair's 96
   "same" verdicts mean *no difference found in 10 seconds*. Both were right
   here; only one of them can say why. That is a trust difference, not a
   detection difference, and it is the same distinction this project already
   draws between a solver's answer and a checked proof.
2. **Exhaustiveness.** A `pyeq` `True` covers every input at the declared width.
   CrossHair's silence is bounded by its timeout.

Whether anyone pays for that is a separate question this experiment does not
answer. It does establish that the pitch cannot be *"we find bugs your tests
miss"* — CrossHair finds them too, for free — and has to be *"we prove the
absence of bugs, and we tell you which semantics you're proving it in."*

## Scaling limit, and it lands badly

The worst cases are the branchless mask idioms — which is exactly what an
aggressive refactoring prompt produces.

| function | pass | width | seconds | conflicts |
|---|---|---|---|---|
| `f_cond_negate` | haiku-2 | 16 | **728.5** | 170,271 |
| `f_cond_negate` | opus-2 | 16 | 104.9 | 85,283 |
| `f_abs` | sonnet-2 | 16 | 60.9 | **65,536** |

`f_abs` at width 16 took 65,536 conflicts — precisely 2^16. On the
`(a ^ m) - m` negate identity the solver is enumerating the input space, not
reasoning about it. Three of 210 verdicts consumed 87% of the total 18 minutes.

This is the known "no XOR/Gaussian reasoning" limitation arriving in the one
place it hurts most: the idiom LLMs reach for when told to go branchless is the
idiom CDCL is worst at. Widening `pyeq` to bigger integers is not a matter of
patience.

## Subset coverage

Zero `UnsupportedConstruct` across 210 verdicts — including the mask, SWAR and
comparison-as-value forms the aggressive prompt produced. That is a better
coverage result than expected.

The honest counterweight is at authoring time: **5 of 53** naturally-written
corpus functions (9.4%) were rejected and had to be dropped, all for the same
cause — shifting by a loop variable. `unroll_for` binds the loop variable to a
constant in `self.env`, but `binop` tests `isinstance(node.right, ast.Constant)`
at the AST level and never consults that environment. A fixable oversight rather
than a design limit, and it is recorded in `corpus.py` as `SUBSET_REJECTED`
rather than worked around, because rewriting those functions to fit would have
hidden the coverage gap the experiment was measuring.

## Threats to validity

- **Underpowered below ~3.5%.** 0/105 excludes a marginal rate above 3.53% and
  says nothing below it. Pre-registered as such.
- **The corpus is small integer functions.** It is the domain `pyeq` supports,
  and it is not representative of production Python.
- **The fixed-width baselines are stronger than any real team's.** Building them
  required an AST transform that masks every operation — the very thing most
  teams have not done. The 0% marginal rate is against a competitor that had to
  be constructed for this experiment; the 6.67% is against what people run.
- **Two implementations, deliberately.** Fixed-width semantics is implemented
  twice here — an AST interpreter (`wrapping.py`) and a source transform
  (`baselines.py`) — cross-checked at 23,040 points across widths 4/5/8/16, 0
  disagreements. This was not ceremony: it caught three harness bugs that would
  each have silently corrupted the headline (constants truncated in divisor
  position turning `// 256` into division by zero; `range(8)` truncated to
  `range(-8)`, making every loop body dead; and augmented assignment escaping
  the wrap entirely, so accumulators ran at full precision). The same reason
  `differential_solve` exists in `cdclkit/model.py`: one implementation of a
  translation is an assumption.
- **The known `pyeq` soundness bug did not fire.** The guard excluded 0 of 288
  pairs — no function on either side has a reachable fall-off-the-end path — so
  it does not bias these numbers in either direction.

## What to do with this

1. **Drop "catches what tests miss" as the pitch.** It does not survive contact
   with CrossHair, and CrossHair is free.
2. **The finding worth keeping is the semantics gap.** "Your refactor passed
   845,662 tests and still broke your `int16` pipeline" is a true, demonstrable,
   reproducible claim, and it is the one that made three frontier-model passes
   fail in this run. It also does not require a SAT solver to state — which is
   either the honest thing to admit or the beginning of a much cheaper product.
3. **Certificates are the only defensible differentiator.** Everything else
   here was matched by a free tool in 10 seconds per pair.
4. **Fix the loop-variable shift gap** before quoting any coverage number.
5. **Re-run without the guard once the soundness fix lands.** The difference
   between the two runs measures what that bug was costing; today it is 0.
