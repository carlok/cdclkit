# Verification of the campaign's Critical candidates

Independent check of the findings below, at commit 7946120 on `campaign/soundness`, with the
campaign venv. Everything quoted was produced by running the current code. `cdclkit/`, `tests/`
and `native/` are unchanged. Reproductions were attempted as refutations: for each finding the
question was whether the input is out of contract, whether the output is really wrong, and whether
a documented semantic explains it.

## Verdicts

| Candidate | Proposed | Verdict | One-line reason |
|---|---|---|---|
| preprocess-1 / engines-5 | Critical | **Critical** | `s SATISFIABLE`, `v -1`, exit 10 on `(x1)`: a final answer that falsifies the formula it was handed. |
| modelling-1 | Critical | **Critical**, supported program | `expr()` compiles `and`/`or` on purpose and wrongly; `x or 5` is proved equal to `1`. |
| modelling-2 | Critical | **Critical**, should have been rejected | Walrus statement is dropped: a function returning `x + 1` is proved equal to `x`. |
| modelling-3 | Critical | **Critical**, should have been rejected | The undecorated source is compiled, so `f(1) = 2` is proved equal to `g(1) = 1`. |
| modelling-4 | Critical | **Critical**, should have been rejected | As filed the programs only raise TypeError, but a module-level `range` gives a running program with a wrong proof. |
| modelling-5 | Critical | **Critical** | The returned `Solution` falsifies a clause of the model's own CNF; `add(x == 3)` can return `x = 4`. |
| mus-1 | open | **Critical** for the aftermath, Bug for the crash | `verify` endorses a satisfiable set on a live extractor, and a repeated index is not the only way there. |
| modelling-12 | open | **Bug** | The label is wrong and the circuit is faithful: correcting the width makes every claim true. |
| modelling-6 | Bug | **Bug**, not Critical | A real wrong UNSAT, but the replay rejects it, and no valid proof of it can exist. |

Nothing proposed as Critical was refuted. mus-1 goes up, and its filed reasoning does not hold. The
scan at the end found four findings that meet the literal words of Critical through a wrong encoding.
They stay Bug, for the reason given there, and that call is the orchestrator's to overturn.

## How the two lines are read

The tension between "wrong SAT model" (Critical) and "a preprocessed model does not satisfy the
original formula" (Bug) goes away once you ask what an answer is judged against.

- **Critical**: a final answer is wrong about the formula cdclkit was handed.
- **Bug, preprocessing**: `Preprocessor.reconstruct` gives a bad model when a library caller drives
  the steps. That is an intermediate result, and no verdict has been issued.
- **Bug, encoding**: the CNF is wrong, and the solver answers that CNF correctly.

**preprocess-1 is Critical.** The input is the user's own DIMACS, there is no translation step, and
the CLI prints a verdict and exits 10. `reconstruct` itself is correct; the CLI branch does not call it.

Taking the higher line whenever both seem to apply does not work: every wrong encoding yields either a
model that violates the intent or a wrong UNSAT, so the encoding line would be empty. The rule above
leaves all three lines with content.

The pyeq rule comes from the brief, not from this reading: a wrong `proved=True` is Critical when the
circuit is not the function. A second test separates those from modelling-12: **does correcting a label
make the claim true?** If the circuit is unfaithful at every width, as in modelling-1 to 4, no label
helps.

### Supported, or should have been rejected?

The documented contract is a closed one. CHANGELOG 0.1.0: "Everything outside it raises
`UnsupportedConstruct` with a line number rather than being approximated." So anything accepted is
presented as covered. `UnsupportedConstruct`'s docstring says silent approximation "would make every
'equivalent' answer meaningless", and the module says a verifier that quietly ignores a construct "is
worse than no verifier".

There is a direct precedent. `docs/ROADMAP.md:99-108` opens "The tree must not contain a known false
proof" and lists default arguments that were "silently dropped" and a bare `return` as soundness
defects. modelling-2, 3 and 4 are the same class, so being outside the subset is not a defence: being
outside and accepted is the defect.

The strongest refutation available is the module's warning that "equivalent" means fixed-width
machine integers, not Python programs. It does not apply: the documented gap is wrapping only, and
every counterexample below is in range with nothing overflowing.

## 1. preprocess-1 / engines-5

```
$ printf 'p cnf 1 1\n1 0\n' > d.cnf
$ cdclkit solve d.cnf --preprocess --adaptive        s SATISFIABLE / v -1 / v 0   exit 10
  same with CDCLKIT_ENGINE=python, and with =native
  --preprocess --adaptive --check-model              c MODEL CHECK FAILED         exit 1
  --preprocess --adaptive --self-check               s SATISFIABLE / v -1 / v 0   exit 10
  --preprocess                                       s SATISFIABLE / v 1 / v 0    exit 10
  --adaptive                                         s SATISFIABLE / v 1 / v 0    exit 10
```

**Oracle, 120 random formulas (up to 6 variables), both engines, each printed model evaluated
clause by clause:**

| Flags | Wrong model | Right model | UNSAT right |
|---|---|---|---|
| `--preprocess --adaptive` | **48 of 64** on each engine | 16 | 56 of 56 |
| `--preprocess` | 0 | 64 | 56 of 56 |
| `--adaptive` | 0 | 64 | 56 of 56 |

So this is the common case on this route, not a corner. `--check-model` turned all 48 into exit 1.

**By hand:** the only clause is `(x1)`, and `v -1` sets x1 false. Also new: `--preprocess --adaptive
-j 2` is affected, on `(1 2)(-1 3)(-2 -3)` printing `v -1 -2 -3`, which falsifies `(1 2)`.

**Cause:** `cdclkit/cli.py:111` replaces `f` with the reduced formula, `:141` solves it, `:153` and
`:159` use `pr.model` directly, and `:160` returns before the only `pre.reconstruct`, at `:202`.
`solve_adaptive` in the library returned `[True]` on both engines, so the library is unaffected.

## 2. modelling-1

```
x and x vs 1-if-x   python (proved True, checked True)  native (True, True)   6/8 inputs differ
x or x  vs 1-if-x   python (True, True)                 native (True, True)   6/8 inputs differ
x or 5  vs 1        python (True, True)                 native (True, True)   7/8 inputs differ
x and 5 vs 1-if-x   python (True, True)                 native (True, True)   7/8 inputs differ
x and x vs x        proved False, overflow_only True    both engines          0/8 inputs differ
controls, all correct: not x; (x>0 and x<3) as a value; if x and x:
```

The last column is brute force over all 8 inputs at 3 bits, running the Python functions.

**By hand:** at x = 2, within the range -4..3, `2 and 2` is 2 and `1 if 2 else 0` is 1. Nothing
overflows, and `x or 5` at x = 2 is 2, not 1.

**Cause:** `cdclkit/pyeq.py:288-290` routes `ast.BoolOp` through `truth()`, which `:375-376` makes 1
for any non-zero operand. Comparisons in value position are right, because `True == 1`. That is why
the tests and the report's "comparison-as-value" forms pass.

**Supported:** this is an explicit branch, not an omission. The false `proved=False` half is
separately wrong: the docstring says a spurious counterexample is a bug here, and `overflow_only`
blames an overflow that never happens.

## 3. modelling-2

```
walrus      proved True, checked True, both engines   8/8 differ   first (-4, -3, -4)
generator   proved True, checked True, both engines   8/8 differ   returns a generator object
x % 0       proved True, checked True, both engines   8/8 differ   ZeroDivisionError
x // 0      proved True, checked True, both engines   8/8 differ   ZeroDivisionError
controls: return (y := x) rejected; x + 1 and a docstring correctly accepted
```

**By hand:** `walrus(1)` assigns 2 and returns 2; `identity(1)` returns 1.

**Cause:** `cdclkit/pyeq.py:446-448` returns for any `ast.Expr` whose value is not directly a `Call`.

**Should have been rejected:** the walrus is enough for Critical on its own, being two total
integer functions. The other two have precedent in `result()`'s comments, which treat a non-integer
outcome as a false proof.

One sub-claim is weaker than filed: `[print(x) for i in range(1)]` is accepted, which should be
fixed, but it returns the right integer on 8/8 inputs. It is not a wrong `proved=True` by itself.

## 4. modelling-3

```
@double with functools.wraps   proved True, checked True, both engines   7/8 differ   first (-4, -8, -4)
@double without wraps          UnsupportedConstruct: function calls
dec.__wrapped__ is the undecorated function; dec(1) = 2, g(1) = 1
```

**By hand:** `dec(1)` is `1 * 2`, and the function it was compared with returns 1.

**Cause:** `inspect.getsource` at `cdclkit/pyeq.py:539` follows `__wrapped__` and `:545-547` takes the
`FunctionDef`, whose `decorator_list` is never read. The callable checked is not the callable given.

**Should have been rejected:** this is the case `UnsupportedConstruct`'s docstring names, a proof that
covers "a simplification" of the code.

## 5. modelling-4

```
range()            proved True, checked True, both engines   8/8 differ: TypeError
range(stop=3)      proved True, checked True, both engines   8/8 differ: TypeError
local range = 7    proved True, checked True, both engines   8/8 differ: TypeError
range(1, 2, 0)     bare ValueError from the compiler, not UnsupportedConstruct
control range(1)   proved True, 0/8 differ
```

As filed, this was the one place a downgrade looked possible: these programs cannot run at all, so
nobody ships them believing they work. A variant removes that defence, and it is new here:

```python
def range(n):               # at module level
    return (0, 0, 0)

def f(x):
    for i in range(1):
        x = x + 1
    return x

def plus_one(x): return x + 1
```

```
python proved True proof_checked True
native proved True proof_checked True
f(1) = 4  plus_one(1) = 2
```

**By hand:** `f` iterates three times, so it adds 3, not 1. All 16 inputs at 4 bits differ.

**Cause:** `cdclkit/pyeq.py:470-471` matches the name `range` only, `:474` reads `call.args` and never
`call.keywords`, and `:479` turns no arguments into `range(0)`.

**The finding's fix is incomplete:** rejecting `range` when bound in `env` misses this variant. It must
also consult `fn.__globals__` and closures.

**Should have been rejected:** Critical. The three filed forms carry the least practical weight, and
the module-level form is an ordinary wrong integer.

## 6. modelling-5

```
first 2 | added x != 2 | second 2
clauses [[1,2,3],[-1,-2],[-1,-3],[-2,-3],[-3]]   bits [-1,-2,3]   falsified [[-3]]   oracle satisfiable True
AGENTS.md's form, add(x == 3) on range(1, 5), after a solve:  x = 4, CNF not satisfied
a and not a after one solve:  a Solution; a fresh build gives False; before any solve, None
control, a new variable added after the constraint:  2 -> 1, CNF satisfied
```

Evaluated from the DIMACS clauses, not with the repo's `is_satisfied_by`. **By hand:** the last unit
clause says x3 is false, and the returned bits set x3 true.

**Cause:** `cdclkit/model.py:321` judges staleness by `s.nvars < self.cnf.nvars` only. Unlike the
encoding Bugs, the CNF here is right and the answer violates it, so this is Critical without any
appeal to intent. Solving and then adding a constraint is the standard incremental idiom.

## 7. mus-1

### The crash: Bug

```
IndexError: list index out of range | solver.py:729 <- 827 <- 1217 <- 1329 <- mus.py:65
```

`MUSExtractor(f).is_unsat([0, 0, 1])`. A crash on valid input with no wrong answer. Python only.

### The aftermath: Critical

```
raised: list index out of range | seen dirty: [2, 4]
deletion: [1, 3]
verify:   (True, 'verified: unsatisfiable, and all 2 clauses are necessary')
oracle.satisfiable(set): True
fresh extractor verify: (False, 'the subset is satisfiable') | fresh deletion: [0, 1, 2, 3]
```

**By hand:** the set is `(-1 2)` and `(-1 -2)`, and x1 = false satisfies both.

The literal text is met: a wrong UNSAT that passes the project's documented self-check, whose
docstring says "Check the defining property". The finding proposes Bug because the caller was already
told something went wrong. Three things undercut that.

1. **Nothing says the object is dead.** No document does, and later answers carry no taint.
2. **The exception looks benign.** An out-of-range index raises the same `IndexError` from
   `mus.py:65` and leaves the extractor healthy (checked: `is_unsat([99])`, then a right answer).
   Code that catches `IndexError` as "bad input" and carries on cannot tell them apart.
3. **A repeated index is not needed.** This is new, and it is the main point. The finding says "no
   repeated index and no caught exception means no wrong answer"; the second half is what matters,
   and any exception will do. An asynchronous `KeyboardInterrupt`, raised from a timer signal's
   handler the way Python's default handler raises it for Ctrl-C, on a formula with no repeats:

```python
signal.signal(signal.SIGALRM, handler)        # handler raises KeyboardInterrupt
ex = MUSExtractor(php_6_5)                    # 81 clauses, minimally unsatisfiable
signal.setitimer(signal.ITIMER_REAL, delay)   # 0.5 to 20 ms
try:
    ex.is_unsat(list(range(81)))
except KeyboardInterrupt:
    pass
r = ex.deletion()
ex.verify(r)
```

Every set was judged by an explicit model from a fresh solver, evaluated clause by clause. Timer
delivery is not deterministic, so these are rates, not exact counts:

| Run | Interrupted | State after | Outcome |
|---|---|---|---|
| A | 35 | 19 `seen` dirty | **19 satisfiable sets, all 19 endorsed by `verify`**; 13 no smaller set; 3 raised (not split by `seen`) |
| B | 22 | 13 `seen` dirty | **13 satisfiable sets, all endorsed** |
| B | | 9 `seen` clean | 8 right, 1 `AttributeError` |

Interrupting a long extraction in a notebook and re-running the cell on the same object is the
ordinary way to meet this.

**Repeated indices, random formulas, oracle:**

- 37 of 4877 repeated-index lists raised. A later `deletion()` returned a satisfiable set for 2 of
  those 37, both endorsed by the same extractor and rejected by a fresh one.
- The other 4840 answered correctly, so a repeat alone never gives a wrong answer.
- Distinct indices: 0 of 6000 raised, 0 wrong.
- Distinct `Solver` assumptions: 0 of 3426 raised, 0 wrong.

**A correction to the finding's reasoning:** "each level uses up a variable" is not quite right. A
distinct assumption already implied by propagation also opens a dummy level, at `solver.py:1288`. The
conclusion survives, because each level still maps to a distinct variable when no variable is repeated.

**The DRAT path is safe:** a plain `Solver` with a proof sink, on planted-satisfiable 3-SAT, interrupted
25 times, gave 5 wrong UNSAT on the next solve, and **all 5 replays were rejected**. So only `verify`
is fooled, because it asks the same poisoned solver and has no proof. That is what makes this Critical,
and it also suggests the fix: `verify` should use a fresh solver.

**The filed fix is partial:** clearing `seen` in the `finally` at `solver.py:1335` matches run B's 1:1
link between dirty `seen` and wrong sets, but the clean-`seen` run that raised `AttributeError` shows
other state can be left inconsistent. (A trace from an earlier interrupt run put an `AttributeError` at
`solver.py:753`, a missing reason clause.) That cause was not traced.

**Cause, confirmed:** `_lbd_stamp` has one slot per variable (`solver.py:449`), `_lbd` indexes it by
level (`:729`), and `_analyze` calls `_lbd` at `:827` before clearing `seen` at `:828-829`.

**Priority:** Critical on the definition, with a narrow route. It needs an exception and then reuse of
the same object. `mus()`, `shrink_core()` and the CLI build a new extractor per call and cannot reach
it. Fixing it after preprocess-1 and modelling-1 to 5 is reasonable.

## 8. modelling-12: Bug

```
{'a': 4}                proved True   width 4   c equivalent at 4 bits
{'a': 4, 'unused': 8}   proved True   width 8   c equivalent at 8 bits
{'a': 8}                proved False  width 8   c NOT equivalent at 8 bits: a=8 -> -128 vs 0
{}        c vs d        proved True   width 0   c equivalent at 0 bits     Python 300, 44
{'z': 16} c vs d        proved True   width 16  c equivalent at 16 bits    Python 300, 44
output width with and without 'unused': 4 and 4
```

**By hand:** `a * 16` wraps to 0 at 4 bits, and at 8 bits `a = 1` gives 16.

**Cause:** `cdclkit/pyeq.py:801` uses all of `widths`; `:576` uses the parameters, or 8 when there are
none.

**Why Bug:** `EquivalenceResult` promises agreement "at the declared widths". `unused` declares no
parameter, and `a` is declared 4, where the claim is true. Correct the label and every statement holds,
unlike modelling-1 to 4. It is not a Note either, because `report()` states something false.

**The sharpest form, new here,** uses only a key that names a real parameter:

```python
def c(a, /): return 300
def d(a, /): return 44
equivalent(c, d, {"a": 16})   # proved True, checked True, width 16, "equivalent at 16 bits", both engines
```

300 and 44 differ at 16 bits with nothing overflowing. The root is modelling-13's: `tree.args.args`
omits `posonlyargs`, so the names are empty and the circuit falls to the hidden 8. It is still fixed by
correcting the width, so it stays Bug, but this one is a clearly false claim at a properly declared
width. If the orchestrator reads "in the bit width it claims" strictly, this and the `{'z': 16}` case
are the ones that become Critical.

## 9. modelling-6: Bug, not Critical

```
solutions: 2 | then solve(): None
clauses [] , oracle satisfiable True
with a proof: None | steps 0 | ok False | every step verified, but the proof never derives the empty clause
```

**By hand:** the model has no clauses, so `a = true` is a solution.

**Does it meet Critical?** No. The definition needs a self-check that passes, and every route tried
fails it:

- `m.solve(proof=p)` after `solutions()`: the proof stays empty and replay rejects it.
- A solver built with a proof and enumerated directly: steps `[('a', ()), ('a', ())]`, rejected as
  "neither RUP nor RAT". The blocking clauses are not logged.
- In principle: the CNF is satisfiable, so no valid DRAT refutation exists. Passing would need a checker
  bug, and that would be a different finding.

Two things keep this serious. The default `m.solve()` asks for no check at all. And the same replay also
rejects a *correct* UNSAT from a stale solver (modelling-5's last lines), so the rejection means "no
proof was produced", not "this answer is wrong".

The severity list has no line for a wrong UNSAT without a passing check. Bug is the closest fit.
**Fix it with modelling-5**, which shares the stale `self.solver`.

**A nuance on the finding:** "a partly consumed generator leaves the same state" holds only in part.
The blocking clause is added on resumption, so one or two `next()` calls on a single boolean still
leave `solve()` satisfiable. Exhaustion gives None. Partial enumeration silently excludes the values
already passed, without reaching UNSAT.

**Cause:** `cdclkit/model.py:327` and `:316` store the enumerating solver, and `:320` reuses it.

## Scan of the remaining findings

### Meets the words of Critical, kept at Bug

These four findings give a **wrong UNSAT with a passing DRAT replay**:

| Finding | Input | Solve | Replay | True answer |
|---|---|---|---|---|
| modelling-9 | `x.le(1)` over `[2, 1]` | None | ok | `x = 1` |
| modelling-7 | `add(a)`, `add(True)` | None | ok | `a = true` |
| modelling-7 | `add(~a)`, `add(~b)`, `add(a == b)` | None | ok | `a = b = false` |
| encodings-2 | `x1 + x2 >= 2`, `max_count=1` | False | ok | `x1 = x2 = true` |
| encodings-4 | at-most-one over undeclared `x1, x2`, plus `x2` | False | ok | `x1 = false, x2 = true` |

The mechanism is exactly modelling-1's: the proof is valid and the CNF is not the question. They stay
Bug because the severity list names this case, "an encoding has the wrong solutions", and promoting
them would empty that line. The answer is right about the CNF the solver was given, which the encoding
produced. The pyeq rule differs because the brief says so, and `proved=True` is a verdict on functions.

**This is the orchestrator's call.** If the concern is what a user ends up believing, these belong with
the Criticals. Of them, **modelling-7 is the one to fix first regardless**: `m.add(a == b)` on two
BoolVars is natural code, evaluates to `False`, and silently asserts `a`. It returned `a = True,
b = False` here.

### Checked and not Critical

- **modelling-8, modelling-10, encodings-3:** extra solutions from an encoding. Same reasoning, Bug.
- **engines-4:** native returns `False` with stale model `[True]`; Python returns `False []`.
  Reproduced. The verdict is right and nothing presents the model as one. Bug.
- **modelling-17:** `f(a) = a` vs `a + 1` is proved at widths 0 and -1, with `proof_checked` True, on both
  engines. At 0 bits it is vacuously true and at -1 it is meaningless, and the report prints the width.
  The closest call in the scan. Any pair passes, so a computed width of 0 turns a CI gate into a no-op.
  Not Critical, but Bug fits better than Note.
- **encodings-6:** `solve_with_bound(-1)` returns `[]` and `run(target=-1)` returns `(0, [])`. Reproduced.
  No clause is violated, only an impossible bound. It behaves like encodings-3, so Bug fits better than
  Note, though it has no effect on `optimise()`.
- **engines-1, preprocess-4:** the UNSAT answers are correct (56 of 56 above) and the proofs hold under
  dratify's documented rule. Note.
- **modelling-16:** a differential check that compares a CNF with itself says nothing but says nothing
  false. Note.
- **encodings-1, encodings-5, engines-2, engines-3, engines-6, engines-7, engines-8, engines-9,
  modelling-11, modelling-13, modelling-14, modelling-15, mus-2, mus-3, preprocess-2, preprocess-3:** crashes,
  engine differences, unhonoured budgets or overstated documentation, with no wrong model and no wrong
  UNSAT in the finding. Read from the finding text in this scan, not re-run, except that modelling-13's
  root also produces the false width claim in section 8.
