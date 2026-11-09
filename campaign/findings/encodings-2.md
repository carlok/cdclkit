# encodings-2: A truncated Totalizer answers bounds past its cut wrongly

**Proposed severity: Bug**, "an encoding has the wrong solutions". It needs the public `max_count`
argument and a bound above the cut. Off the requested `at_most_k` grid, on the Totalizer part of it.

## Minimal case

Two inputs, `max_count=1`. Going to one input removes the truncation, and it passes.

## Reproducer

Run from the repo root.

```python
from campaign import dpll
from dratify.cnf import CNF
from dratify.lits import mk_lit, to_dimacs
from cdclkit.encodings import Encoder, Totalizer

def run(method, k):
    f = CNF()
    xs = [mk_lit(f.new_var()) for _ in range(2)]
    enc = Encoder(f)
    t = Totalizer(enc, xs, max_count=1)
    print(method, k, "literal:", getattr(t, method.replace("assert_", "") + "_lit")(k))
    getattr(t, method)(k)
    clauses = [[to_dimacs(l) for l in c] for c in f.clauses]
    print(sorted(dpll.projected_models(clauses, [1, 2])))

run("assert_at_most", 1)
run("assert_at_least", 2)
```

Actual output:

```
assert_at_most 1 literal: None
[(False, False), (False, True), (True, False), (True, True)]
assert_at_least 2 literal: 7
[]
```

## What it should be

`x1 + x2 <= 1` has three solutions, and `(True, True)` is not one. `x1 + x2 >= 2` has exactly one,
`(True, True)`, and the encoding has none. Over these two inputs the expected sets are
`{FF, FT, TF}` and `{TT}`. The second is judged with the oracle as well:

```python
from campaign import oracle
f = [[1], [2]]                 # x1 + x2 >= 2 written out: satisfiable
oracle.satisfiable(f)          # True, while the totalizer's formula is refuted
```

`at_most_lit`'s docstring says "None when the bound is vacuous". `sum <= 1` over two inputs is not
vacuous. The class docstring says the truncated version is "still arc consistent for the bound it was
built for", which reads as a limit on propagation, not as a licence for wrong answers elsewhere.

The first case silently drops a constraint. The second makes a feasible problem unsatisfiable, and a
self-checking UNSAT would pass, because the formula it was given really is unsatisfiable.

The full-counter and in-cut cases all pass. The default run judges 876 bounds past a cut, 438 in each
direction, and all 876 are wrong: every truncated counter fails on every bound above its cut.

## Reach

`Encoder.amk_totalizer` returns a truncated counter, but its own `<= k` is already asserted, so a
later loose at-most is implied and a later `>= k + 2` is truly infeasible. That path is right by
accident. Only a caller of `Totalizer(enc, lits, max_count=m)` reaches this. `Optimiser` builds a full
counter and does not reach it.

## Suspected cause

`cdclkit/encodings.py:656`, `at_most_lit`: `if k >= len(self.outputs): return None` treats "no output
for this bound" as "vacuous". `cdclkit/encodings.py:663`, `at_least_lit`:
`k > len(self.outputs)` returns `false_lit`, treating it as impossible.

Engines: both, since the formula is wrong before a solver sees it. Run on each case, `solve()`,
`solve_adaptive(engine="native")` and `solve_adaptive(engine="python")` all give the same wrong answer:
SAT with both inputs true under `<= 1`, and UNSAT under `>= 2`.

The fix is a design choice, though a small one: a truncated counter cannot express these bounds, so
raising `ValueError` is the honest answer. Keep `None` for `k >= len(inputs)` and `false_lit` for
`k > len(inputs)`, which are the true vacuous and impossible cases.

## Proposed failing test

```python
import itertools
import unittest
from dratify.cnf import CNF
from dratify.lits import mk_lit, neg
from cdclkit.encodings import Encoder, Totalizer
from cdclkit.solver import Solver

class TestTruncatedTotalizerPastTheCut(unittest.TestCase):
    def check(self, method, k, spec):
        """Either it refuses the bound, or the bound is what it says."""
        f = CNF()
        xs = [mk_lit(f.new_var()) for _ in range(2)]
        t = Totalizer(Encoder(f), xs, max_count=1)
        try:
            getattr(t, method)(k)
        except ValueError:
            return
        for bits in itertools.product((0, 1), repeat=2):
            s = Solver(f.nvars)
            ok = s.add_cnf(f)
            got = bool(ok and s.solve([x if b else neg(x) for x, b in zip(xs, bits)]))
            self.assertEqual(got, spec(sum(bits)), f"{method}({k}) bits={bits}")

    def test_at_most_past_the_cut_is_not_vacuous(self):
        self.check("assert_at_most", 1, lambda c: c <= 1)

    def test_at_least_past_the_cut_is_not_impossible(self):
        self.check("assert_at_least", 2, lambda c: c >= 2)

if __name__ == "__main__":
    unittest.main()
```
