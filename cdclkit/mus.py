# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Minimal unsatisfiable subsets: *why* is this formula unsatisfiable?

An UNSAT answer says a formula has no model. A **MUS** says which clauses are
to blame: an unsatisfiable subset of the clauses such that removing any one of
them makes it satisfiable. For a specification with 10,000 constraints and a
contradiction somewhere in it, that difference is the difference between "your
model is broken" and "these six lines conflict".

Formally, `M ⊆ F` is a MUS when `M` is unsatisfiable and every proper subset of
`M` is satisfiable. Minimal, not minimum: a formula can have many MUSes of
different sizes, and finding the smallest is a harder (Σ₂ᵖ-complete) problem.
Every algorithm here returns *a* MUS.

The machinery is selector variables. Clause `cᵢ` becomes `¬sᵢ ∨ cᵢ`, so
assuming `sᵢ` switches the clause on and assuming nothing leaves it inert. Then
"is this subset unsatisfiable?" is one incremental solve under assumptions, the
solver keeps everything it learned across all of them, and the unsatisfiable
core the solver already computes (`Solver.conflict`) gives a free head start:
it is an unsatisfiable subset, just not necessarily a minimal one.

Two algorithms:

**Deletion-based.** Try each candidate clause in turn; if the rest are still
unsatisfiable, drop it permanently. Exactly `|M|` solver calls after the
initial core, each one UNSAT-or-SAT, and the result is minimal by construction.
Simple and hard to get wrong.

**QuickXplain** (Junker 2004). Divide and conquer: split the candidate set,
recurse on halves, and only descend into a half that is actually needed. When
the MUS is small relative to the formula it takes O(|M| log(|F|/|M|)) calls
instead of O(|F|), which is a large win on the realistic case where a handful
of constraints out of thousands are guilty.
"""

from __future__ import annotations

from typing import Sequence

from dratify.cnf import CNF
from dratify.lits import mk_lit, neg
from .solver import Solver

__all__ = ["MUSExtractor", "mus", "shrink_core"]


class MUSExtractor:
    """Wraps a formula with selector variables for incremental subset testing."""

    def __init__(self, formula: CNF) -> None:
        self.formula = formula
        self.solver = Solver(formula.nvars)
        self.selectors: list[int] = []
        for clause in formula.clauses:
            s = mk_lit(self.solver.new_var())
            self.selectors.append(s)
            # (~s or clause): assuming s switches the clause on
            self.solver.add_clause([neg(s)] + list(clause))
        self.calls = 0

    def is_unsat(self, subset: Sequence[int]) -> bool:
        """True when the clauses indexed by ``subset`` are unsatisfiable."""
        self.calls += 1
        return not self.solver.solve([self.selectors[i] for i in subset])

    def _all(self, subset: Sequence[int] | None) -> list[int]:
        cands = list(range(len(self.selectors))) if subset is None else list(subset)
        return cands if self.is_unsat(cands) else []

    def core(self, subset: Sequence[int] | None = None) -> list[int]:
        """An unsatisfiable core: the subset the solver actually used.

        Not minimal, but usually far smaller than the input, and it costs
        nothing extra -- the solver computes it during the failed solve.
        """
        candidates = list(range(len(self.selectors))) if subset is None else list(subset)
        if not self.is_unsat(candidates):
            return []
        by_sel = {self.selectors[i]: i for i in candidates}
        used = [by_sel[l] for l in self.solver.conflict if l in by_sel]
        return sorted(used) if used else candidates

    # -- algorithms ---------------------------------------------------------

    def deletion(self, subset: Sequence[int] | None = None, use_core: bool = True) -> list[int]:
        """Deletion-based MUS extraction.

        ``use_core`` first shrinks the candidate set to the solver's own
        unsatisfiable core, which is nearly always worth it: one solve replaces
        many.  Set it to False to measure the algorithms on equal footing.
        """
        candidates = self.core(subset) if use_core else self._all(subset)
        if not candidates:
            return []
        keep: list[int] = []
        remaining = list(candidates)
        while remaining:
            c = remaining.pop()
            if self.is_unsat(keep + remaining):
                continue  # c is not needed
            keep.append(c)
        return sorted(keep)

    def quickxplain(self, subset: Sequence[int] | None = None,
                    use_core: bool = True) -> list[int]:
        """Junker's QuickXplain: divide and conquer over the candidate set."""
        candidates = self.core(subset) if use_core else self._all(subset)
        if not candidates:
            return []
        if self.is_unsat([]):
            return []
        return sorted(self._qx([], [], candidates))

    def _qx(self, background: list[int], delta: list[int], candidates: list[int]) -> list[int]:
        if delta and self.is_unsat(background):
            return []
        if len(candidates) == 1:
            return list(candidates)
        mid = len(candidates) // 2
        first, second = candidates[:mid], candidates[mid:]
        d1 = self._qx(background + first, first, second)
        d2 = self._qx(background + d1, d1, first)
        return d1 + d2

    # -- verification -------------------------------------------------------

    def verify(self, subset: Sequence[int]) -> tuple[bool, str]:
        """Check the defining property: unsatisfiable, and minimally so.

        Costs ``|subset| + 1`` solver calls.  Cheap enough to run in anger, and
        the test suite always does -- a "minimal" set nobody checked is just a
        set.
        """
        if not self.is_unsat(subset):
            return False, "the subset is satisfiable"
        for i in subset:
            rest = [j for j in subset if j != i]
            if self.is_unsat(rest):
                return False, f"clause {i} is redundant: the rest is still unsatisfiable"
        return True, f"verified: unsatisfiable, and all {len(subset)} clauses are necessary"


def mus(formula: CNF, method: str = "deletion") -> list[int]:
    """Return the indices of a minimal unsatisfiable subset of ``formula``.

    Returns an empty list when the formula is satisfiable.
    """
    ex = MUSExtractor(formula)
    if method == "deletion":
        return ex.deletion()
    if method == "quickxplain":
        return ex.quickxplain()
    raise ValueError(f"unknown MUS method {method!r}")


def shrink_core(formula: CNF) -> list[int]:
    """The cheap option: the solver's own unsatisfiable core, unminimised."""
    return MUSExtractor(formula).core()
