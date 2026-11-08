# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A small DPLL for formulas past the oracle's 16 variables, such as encodings.

An encoding's auxiliary variables can run to hundreds, so the oracle's truth
tables cannot reach it. Enumerating the original variables and deciding each
residual formula here gives the projected solution set exactly. It shares no
code with dratify or cdclkit, and test_dpll.py checks it against the oracle.

Literals are DIMACS integers. There is no learning and no heuristic beyond
branching on the first free literal of the first open clause.
"""

from __future__ import annotations

import itertools
from typing import Iterable, Sequence


def _simplify(clauses, lit):
    """Set ``lit`` true: drop satisfied clauses and remove its negation."""
    out = []
    for c in clauses:
        if lit in c:
            continue
        out.append(c - {-lit} if -lit in c else c)
    return out


def model(formula: Iterable[Iterable[int]]) -> dict[int, bool] | None:
    """A satisfying assignment of the variables it had to fix, or None."""
    clauses = [frozenset(c) for c in formula]
    if any(0 in c for c in clauses):
        raise ValueError("0 is not a DIMACS literal")
    clauses = [c for c in clauses if not any(-l in c for l in c)]
    stack = [(clauses, ())]
    while stack:
        current, chosen = stack.pop()
        chosen = list(chosen)
        while True:
            unit = next((c for c in current if len(c) <= 1), None)
            if unit is None:
                break
            if not unit:
                current = None
                break
            lit = next(iter(unit))
            chosen.append(lit)
            current = _simplify(current, lit)
        if current is None:
            continue
        if not current:
            return {abs(l): l > 0 for l in chosen}
        lit = next(iter(current[0]))
        stack.append((_simplify(current, -lit), (*chosen, -lit)))
        stack.append((_simplify(current, lit), (*chosen, lit)))
    return None


def satisfiable(formula: Iterable[Iterable[int]]) -> bool:
    return model(formula) is not None


def projected_models(
    formula: Iterable[Iterable[int]], variables: Sequence[int]
) -> set[tuple[bool, ...]]:
    """Every assignment of ``variables`` that extends to a model of the formula.

    Each of the 2**len(variables) assignments is tried, so this is exact, and
    it is meant for a dozen or so variables.
    """
    clauses = [frozenset(c) for c in formula]
    out = set()
    for values in itertools.product((False, True), repeat=len(variables)):
        current = clauses
        for v, value in zip(variables, values):
            current = _simplify(current, v if value else -v)
        if satisfiable(current):
            out.add(values)
    return out
