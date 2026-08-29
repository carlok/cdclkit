# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Reference solvers: slow, obviously correct, and written independently.

Every nontrivial claim cdclkit makes is cross-checked against something in this
file.  The rule I hold myself to: a reference implementation must be simple
enough that its correctness is apparent by reading, even at the cost of being
exponentially slower.  No watched literals, no learning, no clever data
structures.  If the CDCL solver and the reference disagree, the reference is
right until proven otherwise.

Three of them, at increasing strength:

``exhaustive``
    Enumerate all 2^n assignments.  Correct by definition of satisfiability.
``dpll``
    Classic Davis-Putnam-Logemann-Loveland: unit propagation, pure literal
    elimination, splitting.  Independent of the CDCL code path.
``resolution_refute``
    Bounded ordered resolution -- the proof system CDCL simulates.  Used to
    show, on small instances, that a formula the solver calls UNSAT really has
    a resolution refutation, and to generate ground truth for proof tests.
"""

from __future__ import annotations

import itertools
from typing import Sequence

from dratify.cnf import CNF

__all__ = [
    "exhaustive_solve",
    "count_models",
    "all_models",
    "dpll",
    "resolution_refute",
    "implied_literals",
]


def exhaustive_solve(f: CNF) -> list[bool] | None:
    """Return the lexicographically first model, or None if there is none."""
    for bits in itertools.product((False, True), repeat=f.nvars):
        if f.is_satisfied_by(bits):
            return list(bits)
    return None


def all_models(f: CNF, projection: Sequence[int] | None = None) -> list[tuple[bool, ...]]:
    """Every model, optionally projected onto a subset of variables."""
    seen = set()
    out = []
    for bits in itertools.product((False, True), repeat=f.nvars):
        if not f.is_satisfied_by(bits):
            continue
        key = tuple(bits) if projection is None else tuple(bits[v] for v in projection)
        if key not in seen:
            seen.add(key)
            out.append(key)
    return out


def count_models(f: CNF, projection: Sequence[int] | None = None) -> int:
    return len(all_models(f, projection))


def implied_literals(f: CNF) -> set[int]:
    """Internal literals true in *every* model (the formula's backbone).

    Exponential.  Used to test that the solver's root-level propagation and
    simplification never assert something that is not actually implied.
    """
    models = [m for m in itertools.product((False, True), repeat=f.nvars) if f.is_satisfied_by(m)]
    if not models:
        return set()
    out = set()
    for v in range(f.nvars):
        vals = {m[v] for m in models}
        if len(vals) == 1:
            out.add((v << 1) | (0 if vals.pop() else 1))
    return out


# --------------------------------------------------------------------------
# DPLL
# --------------------------------------------------------------------------


def dpll(f: CNF, max_steps: int = 2_000_000) -> list[bool] | None:
    """Textbook DPLL.  Returns a model or None; raises on step exhaustion."""
    clauses = [list(c) for c in f.clauses]
    assign: dict[int, bool] = {}
    steps = [0]

    def simplify(cs: list[list[int]], lit: int) -> list[list[int]] | None:
        """Apply ``lit = true``; None signals the empty clause."""
        out = []
        for c in cs:
            if lit in c:
                continue
            if (lit ^ 1) in c:
                rest = [l for l in c if l != (lit ^ 1)]
                if not rest:
                    return None
                out.append(rest)
            else:
                out.append(c)
        return out

    def rec(cs: list[list[int]], a: dict[int, bool]) -> dict[int, bool] | None:
        steps[0] += 1
        if steps[0] > max_steps:
            raise RuntimeError("DPLL step budget exhausted")
        # unit propagation
        while True:
            unit = next((c[0] for c in cs if len(c) == 1), None)
            if unit is None:
                break
            a = dict(a)
            a[unit >> 1] = not (unit & 1)
            cs2 = simplify(cs, unit)
            if cs2 is None:
                return None
            cs = cs2
        if not cs:
            return a
        # pure literal elimination
        present = {l for c in cs for l in c}
        pure = next((l for l in present if (l ^ 1) not in present), None)
        if pure is not None:
            a = dict(a)
            a[pure >> 1] = not (pure & 1)
            cs2 = simplify(cs, pure)
            return rec(cs2, a) if cs2 is not None else None
        # split on the first literal of the first clause
        lit = cs[0][0]
        for choice in (lit, lit ^ 1):
            a2 = dict(a)
            a2[choice >> 1] = not (choice & 1)
            cs2 = simplify(cs, choice)
            if cs2 is None:
                continue
            r = rec(cs2, a2)
            if r is not None:
                return r
        return None

    res = rec(clauses, assign)
    if res is None:
        return None
    return [res.get(v, False) for v in range(f.nvars)]


# --------------------------------------------------------------------------
# resolution
# --------------------------------------------------------------------------


def resolution_refute(f: CNF, max_clauses: int = 200_000) -> list[tuple] | None:
    """Saturating unrestricted resolution.  Returns a derivation of the empty
    clause as a list of ``(resolvent, parent_a, parent_b, pivot_var)``, or None
    if the formula is satisfiable (saturation closed without deriving it).

    This is the ground truth for "UNSAT means refutable": CDCL learning is
    exactly a restricted form of this rule, so anything the solver refutes must
    be refutable here.  Exponential in the worst case, hence the cap.
    """
    frontier = {frozenset(c) for c in f.clauses}
    if frozenset() in frontier:
        return []
    known = set(frontier)
    derivation: list[tuple] = []
    parents: dict[frozenset, tuple] = {}
    while True:
        new = set()
        items = list(known)
        for i, a in enumerate(items):
            for b in items[i + 1 :]:
                for l in a:
                    if (l ^ 1) not in b:
                        continue
                    r = (a - {l}) | (b - {l ^ 1})
                    if any((x ^ 1) in r for x in r):
                        continue  # tautology
                    r = frozenset(r)
                    if r in known or r in new:
                        continue
                    new.add(r)
                    parents[r] = (a, b, l >> 1)
                    if not r:
                        # unwind the derivation
                        order: list[tuple] = []
                        stack = [r]
                        seen = set()
                        while stack:
                            cur = stack.pop()
                            if cur in seen or cur not in parents:
                                continue
                            seen.add(cur)
                            pa, pb, piv = parents[cur]
                            order.append((tuple(sorted(cur)), tuple(sorted(pa)), tuple(sorted(pb)), piv))
                            stack.extend((pa, pb))
                        order.reverse()
                        return order
        if not new:
            return None
        if len(known) + len(new) > max_clauses:
            raise RuntimeError("resolution saturation exceeded the clause cap")
        known |= new
