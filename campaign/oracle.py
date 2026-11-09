# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A reference for DRAT reasoning on tiny formulas, by definition and brute force.

This module shares no code with dratify or cdclkit and imports neither. It is
the same file in both repositories' ``campaign/`` directories.

Conventions:

* A literal is a non-zero DIMACS integer, a clause is an iterable of literals,
  and a formula is a list of clauses read as a **multiset**: a clause present
  twice stands for two copies, which matters for deletion and for nothing else.
* A clause means the set of its literals. ``[1, 1]`` is the clause (1), and
  ``[1, -1]`` is a tautology.
* A formula may mention at most ``MAX_VARS`` distinct variables (counting the
  clause under test). Above that the exhaustive functions raise ``ValueError``
  rather than quietly take an hour. ``rup`` and ``rat`` do no search and have
  no such limit.

Definitions, from Wetzler, Heule and Hunt, "DRAT-trim" (SAT 2014):

* ``C`` is **RUP** (equivalently AT, asymmetric tautology) with respect to
  ``F`` if unit propagation on ``F`` with every literal of ``C`` assigned false
  reaches a conflict.
* ``C`` is **RAT on l**, for a literal ``l`` in ``C``, if for every ``D`` in
  ``F`` containing ``-l``, the resolvent ``C ∪ (D \\ {-l})`` is RUP with
  respect to ``F``. With no such ``D`` this holds vacuously.

And from Rebola-Pardo and Biere, "Two flavors of DRAT" (2018), the two readings
of a deletion, which :func:`replay` offers as flavours alongside the rule
dratify documents:

* ``"specified"``: every deletion happens.
* ``"operational"``: as drat-trim runs in practice, a deletion is ignored when
  the clause is pseudo-unit, meaning unit under the top-level assignment, and
  every deletion is ignored once top-level propagation conflicts, because the
  proof is over. See :func:`is_pseudo_unit`, which is this module's
  approximation of drat-trim's reason-clause test: it also answers true for a
  clause that merely looks like a reason, so ``applied`` and the final multiset
  can differ from drat-trim's.
* ``"length-one"``: a deletion is ignored only when the clause, as a set, has
  at most one literal.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence

MAX_VARS = 16

FLAVOURS = ("specified", "operational", "length-one")


def _lits(clause: Iterable[int]) -> frozenset[int]:
    lits = frozenset(clause)
    for lit in lits:
        if not isinstance(lit, int) or isinstance(lit, bool) or lit == 0:
            raise ValueError(f"{lit!r} is not a DIMACS literal")
    return lits


def _masks(clauses: Sequence[frozenset[int]]) -> tuple[list[int], int]:
    """The truth table of each clause over the variables mentioned, as an int.

    Bit ``m`` of a table is the clause's value under assignment number ``m``,
    so a formula's table is the AND of its clauses' tables. All ``2**n``
    assignments are evaluated: this is exhaustive search, done a word at a time.
    """
    variables = sorted({abs(l) for c in clauses for l in c})
    if len(variables) > MAX_VARS:
        raise ValueError(
            f"{len(variables)} variables; the exhaustive oracle stops at {MAX_VARS}")
    n = len(variables)
    size = 1 << n
    full = (1 << size) - 1
    positive = {}
    for i, v in enumerate(variables):
        # the assignments numbered m with bit i of m set: blocks of 2**i
        # zeros then 2**i ones, repeated
        table = ((1 << (1 << i)) - 1) << (1 << i)
        width = 1 << (i + 1)
        while width < size:
            table |= table << width
            width <<= 1
        positive[v] = table
    tables = []
    for c in clauses:
        t = 0
        for l in c:
            t |= positive[l] if l > 0 else full & ~positive[-l]
        tables.append(t)
    return tables, full


def satisfiable(formula: Iterable[Iterable[int]]) -> bool:
    """True when some assignment satisfies every clause. The empty formula does."""
    clauses = [_lits(c) for c in formula]
    tables, full = _masks(clauses)
    result = full
    for t in tables:
        result &= t
    return result != 0


def implies(formula: Iterable[Iterable[int]], clause: Iterable[int]) -> bool:
    """F implies C: F together with the negation of C is unsatisfiable."""
    negation = [[-l] for l in _lits(clause)]
    return not satisfiable([*formula, *negation])


def preserves_sat(formula: Iterable[Iterable[int]], clause: Iterable[int]) -> bool:
    """If F is satisfiable, so is F together with C."""
    clauses = [_lits(c) for c in formula]
    # both are asked for, so a variable over the limit raises whatever F's answer
    with_clause = satisfiable([*clauses, _lits(clause)])
    return with_clause or not satisfiable(clauses)


def propagate(
    formula: Iterable[Iterable[int]], assumptions: Iterable[int] = ()
) -> tuple[bool, frozenset[int]]:
    """Unit propagation to fixpoint on the clause multiset.

    Returns ``(conflict, literals assigned true)``. Contradictory assumptions
    are a conflict. Every clause is rescanned until nothing changes: no watches
    and no cleverness, so there is little to get wrong.
    """
    assigned = set(_lits(assumptions))
    if any(-l in assigned for l in assigned):
        return True, frozenset(assigned)
    clauses = [_lits(c) for c in formula]
    changed = True
    while changed:
        changed = False
        for lits in clauses:
            if lits & assigned:
                continue
            free = [l for l in lits if -l not in assigned]
            if not free:
                return True, frozenset(assigned)
            if len(free) == 1:
                assigned.add(free[0])
                changed = True
    return False, frozenset(assigned)


def rup(formula: Iterable[Iterable[int]], clause: Iterable[int]) -> bool:
    """C is RUP with respect to F. A tautological C is, trivially."""
    conflict, _ = propagate(formula, [-l for l in _lits(clause)])
    return conflict


def rat(formula: Iterable[Iterable[int]], clause: Iterable[int], pivot: int) -> bool:
    """C is RAT on ``pivot`` with respect to F, by the definition above."""
    lits = _lits(clause)
    if pivot not in lits:
        raise ValueError(f"the pivot {pivot} is not in the clause {sorted(lits)}")
    clauses = [_lits(c) for c in formula]
    for d in clauses:
        if -pivot in d:
            if not rup(clauses, lits | (d - {-pivot})):
                return False
    return True


def is_pseudo_unit(formula: Iterable[Iterable[int]], clause: Iterable[int]) -> bool:
    """C has one true literal and the rest false, under F's top-level assignment.

    If top-level propagation conflicts, this answers from the assignment it had
    reached when it stopped.
    """
    _, assigned = propagate(formula)
    lits = _lits(clause)
    true = lits & assigned
    false = {l for l in lits if -l in assigned}
    return len(true) == 1 and len(true) + len(false) == len(lits)


def remove_one(
    formula: Sequence[Iterable[int]], clause: Iterable[int]
) -> tuple[list[list[int]], bool]:
    """Delete one copy of C, matching as sets. Returns (new formula, was it there)."""
    lits = _lits(clause)
    out = [list(c) for c in formula]
    for i, c in enumerate(out):
        if _lits(c) == lits:
            del out[i]
            return out, True
    return out, False


@dataclass(frozen=True)
class Step:
    """What the definitions say about one proof step, before it is applied."""

    index: int                       # 1-based, as dratify numbers failed_step
    kind: str                        # "a" or "d"
    clause: tuple[int, ...]          # as written; the first literal is the pivot
    rup: bool | None = None          # additions only
    rat_on_first: bool | None = None # additions with a first literal only
    implied: bool | None = None      # additions only
    preserves_sat: bool | None = None  # additions only
    present: bool | None = None      # deletions only
    applied: bool | None = None      # deletions only

    @property
    def acceptable(self) -> bool:
        """An addition that is RUP, or RAT on its first literal, at this point.

        False does not mean every checker must reject: a backward checker such
        as drat-trim never examines a lemma the refutation does not use.
        ``implied`` and ``preserves_sat`` are relative to the current multiset,
        not the input formula. Once that multiset is refuted, every addition
        passes. A tautological ``D`` is a candidate under the literal
        definition, so ``rat`` can say False where ``preserves_sat`` says True.
        """
        return self.kind == "d" or bool(self.rup or self.rat_on_first)


def replay(
    formula: Sequence[Iterable[int]],
    steps: Iterable[tuple[str, Sequence[int]]],
    flavour: str = "specified",
    stop_at_unacceptable: bool = True,
) -> tuple[list[Step], list[list[int]]]:
    """Walk a proof over a multiset of clauses under one reading of deletion.

    ``steps`` are ``("a" | "d", DIMACS literals)``. Every addition is judged
    against the clauses present at that moment and then added, unless it is
    unacceptable and ``stop_at_unacceptable`` is set, which ends the walk there
    as a checker would. Returns the judgements and the final multiset.
    """
    if flavour not in FLAVOURS:
        raise ValueError(f"flavour must be one of {FLAVOURS}, not {flavour!r}")
    current = [list(c) for c in formula]
    out: list[Step] = []
    for index, (kind, lits) in enumerate(steps, 1):
        clause = tuple(lits)
        if kind == "d":
            _, present = remove_one(current, clause)
            if flavour == "specified":
                ignored = False
            elif flavour == "operational":
                ignored = propagate(current)[0] or is_pseudo_unit(current, clause)
            else:
                ignored = len(_lits(clause)) <= 1
            applied = present and not ignored
            if applied:
                current, _ = remove_one(current, clause)
            out.append(Step(index, kind, clause, present=present, applied=applied))
            continue
        if kind != "a":
            raise ValueError(f"step {index}: kind must be 'a' or 'd', not {kind!r}")
        step = Step(
            index,
            kind,
            clause,
            rup=rup(current, clause),
            rat_on_first=rat(current, clause, clause[0]) if clause else None,
            implied=implies(current, clause),
            preserves_sat=preserves_sat(current, clause),
        )
        out.append(step)
        if stop_at_unacceptable and not step.acceptable:
            break
        current.append(list(clause))
    return out, current
