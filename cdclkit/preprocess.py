# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""SatELite-style preprocessing: subsumption, strengthening, variable elimination.

Preprocessing is where the biggest wins on structured industrial instances come
from, and it is also where correctness gets slippery, because the transformed
formula is **not logically equivalent** to the original -- only
*equisatisfiable*.  Bounded variable elimination in particular throws away
clauses whose information is not recoverable from the reduced formula alone.
So every elimination is recorded on a stack, and :meth:`Preprocessor.reconstruct`
replays that stack backwards to turn a model of the reduced formula into a
model of the original.  Getting reconstruction wrong is the classic
preprocessing bug: the solver reports SAT and hands back an assignment that
does not satisfy the user's input.

The techniques, with their justifications:

**Unit propagation.**  Trivially equivalence preserving.

**Subsumption.**  ``C`` subsumes ``D`` when ``C`` is a subset of ``D``; then
``D`` is implied by ``C`` and can be dropped.  Equivalence preserving.
Implemented with 64-bit signature filtering: a cheap superset test on the
signature rejects the vast majority of candidate pairs before any set
operation happens.

**Self-subsuming resolution** (strengthening).  If ``C \\ {l}`` is a subset of
``D`` and ``~l`` is in ``D``, then resolving ``C`` and ``D`` on ``l`` gives a
clause that subsumes ``D``; so ``~l`` may be deleted from ``D`` in place.
Equivalence preserving, and it is the engine that makes subsumption keep
firing: every strengthened clause is a new subsumption candidate.

**Bounded variable elimination** (Davis-Putnam, bounded).  Replace all clauses
containing ``v`` by all their non-tautological resolvents on ``v``.  The
resolvents are logically implied, so adding them is sound; removing the
originals is what breaks equivalence and requires reconstruction.  Elimination
is only performed when it does not increase the clause count (the "bounded"
part) and when resolvent lengths stay within a cap, otherwise the formula
explodes -- unbounded Davis-Putnam is exponential, which is exactly why DPLL
replaced it in 1962.

**Pure literal elimination.**  If ``v`` occurs with only one polarity, fix it.
A special case of BVE (the resolvent set is empty), listed separately because
it is worth a dedicated cheap pass.

**Blocked clause elimination.**  ``C`` is blocked on ``l in C`` when every
resolvent of ``C`` on ``l`` is a tautology.  Removing a blocked clause
preserves satisfiability (and, on the reconstruction side, is handled exactly
like an elimination).  This is the operation whose *inverse* -- blocked clause
addition -- needs the RAT rule rather than RUP, and it is why DRAT has an "A"
in it.

Proof logging
-------------
Every clause added is emitted before it is used, every clause removed is
emitted as a deletion afterwards, in that order.  BVE resolvents are RUP (unit
propagation on the two parents derives them), so a plain DRAT checker verifies
the entire preprocessing phase with no special support.
"""

from __future__ import annotations

from typing import Iterable, Sequence

from dratify.cnf import CNF
from dratify.lits import neg

__all__ = ["Preprocessor", "PreprocessStats", "preprocess"]


def _sig(lits: Iterable[int]) -> int:
    """A 64-bit occurrence signature used to reject subsumption candidates."""
    s = 0
    for l in lits:
        s |= 1 << ((l >> 1) & 63)
    return s


class PreprocessStats:
    __slots__ = (
        "rounds",
        "units",
        "subsumed",
        "strengthened",
        "eliminated_vars",
        "resolvents",
        "removed_clauses",
        "blocked",
        "pure",
        "tautologies",
        "tried_vars",
    )

    def __init__(self) -> None:
        for k in PreprocessStats.__slots__:
            setattr(self, k, 0)

    def as_dict(self) -> dict:
        return {k: getattr(self, k) for k in PreprocessStats.__slots__}

    def report(self) -> str:
        d = self.as_dict()
        return "\n".join(
            [
                f"c preprocess rounds     : {d['rounds']}",
                f"c units propagated      : {d['units']}",
                f"c clauses subsumed      : {d['subsumed']}",
                f"c literals strengthened : {d['strengthened']}",
                f"c variables eliminated  : {d['eliminated_vars']} "
                f"(of {d['tried_vars']} tried, {d['resolvents']} resolvents added)",
                f"c pure literals         : {d['pure']}",
                f"c blocked clauses       : {d['blocked']}",
                f"c clauses removed total : {d['removed_clauses']}",
            ]
        )


class Preprocessor:
    """Simplifies a :class:`CNF` in place-ish, returning a new reduced formula.

    Usage::

        pre = Preprocessor(formula, proof=writer)
        reduced = pre.run()
        ... solve `reduced`, get `model` ...
        full_model = pre.reconstruct(model)

    ``reconstruct`` is mandatory: the reduced formula's models are, in general,
    *partial* with respect to the original variables.
    """

    def __init__(
        self,
        formula: CNF,
        proof=None,
        max_resolvent_len: int = 20,
        elim_growth: int = 0,
        do_bve: bool = True,
        do_bce: bool = True,
        subsumption_limit: int = 2_000_000,
    ) -> None:
        self.orig_nvars = formula.nvars
        self.proof = proof
        self.max_resolvent_len = max_resolvent_len
        self.elim_growth = elim_growth
        self.do_bve = do_bve
        self.do_bce = do_bce
        self.subsumption_limit = subsumption_limit
        self.stats = PreprocessStats()

        # clause store: parallel arrays, index = clause id
        self.cls: list[tuple[int, ...] | None] = [tuple(c) for c in formula.clauses]
        self.sig: list[int] = [_sig(c) for c in self.cls]
        self.occ: list[set[int]] = [set() for _ in range(2 * formula.nvars)]
        for i, c in enumerate(self.cls):
            for l in c:
                self.occ[l].add(i)

        self.value: dict[int, bool] = {}  # var -> fixed value
        self.eliminated: list[tuple[int, list[tuple[int, ...]]]] = []
        self.frozen: set[int] = set()  # variables that must survive
        self.unsat = False
        self._touched: set[int] = set(range(2 * formula.nvars))

    # -- freezing -----------------------------------------------------------

    def freeze(self, variables: Iterable[int]) -> None:
        """Protect variables from elimination (needed for incremental use or
        when the caller wants to read their value out of the model)."""
        self.frozen.update(variables)

    # -- low-level clause ops ----------------------------------------------

    def _emit_add(self, lits: Sequence[int]) -> None:
        if self.proof is not None:
            self.proof.add(lits)

    def _emit_del(self, lits: Sequence[int]) -> None:
        if self.proof is not None:
            self.proof.delete(lits)

    def _add_clause(self, lits: Sequence[int], log: bool = True) -> int:
        c = tuple(lits)
        if log:
            self._emit_add(c)
        i = len(self.cls)
        self.cls.append(c)
        self.sig.append(_sig(c))
        for l in c:
            self.occ[l].add(i)
            self._touched.add(l)
        return i

    def _remove_clause(self, i: int, log: bool = True) -> None:
        c = self.cls[i]
        if c is None:
            return
        for l in c:
            self.occ[l].discard(i)
            self._touched.add(l)
        self.cls[i] = None
        if log:
            self._emit_del(c)
        self.stats.removed_clauses += 1

    def _replace_clause(self, i: int, lits: Sequence[int]) -> None:
        """Strengthen clause ``i`` to ``lits`` (a proper subset)."""
        old = self.cls[i]
        self._emit_add(lits)
        for l in old:
            self.occ[l].discard(i)
            self._touched.add(l)
        self.cls[i] = tuple(lits)
        self.sig[i] = _sig(lits)
        for l in lits:
            self.occ[l].add(i)
            self._touched.add(l)
        self._emit_del(old)

    def alive(self) -> Iterable[int]:
        return (i for i, c in enumerate(self.cls) if c is not None)

    # -- unit propagation ---------------------------------------------------

    def propagate(self) -> bool:
        """Propagate unit clauses to fixpoint.  False means UNSAT."""
        queue = [self.cls[i][0] for i in self.alive() if len(self.cls[i]) == 1]
        while queue:
            l = queue.pop()
            v, positive = l >> 1, not (l & 1)
            if v in self.value:
                if self.value[v] != positive:
                    self.unsat = True
                    self._emit_add(())
                    return False
                continue
            self.value[v] = positive
            self.stats.units += 1
            # clauses containing l are satisfied
            for i in list(self.occ[l]):
                self._remove_clause(i)
            # ~l is removed from the clauses that contain it
            for i in list(self.occ[l ^ 1]):
                c = self.cls[i]
                if c is None:
                    continue
                rest = tuple(x for x in c if x != (l ^ 1))
                if not rest:
                    self.unsat = True
                    self._emit_add(())
                    return False
                self._replace_clause(i, rest)
                if len(rest) == 1:
                    queue.append(rest[0])
        return True

    # -- subsumption --------------------------------------------------------

    def subsume(self) -> None:
        """Remove subsumed clauses and strengthen by self-subsuming resolution."""
        work = sorted(self.alive(), key=lambda i: len(self.cls[i]))
        budget = self.subsumption_limit
        for i in work:
            c = self.cls[i]
            if c is None:
                continue
            # pick the literal with the smallest occurrence list to scan
            best = min(c, key=lambda l: len(self.occ[l]) + len(self.occ[l ^ 1]))
            si = self.sig[i]
            cset = set(c)
            for pol in (best, best ^ 1):
                for j in list(self.occ[pol]):
                    if j == i:
                        continue
                    d = self.cls[j]
                    if d is None or len(d) < len(c):
                        continue
                    budget -= 1
                    if budget < 0:
                        return
                    if si & ~self.sig[j]:
                        continue
                    dset = set(d)
                    if cset <= dset:
                        self._remove_clause(j)
                        self.stats.subsumed += 1
                        continue
                    # self-subsuming resolution: C\{l} subset of D and ~l in D
                    diff = cset - dset
                    if len(diff) == 1:
                        l = next(iter(diff))
                        if (l ^ 1) in dset:
                            new = tuple(x for x in d if x != (l ^ 1))
                            if not new:
                                self.unsat = True
                                self._emit_add(())
                                return
                            self._replace_clause(j, new)
                            self.stats.strengthened += 1

    # -- blocked clause elimination ----------------------------------------

    def _resolvent(self, c: Sequence[int], d: Sequence[int], l: int) -> list[int] | None:
        """Resolve on ``l`` (in ``c``); None when the resolvent is a tautology."""
        out = [x for x in c if x != l]
        seen = set(out)
        for x in d:
            if x == (l ^ 1):
                continue
            if (x ^ 1) in seen:
                return None
            if x not in seen:
                seen.add(x)
                out.append(x)
        return out

    def block_eliminate(self) -> None:
        """Remove clauses that are blocked on one of their literals."""
        for i in list(self.alive()):
            c = self.cls[i]
            if c is None or len(c) > self.max_resolvent_len:
                continue
            for l in c:
                if (l >> 1) in self.frozen:
                    continue
                blocked = True
                for j in self.occ[l ^ 1]:
                    d = self.cls[j]
                    if d is None:
                        continue
                    if self._resolvent(c, d, l) is not None:
                        blocked = False
                        break
                if blocked and self.occ[l ^ 1]:
                    self.eliminated.append((l >> 1, [c]))
                    self._remove_clause(i)
                    self.stats.blocked += 1
                    break

    # -- variable elimination ----------------------------------------------

    def _pure_literals(self) -> None:
        for v in range(self.orig_nvars):
            if v in self.value or v in self.frozen:
                continue
            pos, negs = self.occ[v << 1], self.occ[(v << 1) | 1]
            if pos and not negs:
                self._eliminate_pure(v, True)
            elif negs and not pos:
                self._eliminate_pure(v, False)

    def _eliminate_pure(self, v: int, positive: bool) -> None:
        lit = (v << 1) | (0 if positive else 1)
        clauses = [self.cls[i] for i in list(self.occ[lit]) if self.cls[i] is not None]
        if not clauses:
            return
        self.eliminated.append((v, clauses))
        for i in list(self.occ[lit]):
            self._remove_clause(i)
        self.stats.pure += 1
        self.stats.eliminated_vars += 1

    def eliminate_vars(self) -> bool:
        """Bounded variable elimination.  False means UNSAT was derived."""
        order = sorted(
            (v for v in range(self.orig_nvars) if v not in self.value and v not in self.frozen),
            key=lambda v: len(self.occ[v << 1]) * len(self.occ[(v << 1) | 1]),
        )
        for v in order:
            if v in self.value:
                continue
            pos = [self.cls[i] for i in self.occ[v << 1] if self.cls[i] is not None]
            negs = [self.cls[i] for i in self.occ[(v << 1) | 1] if self.cls[i] is not None]
            self.stats.tried_vars += 1
            if not pos and not negs:
                continue
            if len(pos) * len(negs) > 400:
                continue  # cheap guard against quadratic blowup
            resolvents = []
            too_big = False
            for c in pos:
                for d in negs:
                    r = self._resolvent(c, d, v << 1)
                    if r is None:
                        self.stats.tautologies += 1
                        continue
                    if not r:
                        # empty resolvent: the formula is unsatisfiable
                        self._emit_add(())
                        self.unsat = True
                        return False
                    if len(r) > self.max_resolvent_len:
                        too_big = True
                        break
                    resolvents.append(r)
                if too_big:
                    break
            if too_big or len(resolvents) > len(pos) + len(negs) + self.elim_growth:
                continue
            # commit: add resolvents first (they are RUP given the parents),
            # then delete the parents
            for r in resolvents:
                self._add_clause(r)
                self.stats.resolvents += 1
            self.eliminated.append((v, pos + negs))
            for i in list(self.occ[v << 1]) + list(self.occ[(v << 1) | 1]):
                self._remove_clause(i)
            self.stats.eliminated_vars += 1
        return True

    # -- driver -------------------------------------------------------------

    def run(self, rounds: int = 3) -> CNF:
        """Run the simplification loop and return the reduced formula."""
        for _ in range(rounds):
            self.stats.rounds += 1
            before = (self.stats.subsumed, self.stats.strengthened, self.stats.eliminated_vars)
            if not self.propagate():
                break
            self.subsume()
            if self.unsat:
                break
            self._pure_literals()
            if self.do_bce:
                self.block_eliminate()
            if self.do_bve and not self.eliminate_vars():
                break
            if not self.propagate():
                break
            after = (self.stats.subsumed, self.stats.strengthened, self.stats.eliminated_vars)
            if after == before:
                break
        return self.to_cnf()

    def to_cnf(self) -> CNF:
        out = CNF(self.orig_nvars)
        if self.unsat:
            out.add([])
            return out
        for i in self.alive():
            out.add(self.cls[i])
        out.nvars = self.orig_nvars
        return out

    # -- model reconstruction ----------------------------------------------

    def reconstruct(self, model: Sequence[bool]) -> list[bool]:
        """Extend a model of the reduced formula to the original variables.

        Walk the elimination stack in reverse.  For each recorded variable, if
        any of its stored clauses is currently unsatisfied, flip the variable
        to the polarity that satisfies it -- this always works, because every
        stored clause containing the opposite polarity was already accounted
        for by the resolvents that remain in the reduced formula.
        """
        full = [False] * self.orig_nvars
        for v in range(min(len(model), self.orig_nvars)):
            full[v] = model[v]
        for v, val in self.value.items():
            full[v] = val

        def sat(clause: Sequence[int]) -> bool:
            return any(full[l >> 1] != bool(l & 1) for l in clause)

        for v, clauses in reversed(self.eliminated):
            unsat_clauses = [c for c in clauses if not sat(c)]
            if not unsat_clauses:
                continue
            # Every unsatisfied clause must contain the *same* polarity of v --
            # that is the invariant the elimination establishes.  If clauses of
            # both polarities were unsatisfied, their resolvent on v would be
            # unsatisfied too, and that resolvent is still in the reduced
            # formula, contradicting the fact that `model` satisfies it.
            pos = any((v << 1) in c for c in unsat_clauses)
            neg_ = any(((v << 1) | 1) in c for c in unsat_clauses)
            if pos and neg_:
                raise AssertionError(
                    f"reconstruction invariant violated for x{v}: clauses of both "
                    "polarities are unsatisfied; the elimination stack is corrupt"
                )
            full[v] = pos
            if not all(sat(c) for c in clauses):
                raise AssertionError(
                    f"reconstruction failed for x{v}: flipping it did not satisfy "
                    "its stored clauses"
                )
        return full

    # -- reporting ----------------------------------------------------------

    def summary(self, reduced: CNF) -> str:
        return (
            f"c preprocessing: {self.orig_nvars} vars / {len(self.cls)} clause slots "
            f"-> {reduced.nvars} vars / {reduced.nclauses} clauses\n" + self.stats.report()
        )


def preprocess(formula: CNF, proof=None, **kw) -> tuple[CNF, Preprocessor]:
    """Convenience wrapper: returns ``(reduced_formula, preprocessor)``."""
    pre = Preprocessor(formula, proof=proof, **kw)
    return pre.run(), pre
