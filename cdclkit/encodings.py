# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Turning things that are not CNF into CNF.

Almost nothing anyone wants to solve is naturally a conjunction of clauses.
This module is the bridge: boolean circuits via Tseitin, "at most k of these",
weighted sums, parity.  The choice of encoding matters more than almost any
solver tuning, so each one here documents its size and, crucially, its
*propagation strength*.

Propagation strength, precisely
-------------------------------
An encoding of a constraint ``C`` is **arc consistent under unit propagation**
(often "generalised arc consistent", GAC) when, for every partial assignment
to the constrained variables, unit propagation on the encoding fixes every
literal that ``C`` itself would fix.  Example: with ``x1+...+x5 <= 2`` and
``x1=x2=1`` already set, a GAC encoding propagates ``x3=x4=x5=0`` immediately.
A non-GAC encoding may need the solver to *search* and hit a conflict first.
That difference is worth orders of magnitude on constraint-heavy instances.

Summary of what is here
-----------------------

======================  ==========  ================  =========================
encoding                aux vars    clauses           propagation
======================  ==========  ================  =========================
pairwise AMO            0           n(n-1)/2          GAC
binary (bimander) AMO   log n       n log n           GAC on inputs, aux vars
commander AMO           ~n/2        ~3.5 n            GAC
sequential AMK (Sinz)   n*k         ~2nk              GAC
totalizer AMK           ~n log n    O(n^2) (O(nk) cut) GAC, and incremental
BDD PB                  |BDD|       4*|BDD|           GAC
XOR chain               n-2         4(n-2)            GAC on the chain
======================  ==========  ================  =========================

"Incremental" for the totalizer means the bound can be *tightened* later by
adding one unit clause, without re-encoding anything -- which is what makes it
the right structure for MaxSAT-style optimisation loops.  :func:`optimise` in
this module uses exactly that.
"""

from __future__ import annotations

from itertools import product
from typing import Iterable, Sequence

from dratify.cnf import CNF
from dratify.lits import mk_lit, neg

__all__ = [
    "Encoder",
    "SolverSink",
    "at_most_one",
    "at_least_one",
    "exactly_one",
    "at_most_k",
    "at_least_k",
    "exactly_k",
    "Totalizer",
    "Optimiser",
    "optimise",
]


class SolverSink:
    """Adapts a :class:`~cdclkit.solver.Solver` to the encoder's sink protocol."""

    __slots__ = ("solver",)

    def __init__(self, solver) -> None:
        self.solver = solver

    def new_var(self, name: str | None = None) -> int:
        return self.solver.new_var()

    def add(self, lits) -> bool:
        return self.solver.add_clause(lits)

    @property
    def nvars(self) -> int:
        return self.solver.nvars


def _as_sink(target):
    if hasattr(target, "add_clause"):
        return SolverSink(target)
    return target


# --------------------------------------------------------------------------
# the encoder
# --------------------------------------------------------------------------


class Encoder:
    """Builds CNF into a sink (a :class:`CNF` or a :class:`Solver`).

    All gate constructors return a *literal* standing for the gate output and
    assert the full equivalence (both implication directions).  Polarity-aware
    Tseitin -- emitting only the direction that the surrounding formula needs --
    halves the clause count, and :meth:`tseitin` does apply it when you tell it
    the polarity; the individual ``*_gate`` helpers stay complete because they
    are also used to *define* variables the caller may reference either way.
    """

    #: Cap on :meth:`xor_direct`, which emits 2^(k-1) clauses.  16 inputs is
    #: 32768 clauses -- large but survivable, and the point of the direct form
    #: is to cross-check the chain on small arities, not to replace it.
    MAX_DIRECT_XOR_ARITY = 16

    #: Cap on :meth:`assert_expr_expanded`, which enumerates 2^v rows over the
    #: v variables an expression mentions.  12 is 4096 rows per conjunct.
    MAX_EXPAND_ARITY = 12

    def __init__(self, target=None) -> None:
        self.sink = _as_sink(target if target is not None else CNF())
        self._true: int | None = None
        self._cache: dict[tuple, int] = {}
        self.n_clauses_emitted = 0
        self.n_aux = 0

    # -- plumbing -----------------------------------------------------------

    @property
    def formula(self):
        return self.sink.solver if isinstance(self.sink, SolverSink) else self.sink

    def new_var(self, name: str | None = None) -> int:
        self.n_aux += 1
        try:
            return self.sink.new_var(name)
        except TypeError:
            return self.sink.new_var()

    def new_lit(self, name: str | None = None) -> int:
        return mk_lit(self.new_var(name))

    def add(self, lits: Iterable[int]) -> None:
        self.n_clauses_emitted += 1
        self.sink.add(list(lits))

    def add_all(self, clauses: Iterable[Iterable[int]]) -> None:
        for c in clauses:
            self.add(c)

    @property
    def true_lit(self) -> int:
        """A literal that is forced true, created on first use."""
        if self._true is None:
            v = self.new_var("__true")
            self._true = mk_lit(v)
            self.add([self._true])
        return self._true

    @property
    def false_lit(self) -> int:
        return neg(self.true_lit)

    # -- gates --------------------------------------------------------------

    def and_gate(self, lits: Sequence[int], out: int | None = None) -> int:
        """``out <-> AND(lits)``.  Returns ``out``."""
        lits = self._simplify_and(lits)
        if lits is None:
            return self.false_lit
        if not lits:
            return self.true_lit
        if len(lits) == 1 and out is None:
            return lits[0]
        key = ("and", tuple(sorted(lits)))
        if out is None and key in self._cache:
            return self._cache[key]
        if out is None:
            out = self.new_lit()
            self._cache[key] = out
        for l in lits:  # out -> l
            self.add([neg(out), l])
        self.add([out] + [neg(l) for l in lits])  # AND(lits) -> out
        return out

    def or_gate(self, lits: Sequence[int], out: int | None = None) -> int:
        """``out <-> OR(lits)``."""
        inner = self.and_gate([neg(l) for l in lits], None if out is None else neg(out))
        return neg(inner)

    def xor_gate(self, a: int, b: int, out: int | None = None) -> int:
        """``out <-> a XOR b``."""
        key = ("xor", min(a, b), max(a, b))
        if out is None and key in self._cache:
            return self._cache[key]
        if out is None:
            out = self.new_lit()
            self._cache[key] = out
        self.add([neg(out), a, b])
        self.add([neg(out), neg(a), neg(b)])
        self.add([out, neg(a), b])
        self.add([out, a, neg(b)])
        return out

    def xor_chain(self, lits: Sequence[int], value: bool = True) -> None:
        """Assert ``XOR(lits) == value`` with a chain of 3-variable XOR gates.

        A direct CNF encoding of a k-way XOR needs 2^(k-1) clauses; the chain
        needs 4(k-2) clauses and k-2 auxiliary variables, and unit propagation
        on the chain is as strong as on the direct form as long as literals are
        fixed from the ends inwards.
        """
        if not lits:
            if value:
                self.add([])  # empty XOR is false; asserting true is a contradiction
            return
        if len(lits) == 1:
            self.add([lits[0] if value else neg(lits[0])])
            return
        acc = lits[0]
        for l in lits[1:-1]:
            acc = self.xor_gate(acc, l)
        a, b = acc, lits[-1]
        if value:
            self.add([a, b])
            self.add([neg(a), neg(b)])
        else:
            self.add([a, neg(b)])
            self.add([neg(a), b])

    def ite(self, c: int, t: int, e: int, out: int | None = None) -> int:
        """``out <-> (c ? t : e)``, the primitive every BDD encoding needs."""
        if t == e:
            return t
        key = ("ite", c, t, e)
        if out is None and key in self._cache:
            return self._cache[key]
        if out is None:
            out = self.new_lit()
            self._cache[key] = out
        self.add([neg(out), neg(c), t])
        self.add([neg(out), c, e])
        self.add([out, neg(c), neg(t)])
        self.add([out, c, neg(e)])
        # redundant but propagation-strengthening: t & e -> out, ~t & ~e -> ~out
        self.add([neg(t), neg(e), out])
        self.add([t, e, neg(out)])
        return out

    def implies(self, a: int, b: int) -> None:
        self.add([neg(a), b])

    def equiv(self, a: int, b: int) -> None:
        self.add([neg(a), b])
        self.add([a, neg(b)])

    def _simplify_and(self, lits: Sequence[int]) -> list[int] | None:
        """Deduplicate; return None when the conjunction is trivially false."""
        seen: set[int] = set()
        out: list[int] = []
        for l in lits:
            if l == self._true:
                continue
            if self._true is not None and l == neg(self._true):
                return None
            if l in seen:
                continue
            if neg(l) in seen:
                return None
            seen.add(l)
            out.append(l)
        return out

    # -- expression trees ---------------------------------------------------

    def tseitin(self, expr, polarity: int = 0) -> int:
        """Encode a nested expression tree, returning its output literal.

        The tree is built from plain tuples::

            ("and", e1, e2, ...)   ("or", ...)   ("xor", e1, e2)
            ("not", e)             ("ite", c, t, e)      ("imp", a, b)
            ("iff", a, b)          <int literal>

        ``polarity`` is +1 when the expression only ever needs to be *forced
        true* (so only the ``inputs -> out`` direction is required), -1 for the
        mirror case, 0 for both.  Using the polarity halves the clauses on
        large monotone circuits; it is safe exactly because a variable that
        occurs with one polarity can always be set to the value its definition
        prescribes.
        """
        if isinstance(expr, int):
            return expr
        op = expr[0]
        if op == "not":
            return neg(self.tseitin(expr[1], -polarity))
        if op == "and":
            kids = [self.tseitin(e, polarity) for e in expr[1:]]
            return self._and_pol(kids, polarity)
        if op == "or":
            kids = [self.tseitin(e, polarity) for e in expr[1:]]
            return neg(self._and_pol([neg(k) for k in kids], -polarity))
        if op == "imp":
            a = self.tseitin(expr[1], -polarity)
            b = self.tseitin(expr[2], polarity)
            return neg(self._and_pol([a, neg(b)], -polarity))
        if op == "iff":
            a = self.tseitin(expr[1], 0)
            b = self.tseitin(expr[2], 0)
            return neg(self.xor_gate(a, b))
        if op == "xor":
            a = self.tseitin(expr[1], 0)
            b = self.tseitin(expr[2], 0)
            return self.xor_gate(a, b)
        if op == "ite":
            c = self.tseitin(expr[1], 0)
            t = self.tseitin(expr[2], polarity)
            e = self.tseitin(expr[3], polarity)
            return self.ite(c, t, e)
        raise ValueError(f"unknown operator {op!r}")

    def _and_pol(self, lits: Sequence[int], polarity: int) -> int:
        lits = self._simplify_and(lits)
        if lits is None:
            return self.false_lit
        if not lits:
            return self.true_lit
        if len(lits) == 1:
            return lits[0]
        if polarity == 0:
            return self.and_gate(lits)
        out = self.new_lit()
        if polarity > 0:  # out -> AND(lits)
            for l in lits:
                self.add([neg(out), l])
        else:  # AND(lits) -> out
            self.add([out] + [neg(l) for l in lits])
        return out

    def assert_expr(self, expr) -> None:
        """Force an expression tree to be true, with polarity optimisation."""
        if isinstance(expr, tuple) and expr[0] == "and":
            for e in expr[1:]:
                self.assert_expr(e)
            return
        if isinstance(expr, tuple) and expr[0] == "or":
            self.add([self.tseitin(e, +1) for e in expr[1:]])
            return
        self.add([self.tseitin(expr, +1)])

    # ------------------------------------------------------------ at-most-one

    def amo_pairwise(self, lits: Sequence[int]) -> None:
        """n(n-1)/2 clauses, no auxiliary variables.  Best for n <= 6."""
        n = len(lits)
        for i in range(n):
            li = neg(lits[i])
            for j in range(i + 1, n):
                self.add([li, neg(lits[j])])

    def amo_binary(self, lits: Sequence[int]) -> None:
        """Bimander/binary encoding: ceil(log2 n) aux vars, n*log n clauses.

        Each input is assigned a distinct bit pattern and forced to agree with
        it; two inputs cannot both be true because their patterns differ in
        some bit.  Fixing one input true fixes every code bit, and every other
        input then has a clause with a false code literal, so propagation is as
        strong as pairwise on the inputs themselves.  What you pay for the size
        reduction is structural: log2(n) auxiliary variables enter the decision
        heuristic, and the encoding is silent until some input is set true.
        """
        n = len(lits)
        if n <= 1:
            return
        bits = max(1, (n - 1).bit_length())
        code = [self.new_lit() for _ in range(bits)]
        for i, x in enumerate(lits):
            nx = neg(x)
            for b in range(bits):
                self.add([nx, code[b] if (i >> b) & 1 else neg(code[b])])

    def amo_commander(self, lits: Sequence[int], group: int = 3) -> None:
        """Klieber-Kwon commander encoding: linear size *and* arc consistent.

        Split the inputs into groups.  Each group gets a commander variable
        equivalent to the disjunction of the group, the group itself gets a
        pairwise at-most-one, and the commanders are recursively constrained by
        the same encoding.  Roughly 3.5n clauses and n/2 variables, with unit
        propagation as strong as pairwise.
        """
        lits = list(lits)
        if len(lits) <= group:
            self.amo_pairwise(lits)
            return
        commanders: list[int] = []
        for i in range(0, len(lits), group):
            g = lits[i : i + group]
            if len(g) == 1:
                commanders.append(g[0])
                continue
            c = self.new_lit()
            self.amo_pairwise(g)
            for x in g:  # x -> c
                self.add([neg(x), c])
            self.add([neg(c)] + list(g))  # c -> OR(g)
            commanders.append(c)
        self.amo_commander(commanders, group)

    def at_most_one(self, lits: Sequence[int], method: str = "auto") -> None:
        if method == "auto":
            method = "pairwise" if len(lits) <= 6 else "commander"
        if method == "pairwise":
            self.amo_pairwise(lits)
        elif method == "binary":
            self.amo_binary(lits)
        elif method == "commander":
            self.amo_commander(lits)
        elif method == "sequential":
            self.amk_sequential(lits, 1)
        elif method == "totalizer":
            self.amk_totalizer(lits, 1)
        else:
            raise ValueError(f"unknown at-most-one method {method!r}")

    def at_least_one(self, lits: Sequence[int]) -> None:
        self.add(list(lits))

    def exactly_one(self, lits: Sequence[int], method: str = "auto") -> None:
        self.at_least_one(lits)
        self.at_most_one(lits, method)

    # -------------------------------------------------------------- at-most-k

    def amk_sequential(self, lits: Sequence[int], k: int) -> None:
        """Sinz's sequential counter: n*k aux vars, ~2nk clauses, arc consistent.

        ``s[i][j]`` means "at least j of the first i inputs are true".  The
        clauses are just the recurrence
        ``s[i][j] <- s[i-1][j] or (x_i and s[i-1][j-1])`` in implication form,
        plus the blocking clause ``~x_i or ~s[i-1][k]``.
        """
        n = len(lits)
        if k >= n:
            return
        if k < 0:
            self.add([])
            return
        if k == 0:
            for x in lits:
                self.add([neg(x)])
            return
        s = [[self.new_lit() for _ in range(k)] for _ in range(n - 1)]
        self.add([neg(lits[0]), s[0][0]])
        for j in range(1, k):
            self.add([neg(s[0][j])])
        for i in range(1, n - 1):
            self.add([neg(lits[i]), s[i][0]])
            self.add([neg(s[i - 1][0]), s[i][0]])
            for j in range(1, k):
                self.add([neg(lits[i]), neg(s[i - 1][j - 1]), s[i][j]])
                self.add([neg(s[i - 1][j]), s[i][j]])
            self.add([neg(lits[i]), neg(s[i - 1][k - 1])])
        self.add([neg(lits[n - 1]), neg(s[n - 2][k - 1])])

    def amk_totalizer(self, lits: Sequence[int], k: int) -> "Totalizer":
        """Build a totalizer and assert ``sum <= k``.  Returns the totalizer."""
        t = Totalizer(self, lits, max_count=k + 1)
        t.assert_at_most(k)
        return t

    def at_most_k(self, lits: Sequence[int], k: int, method: str = "auto") -> None:
        n = len(lits)
        if k >= n:
            return
        if k <= 0:
            for x in lits:
                self.add([neg(x)])
            return
        if k == 1 and method in ("auto", "commander", "pairwise", "binary"):
            self.at_most_one(lits, "auto" if method == "auto" else method)
            return
        if method == "auto":
            method = "sequential" if k * n <= 20000 else "totalizer"
        if method == "sequential":
            self.amk_sequential(lits, k)
        elif method == "totalizer":
            self.amk_totalizer(lits, k)
        else:
            raise ValueError(f"unknown at-most-k method {method!r}")

    def at_least_k(self, lits: Sequence[int], k: int, method: str = "auto") -> None:
        """``sum(lits) >= k``  <=>  ``sum(~lits) <= n - k``."""
        n = len(lits)
        if k <= 0:
            return
        if k > n:
            self.add([])
            return
        if k == 1:
            self.at_least_one(lits)
            return
        self.at_most_k([neg(l) for l in lits], n - k, method)

    def exactly_k(self, lits: Sequence[int], k: int, method: str = "auto") -> None:
        self.at_most_k(lits, k, method)
        self.at_least_k(lits, k, method)

    # ------------------------------------------------------- pseudo-boolean

    def pb_leq(self, weights: Sequence[int], lits: Sequence[int], bound: int) -> int:
        """Encode ``sum(w_i * l_i) <= bound`` as a BDD; returns the root literal.

        The BDD is the reduced decision diagram of the constraint under the
        input order given, built top-down with memoisation on
        ``(index, remaining_slack)``.  Each node becomes one ITE gate, so the
        encoding is GAC and its size is the BDD's size -- which for a single PB
        constraint is O(n * bound) nodes in the worst case and usually far
        smaller after reduction.

        Negative weights are handled by the standard transformation
        ``w * l = w - w * ~l``, which is applied automatically.
        """
        if len(weights) != len(lits):
            raise ValueError("weights and literals must have equal length")
        ws: list[int] = []
        ls: list[int] = []
        b = bound
        for w, l in zip(weights, lits):
            if w == 0:
                continue
            if w < 0:
                b -= w  # sum += -w * ~l  after moving the constant across
                ws.append(-w)
                ls.append(neg(l))
            else:
                ws.append(w)
                ls.append(l)
        order = sorted(range(len(ws)), key=lambda i: -ws[i])
        ws = [ws[i] for i in order]
        ls = [ls[i] for i in order]
        suffix = [0] * (len(ws) + 1)
        for i in range(len(ws) - 1, -1, -1):
            suffix[i] = suffix[i + 1] + ws[i]
        memo: dict[tuple[int, int], int] = {}

        def build(i: int, slack: int) -> int:
            if slack < 0:
                return self.false_lit
            if slack >= suffix[i]:
                return self.true_lit
            key = (i, slack)
            hit = memo.get(key)
            if hit is not None:
                return hit
            hi = build(i + 1, slack - ws[i])
            lo = build(i + 1, slack)
            out = self.ite(ls[i], hi, lo)
            memo[key] = out
            return out

        root = build(0, b)
        return root

    def pb_geq(self, weights: Sequence[int], lits: Sequence[int], bound: int) -> int:
        """``sum(w_i l_i) >= bound``, by negating every literal."""
        total = sum(weights)
        return self.pb_leq(weights, [neg(l) for l in lits], total - bound)

    def assert_pb_leq(self, weights, lits, bound: int) -> None:
        self.add([self.pb_leq(weights, lits, bound)])

    def assert_pb_geq(self, weights, lits, bound: int) -> None:
        self.add([self.pb_geq(weights, lits, bound)])

    def assert_pb_eq(self, weights, lits, value: int) -> None:
        self.assert_pb_leq(weights, lits, value)
        self.assert_pb_geq(weights, lits, value)


# --------------------------------------------------------------------------
# totalizer
# --------------------------------------------------------------------------


class Totalizer:
    """Bailleux-Boufkhad totalizer: a unary counter tree over input literals.

    ``out[i]`` (0-based) is true iff **at least i+1** inputs are true.  The
    encoding is arc consistent, and both bounds are enforced by unit clauses on
    the outputs:

    * ``sum <= k``  --  assert ``~out[k]``
    * ``sum >= k``  --  assert ``out[k-1]``

    Because the bound is a *unit clause on an existing variable*, it can be
    tightened at any later point without touching the encoding -- add another
    unit, or pass it as an assumption to keep it retractable.  That is the
    property optimisation loops are built on, and it is why the totalizer is
    the workhorse of modern MaxSAT solvers.

    ``max_count`` truncates the counter: outputs above the cut are never
    created, since a bound of k never needs to distinguish k+2 from k+3.  The
    truncated version is still arc consistent for the bound it was built for.
    """

    def __init__(self, enc: Encoder, lits: Sequence[int], max_count: int | None = None):
        self.enc = enc
        self.inputs = list(lits)
        self.max_count = len(self.inputs) if max_count is None else min(
            max_count, len(self.inputs)
        )
        self.outputs = self._build(self.inputs)

    def _build(self, lits: Sequence[int]) -> list[int]:
        if len(lits) == 1:
            return [lits[0]]
        mid = len(lits) // 2
        a = self._build(lits[:mid])
        b = self._build(lits[mid:])
        return self._merge(a, b)

    def _merge(self, a: list[int], b: list[int]) -> list[int]:
        enc = self.enc
        m, n = len(a), len(b)
        size = min(m + n, self.max_count)
        out = [enc.new_lit() for _ in range(size)]
        # "at least" direction: alpha from a and beta from b imply alpha+beta
        for alpha in range(m + 1):
            for beta in range(n + 1):
                sigma = alpha + beta
                if sigma < 1 or sigma > size:
                    continue
                clause = [out[sigma - 1]]
                if alpha > 0:
                    clause.append(neg(a[alpha - 1]))
                if beta > 0:
                    clause.append(neg(b[beta - 1]))
                enc.add(clause)
        # "at most" direction: not alpha and not beta imply not alpha+beta+1
        for alpha in range(m + 1):
            for beta in range(n + 1):
                sigma = alpha + beta
                if sigma >= size:
                    continue
                clause = [neg(out[sigma])]
                if alpha < m:
                    clause.append(a[alpha])
                if beta < n:
                    clause.append(b[beta])
                enc.add(clause)
        return out

    # -- bounds -------------------------------------------------------------

    def at_most_lit(self, k: int) -> int | None:
        """Literal asserting ``sum <= k``; None when the bound is vacuous."""
        if k >= len(self.inputs):
            return None
        if k < 0:
            return self.enc.false_lit
        if k >= len(self.outputs):
            return None
        return neg(self.outputs[k])

    def at_least_lit(self, k: int) -> int | None:
        if k <= 0:
            return None
        if k > len(self.inputs) or k > len(self.outputs):
            return self.enc.false_lit
        return self.outputs[k - 1]

    def assert_at_most(self, k: int) -> None:
        l = self.at_most_lit(k)
        if l is not None:
            self.enc.add([l])

    def assert_at_least(self, k: int) -> None:
        l = self.at_least_lit(k)
        if l is not None:
            self.enc.add([l])


# --------------------------------------------------------------------------
# free functions over a fresh CNF (convenience)
# --------------------------------------------------------------------------


def _wrap(target):
    return target if isinstance(target, Encoder) else Encoder(target)


def at_most_one(target, lits, method="auto"):
    _wrap(target).at_most_one(lits, method)


def at_least_one(target, lits):
    _wrap(target).at_least_one(lits)


def exactly_one(target, lits, method="auto"):
    _wrap(target).exactly_one(lits, method)


def at_most_k(target, lits, k, method="auto"):
    _wrap(target).at_most_k(lits, k, method)


def at_least_k(target, lits, k, method="auto"):
    _wrap(target).at_least_k(lits, k, method)


def exactly_k(target, lits, k, method="auto"):
    _wrap(target).exactly_k(lits, k, method)


# --------------------------------------------------------------------------
# optimisation on top of the totalizer
# --------------------------------------------------------------------------


class Optimiser:
    """Incremental optimisation over a fixed set of soft literals.

    Owns the totalizer, so the bound can be tightened repeatedly without
    re-encoding anything and without the solver losing a single learnt clause.
    That matters: the free function :func:`optimise` builds a totalizer per
    call, so calling it twice on the same solver would encode the counter
    twice.  Use this class when you want to optimise more than once, resume
    after a budget, or drive the search yourself.

    Usage::

        opt = Optimiser(solver, soft_lits)
        best = opt.run()                 # linear SAT-UNSAT search
        ...
        best = opt.run(target=best[0] - 5)   # resume with a stronger demand
    """

    def __init__(self, solver, soft_lits: Sequence[int], minimise: bool = True) -> None:
        from .solver import Solver  # local import: avoids a cycle at module load

        assert isinstance(solver, Solver)
        self.solver = solver
        self.minimise = minimise
        self.soft = list(soft_lits)
        # counting "true among soft" for minimisation, "false among soft" for
        # maximisation, which is the same counter over negated literals
        self.counted = self.soft if minimise else [neg(l) for l in self.soft]
        self.enc = Encoder(solver)
        self.totalizer = Totalizer(self.enc, self.counted) if self.counted else None
        self.best: tuple[int, list[bool]] | None = None
        self.iterations = 0

    # -- one step -----------------------------------------------------------

    def count(self, model: Sequence[bool]) -> int:
        return sum(1 for l in self.counted if model[l >> 1] != bool(l & 1))

    def solve_with_bound(self, bound: int | None, permanent: bool = False):
        """Solve demanding ``count <= bound``.  Returns a model or None."""
        assumptions: list[int] = []
        if bound is not None and self.totalizer is not None:
            lit = self.totalizer.at_most_lit(bound)
            if lit is not None:
                if permanent:
                    self.solver.add_clause([lit])
                else:
                    assumptions = [lit]
        if not self.solver.solve(assumptions):
            return None
        return list(self.solver.model)

    # -- the loop -----------------------------------------------------------

    def run(self, target: int | None = None, max_iterations: int = 0, on_improve=None):
        """Linear SAT-UNSAT search from the current best.

        Every iteration produces a real model, so stopping early still leaves
        :attr:`best` holding the best solution found -- the property that
        matters when there is a time budget.
        """
        bound = target
        while True:
            model = self.solve_with_bound(bound)
            if model is None:
                break
            self.iterations += 1
            n = self.count(model)
            self.best = (n, model)
            if on_improve is not None:
                on_improve(n, model)
            if n == 0:
                break
            if max_iterations and self.iterations >= max_iterations:
                break
            bound = n - 1
        return self.result()

    def result(self):
        if self.best is None:
            return None
        n, model = self.best
        return (n if self.minimise else len(self.soft) - n, model)


def optimise(

    solver,
    soft_lits: Sequence[int],
    minimise: bool = True,
    assumption_based: bool = True,
    on_improve=None,
) -> tuple[int, list[bool]] | None:
    """Minimise (or maximise) the number of true literals among ``soft_lits``.

    Linear search from the top (SAT-UNSAT direction): solve, count, then demand
    strictly better, repeat until UNSAT.  Every intermediate result is a real
    model, so the search can be stopped at any point and still return the best
    solution found -- the property that matters when there is a time budget.

    With ``assumption_based`` the bound is imposed as an *assumption* rather
    than a permanent clause, so the totalizer never has to be rebuilt and the
    solver keeps every clause it learned across iterations.

    Returns ``(best_count, best_model)`` or None when the instance is UNSAT.

    This builds a fresh totalizer, so calling it twice on the same solver
    encodes the counter twice.  Use :class:`Optimiser` when you need more than
    one optimisation run against one solver.
    """
    opt = Optimiser(solver, soft_lits, minimise=minimise)
    if not assumption_based and opt.totalizer is not None:
        # permanent-bound variant: each bound becomes a unit clause
        bound = None
        while True:
            model = opt.solve_with_bound(bound, permanent=True)
            if model is None:
                break
            n = opt.count(model)
            opt.best = (n, model)
            if on_improve is not None:
                on_improve(n, model)
            if n == 0:
                break
            bound = n - 1
        return opt.result()
    return opt.run(on_improve=on_improve)
