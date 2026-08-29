# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A small modelling layer: boolean variables with operators, finite-domain
integers, and the global constraints that make combinatorial problems readable.

The point is to write the *problem*, not the CNF::

    m = Model()
    x = m.int_var(range(1, 10), "x")
    y = m.int_var(range(1, 10), "y")
    m.add(x != y)
    m.all_different([x, y])
    sol = m.solve()
    print(sol[x], sol[y])

Integers are **one-hot** (direct) encoded: one boolean per value, exactly one
true.  The alternatives and why they lost here:

* *order encoding* (``x >= v`` booleans) propagates inequalities better and is
  the right choice for scheduling, but makes equality and all-different clumsy;
* *binary encoding* (log bits) is compact but propagates almost nothing --
  fixing one bit rules out half the domain and unit propagation notices very
  little;
* *one-hot* makes equality, membership and all-different into direct
  cardinality constraints with arc-consistent encodings, which is what the
  puzzle-shaped problems in ``examples/`` need.

Order-encoding channelling is provided by :meth:`Model.int_var(order=True)` for
the cases where inequality reasoning dominates: it adds the ``x >= v`` ladder
alongside the one-hot booleans and links them, giving both kinds of
propagation at the cost of n extra variables.
"""

from __future__ import annotations

from typing import Iterable, Sequence

from dratify.cnf import CNF
from .encodings import Encoder
from dratify.lits import mk_lit, neg
from .solver import Config, Solver

__all__ = ["Model", "BoolVar", "IntVar", "Solution"]


class BoolVar:
    """A boolean, with operators that build expression trees for Tseitin."""

    __slots__ = ("lit", "model", "name")

    def __init__(self, model: "Model", lit: int, name: str = "") -> None:
        self.model = model
        self.lit = lit
        self.name = name

    # expression building -- the results are plain tuples the Encoder speaks
    def __invert__(self):
        return BoolVar(self.model, neg(self.lit), f"~{self.name}")

    def __and__(self, other):
        return ("and", self.lit, _as_expr(other))

    def __or__(self, other):
        return ("or", self.lit, _as_expr(other))

    def __xor__(self, other):
        return ("xor", self.lit, _as_expr(other))

    def __rshift__(self, other):  # implication: a >> b
        return ("imp", self.lit, _as_expr(other))

    def iff(self, other):
        return ("iff", self.lit, _as_expr(other))

    def __repr__(self) -> str:
        return f"BoolVar({self.name or self.lit})"


def _as_expr(x):
    if isinstance(x, BoolVar):
        return x.lit
    if isinstance(x, bool):
        return x
    return x


class IntVar:
    """A finite-domain integer, one-hot encoded over ``domain``."""

    __slots__ = ("model", "domain", "lits", "name", "ge_lits")

    def __init__(self, model: "Model", domain: Sequence[int], name: str = "") -> None:
        self.model = model
        self.domain = list(domain)
        self.name = name
        self.lits = [model.new_lit(f"{name}={v}") for v in self.domain]
        self.ge_lits: list[int] | None = None
        model.enc.exactly_one(self.lits)

    def is_(self, value: int) -> int:
        """Literal for ``self == value`` (a false constant if out of domain)."""
        try:
            return self.lits[self.domain.index(value)]
        except ValueError:
            return self.model.enc.false_lit

    def __eq__(self, other):  # type: ignore[override]
        if isinstance(other, IntVar):
            return ("and", *[
                ("iff", self.is_(v), other.is_(v)) for v in set(self.domain) | set(other.domain)
            ])
        return self.is_(other)

    def __ne__(self, other):  # type: ignore[override]
        if isinstance(other, IntVar):
            return ("and", *[
                ("not", ("and", self.is_(v), other.is_(v)))
                for v in set(self.domain) & set(other.domain)
            ])
        return ("not", self.is_(other))

    def in_(self, values: Iterable[int]) -> tuple:
        vals = set(values)
        return ("or", *[self.is_(v) for v in self.domain if v in vals])

    # -- order encoding ----------------------------------------------------

    def build_order(self) -> list[int]:
        """Add the ``x >= v`` ladder and channel it to the one-hot booleans."""
        if self.ge_lits is not None:
            return self.ge_lits
        enc = self.model.enc
        ge = [self.model.new_lit(f"{self.name}>={v}") for v in self.domain]
        for i in range(len(ge) - 1):
            enc.add([neg(ge[i + 1]), ge[i]])  # x >= v+1  ->  x >= v
        enc.add([ge[0]])  # always >= min(domain)
        for i, l in enumerate(self.lits):
            enc.add([neg(l), ge[i]])
            if i + 1 < len(ge):
                enc.add([neg(l), neg(ge[i + 1])])
            # channel back: (x >= v) and not (x >= v+1)  ->  x = v
            body = [neg(ge[i]), l]
            if i + 1 < len(ge):
                body.append(ge[i + 1])
            enc.add(body)
        self.ge_lits = ge
        return ge

    def ge(self, value: int) -> int:
        """Literal for ``self >= value``."""
        ge = self.build_order()
        for i, v in enumerate(self.domain):
            if v >= value:
                return ge[i]
        return self.model.enc.false_lit

    def le(self, value: int) -> int:
        return neg(self.ge(value + 1)) if value + 1 <= max(self.domain) else self.model.enc.true_lit

    def __repr__(self) -> str:
        return f"IntVar({self.name}, {self.domain[0]}..{self.domain[-1]})"

    def __hash__(self):
        return id(self)


class Solution:
    """Read values back out of a model."""

    __slots__ = ("bits",)

    def __init__(self, bits: Sequence[bool]) -> None:
        self.bits = list(bits)

    def _lit(self, l: int) -> bool:
        return self.bits[l >> 1] != bool(l & 1)

    def __getitem__(self, var):
        if isinstance(var, BoolVar):
            return self._lit(var.lit)
        if isinstance(var, IntVar):
            for v, l in zip(var.domain, var.lits):
                if self._lit(l):
                    return v
            raise KeyError(f"{var} has no value in this solution")
        if isinstance(var, int):
            return self._lit(var)
        raise TypeError(type(var))

    def value(self, var):
        return self[var]


class Model:
    """A problem being built.  Owns the CNF, the encoder and the solver."""

    def __init__(self, config: Config | None = None,
                 encoding_method: str | None = None) -> None:
        self.cnf = CNF()
        self.enc = Encoder(self.cnf)
        self.config = config
        self.solver: Solver | None = None
        self._names: dict[int, str] = {}
        #: Overrides the `method` argument of every cardinality constraint.
        #: Set by :func:`differential_solve` to build the same problem twice
        #: with different encodings; None leaves each call's own choice alone.
        self.encoding_method = encoding_method

    #: methods each constraint kind accepts, mirroring cdclkit/encodings.py
    AMO_METHODS = ("pairwise", "binary", "commander", "sequential")
    AMK_METHODS = ("sequential", "totalizer")

    def _method(self, method: str, valid: tuple[str, ...]) -> str:
        """Apply the model-wide override, but only where it means something.

        `pairwise` is an at-most-one encoding and `totalizer` an at-most-k one,
        so a single global override cannot apply to both. Constraints the
        override does not fit keep the caller's choice rather than raising --
        a differential run then varies the constraints the method applies to
        and leaves the rest identical, which is still a valid comparison.
        """
        if self.encoding_method and self.encoding_method in valid:
            return self.encoding_method
        return method

    # -- variables ----------------------------------------------------------

    def new_lit(self, name: str = "") -> int:
        v = self.cnf.new_var(name or None)
        return mk_lit(v)

    def bool_var(self, name: str = "") -> BoolVar:
        return BoolVar(self, self.new_lit(name), name)

    def bool_vars(self, n: int, prefix: str = "b") -> list[BoolVar]:
        return [self.bool_var(f"{prefix}{i}") for i in range(n)]

    def int_var(self, domain: Iterable[int], name: str = "", order: bool = False) -> IntVar:
        iv = IntVar(self, list(domain), name)
        if order:
            iv.build_order()
        return iv

    def int_vars(self, n: int, domain: Iterable[int], prefix: str = "n") -> list[IntVar]:
        dom = list(domain)
        return [self.int_var(dom, f"{prefix}{i}") for i in range(n)]

    # -- constraints --------------------------------------------------------

    def add(self, expr) -> None:
        """Assert an expression (a tree, a literal, or a BoolVar)."""
        self.enc.assert_expr(_as_expr(expr))

    def add_clause(self, lits: Iterable[int]) -> None:
        self.enc.add([_as_expr(l) for l in lits])

    def all_different(self, variables: Sequence[IntVar]) -> None:
        """Pairwise-distinct, encoded value by value.

        For each value, at most one variable takes it -- which is exactly an
        at-most-one constraint over the one-hot literals for that value, and so
        inherits the arc consistency of the chosen at-most-one encoding.  This
        is strictly stronger propagation than pairwise ``x != y`` clauses and
        uses fewer clauses once the domain is larger than a handful.
        """
        values = sorted({v for x in variables for v in x.domain})
        for val in values:
            lits = [x.is_(val) for x in variables if val in x.domain]
            if len(lits) > 1:
                self.enc.at_most_one(lits)

    def all_different_permutation(self, variables: Sequence[IntVar]) -> None:
        """All-different where #variables == #values: adds the exactly-one
        constraint in the other direction too, a redundant constraint that
        cuts search dramatically on Latin-square-shaped problems."""
        self.all_different(variables)
        values = sorted({v for x in variables for v in x.domain})
        if len(values) == len(variables):
            for val in values:
                self.enc.at_least_one([x.is_(val) for x in variables if val in x.domain])

    def at_most_one(self, items, method: str = "auto") -> None:
        self.enc.at_most_one([_lit_of(i) for i in items],
                             self._method(method, self.AMO_METHODS))

    def exactly_one(self, items, method: str = "auto") -> None:
        self.enc.exactly_one([_lit_of(i) for i in items],
                             self._method(method, self.AMO_METHODS))

    def at_most_k(self, items, k: int, method: str = "auto") -> None:
        self.enc.at_most_k([_lit_of(i) for i in items], k,
                        self._method(method, self.AMK_METHODS))

    def at_least_k(self, items, k: int, method: str = "auto") -> None:
        self.enc.at_least_k([_lit_of(i) for i in items], k,
                        self._method(method, self.AMK_METHODS))

    def exactly_k(self, items, k: int, method: str = "auto") -> None:
        self.enc.exactly_k([_lit_of(i) for i in items], k,
                        self._method(method, self.AMK_METHODS))

    def sum_leq(self, weights: Sequence[int], items, bound: int) -> None:
        self.enc.assert_pb_leq(weights, [_lit_of(i) for i in items], bound)

    def sum_geq(self, weights: Sequence[int], items, bound: int) -> None:
        self.enc.assert_pb_geq(weights, [_lit_of(i) for i in items], bound)

    def parity(self, items, odd: bool = True) -> None:
        self.enc.xor_chain([_lit_of(i) for i in items], value=odd)

    # -- solving ------------------------------------------------------------

    def build_solver(self, proof=None) -> Solver:
        s = Solver(self.cnf.nvars, proof=proof, config=self.config)
        s.add_cnf(self.cnf)
        self.solver = s
        return s

    def solve(self, proof=None, assumptions: Sequence[int] = ()) -> Solution | None:
        s = self.solver if self.solver is not None else self.build_solver(proof)
        if s.nvars < self.cnf.nvars:  # new constraints since the last build
            s = self.build_solver(proof)
        return Solution(s.model) if s.solve(assumptions) else None

    def solutions(self, project: Sequence[IntVar | BoolVar] | None = None, limit: int = 0):
        """Iterate over distinct solutions, optionally projected onto variables."""
        s = self.build_solver()
        proj = None
        if project is not None:
            proj = []
            for v in project:
                if isinstance(v, IntVar):
                    proj.extend(l >> 1 for l in v.lits)
                else:
                    proj.append(v.lit >> 1)
        for bits in s.enumerate_models(projection=proj, limit=limit):
            yield Solution(bits)

    def stats(self) -> dict:
        return self.cnf.stats()


def _lit_of(x) -> int:
    if isinstance(x, BoolVar):
        return x.lit
    if isinstance(x, int):
        return x
    raise TypeError(f"expected a literal or BoolVar, got {type(x)}")


# --------------------------------------------------------------------------
# differential encoding
# --------------------------------------------------------------------------


class EncodingDisagreement(AssertionError):
    """Two encodings of the same problem reached different verdicts.

    One of them is wrong, and neither the solver nor its proof can tell you
    which: a DRAT refutation certifies *the CNF it was given*, not that the CNF
    says what you meant. That translation is the last unchecked step in every
    verification pipeline, this one included, and it is the step nobody
    verifies -- the formally verified solvers and checkers all take CNF as
    their input and start from there.
    """


def differential_solve(build, methods=("pairwise", "commander"),
                       config: Config | None = None, verify: bool = True):
    """Build the same problem under two encodings; require the same verdict.

    `build(model)` constructs the problem. It is called once per method, on a
    fresh :class:`Model` whose `encoding_method` is set, so the *constraints*
    are identical and only their translation to clauses differs.

    This is the two-checker discipline applied one level up. The solver already
    has two independent implementations that must agree, and every UNSAT answer
    already carries a proof replayed by a checker sharing no code with it. None
    of that touches the encoder. Encoding a cardinality constraint two ways and
    requiring the same answer is the cheapest available check on the one
    remaining unverified translation.

    Returns the :class:`Solution` (or None for unsatisfiable) from the first
    method. Raises :class:`EncodingDisagreement` when the methods disagree.

        >>> def build(m):
        ...     xs = m.bool_vars(5)
        ...     m.at_most_k(xs, 2)
        ...     m.add_clause([_lit_of(x) for x in xs])
        >>> differential_solve(build, methods=("sequential", "totalizer"))
        ...                                      # doctest: +ELLIPSIS
        <...Solution...>
    """
    verdicts, first = [], None
    for method in methods:
        m = Model(config=config, encoding_method=method)
        build(m)
        sol = m.solve()
        # A satisfying assignment must satisfy the formula that produced it.
        # Checking here means a disagreement is attributed to the encoding
        # rather than to the solver, which is the whole point of the exercise.
        if verify and sol is not None and not m.cnf.is_satisfied_by(sol.bits):
            raise EncodingDisagreement(
                f"the {method!r} encoding produced a model that does not "
                f"satisfy its own CNF -- that is a solver bug, not an "
                f"encoding one"
            )
        verdicts.append((method, sol is not None))
        if first is None:
            first = sol

    answers = {sat for _, sat in verdicts}
    if len(answers) > 1:
        detail = ", ".join(f"{m}={'SAT' if v else 'UNSAT'}" for m, v in verdicts)
        raise EncodingDisagreement(
            f"encodings disagree on the same problem: {detail}. One of these "
            f"translations is wrong. A proof would not have caught this: it "
            f"certifies the clauses, not that the clauses mean the constraint."
        )
    return first
