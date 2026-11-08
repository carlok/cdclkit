# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Campaign corner: `cdclkit.model` and `cdclkit.pyeq` against brute force.

Two independent oracles, neither importing the code under test's logic:

* **Models.** Every constraint a generated `Model` receives is also held as a
  plain Python predicate over the user's variables, so direct enumeration gives
  the solution set and every optimum. `campaign.dpll` then judges the CNF
  itself, auxiliary variables included, without going through the solver.
* **pyeq.** Each generated function exists as a small IR. A fixed-width
  evaluator runs it on every input at the declared widths, wrapping after each
  operation. Where no intermediate overflowed, that evaluator must equal real
  Python on the rendered source; this is what stops it being a second copy of a
  misunderstanding. Probes outside the generated grammar are judged directly by
  running them in Python.

Run from the repo root:

    python -m campaign.gen_modelling                 # exit 1 on any mismatch
    python -m campaign.gen_modelling --self-test     # the harness catches stubs

Known findings stay mismatches. They are labelled with their finding id, and
the run exits non-zero until they are fixed.
"""

from __future__ import annotations

import argparse
import inspect
import itertools
import json
import os
import random
import sys
import tempfile
import time
from collections import Counter

from campaign import dpll

from cdclkit.encodings import optimise
from cdclkit.model import EncodingDisagreement, Model, differential_solve
from cdclkit.native import available as native_available
from cdclkit.pyeq import (
    UnsupportedConstruct,
    compile_function,
    equivalent as real_equivalent,
)
from cdclkit.encodings import Encoder
from cdclkit.solver import Solver
from dratify.cnf import CNF
from dratify.lits import neg, to_dimacs
from dratify.proof import MemoryProof, check_proof

DEFAULT_SEED = 20261108
DEFAULT_INSTANCES = 3000
RESULTS_PATH = os.path.join("campaign", "results", "modelling.json")

# Which finding a feature of an instance points to. A mismatch on an instance
# carrying one of these features is labelled, never dropped.
FEATURE_FINDING = {
    "value_boolop": "modelling-1",
    "bare_expr": "modelling-2",
    "decorator": "modelling-3",
    "range_shape": "modelling-4",
    "incremental": "modelling-5",
    "sols_then_solve": "modelling-6",
    "bool_const": "modelling-7",
    "negative_k": "modelling-8",
    "unsorted_order": "modelling-9",
    "dup_domain": "modelling-10",
    "empty_totalizer": "modelling-11",
    "extra_width": "modelling-12",
    "posonly": "modelling-13",
}

FINDINGS = [
    {"id": "modelling-1", "severity": "Critical",
     "summary": "pyeq compiles `x and y` / `x or y` in a value position to 0/1, not to the operand "
                "Python returns: wrong proved=True, and proved=False with overflow_only=True"},
    {"id": "modelling-2", "severity": "Critical",
     "summary": "pyeq drops every bare expression statement that is not a call: walrus, yield and "
                "raising expressions vanish, giving wrong proved=True"},
    {"id": "modelling-3", "severity": "Critical",
     "summary": "pyeq ignores decorators: a function wrapped with functools.wraps is compiled undecorated"},
    {"id": "modelling-4", "severity": "Critical",
     "summary": "pyeq accepts range() and range(stop=3) as empty loops, and a shadowed range as the "
                "builtin, proving equal functions that raise TypeError on every input"},
    {"id": "modelling-5", "severity": "Critical",
     "summary": "Model.solve reuses its solver when a new constraint adds no variable: the model "
                "returned violates the constraint, and a contradiction reads as SAT"},
    {"id": "modelling-6", "severity": "Bug",
     "summary": "Model.solve after Model.solutions keeps the blocking clauses: None on a satisfiable model"},
    {"id": "modelling-7", "severity": "Bug",
     "summary": "A Python bool in an expression becomes literal 0 or 1 of variable 0: m.add(True), "
                "b | False and a == b on BoolVars all constrain the first variable"},
    {"id": "modelling-8", "severity": "Bug",
     "summary": "at_most_k and exactly_k with k < 0 are satisfiable; the sum cannot be negative"},
    {"id": "modelling-9", "severity": "Bug",
     "summary": "IntVar.ge and le assume a sorted domain: wrong solutions on int_var([2, 1])"},
    {"id": "modelling-10", "severity": "Bug",
     "summary": "A repeated domain value gets two literals and is_ knows one: x != 1 still allows 1"},
    {"id": "modelling-11", "severity": "Bug",
     "summary": "at_most_one([]) and exactly_one([]) with method='totalizer' die with RecursionError"},
    {"id": "modelling-12", "severity": "Bug",
     "summary": "pyeq reports a width the circuit does not have: an unused key in widths claims "
                "'equivalent at 8 bits' for a 4-bit circuit, and no parameters claims 0 bits for 8"},
    {"id": "modelling-13", "severity": "Bug",
     "summary": "pyeq ignores positional-only parameters, then crashes with TypeError building "
                "python_outputs for a counterexample"},
    {"id": "modelling-14", "severity": "Note",
     "summary": "proof_steps differs between the engines, as tests/test_pyeq.py documents; a field "
                "disagreement that is not a bug"},
    {"id": "modelling-15", "severity": "Note",
     "summary": "Model.solutions() without project repeats user-level solutions, one per state of the "
                "auxiliary variables, under a docstring that says distinct"},
    {"id": "modelling-16", "severity": "Note",
     "summary": "differential_solve compares a CNF with itself when a model uses only all_different, "
                "sum_leq, sum_geq or parity"},
    {"id": "modelling-17", "severity": "Note",
     "summary": "pyeq accepts widths of 0 and below and proves anything at them, and treats an "
                "unknown engine name as Python"},
]

NOT_CHECKED = [
    "Model(config=...): every model runs under the default Config",
    "Model has no engine parameter, so native is judged on the Model's CNF, not through Model.solve",
    "Encoder gates called with an explicit out=, and Encoder features the Model API does not expose "
    "(campaign/gen_encodings.py owns them)",
    "Optimiser.run(target=...), max_iterations and resuming; only optimise() is run",
    "a weighted optimum has no API, so it is judged by bounding sum_leq at the optimum and one below",
    "CNF checks by DPLL look at up to 32 user assignments per model, not all of them",
    "unprojected solutions() is capped at 2000 models per instance",
    "EncodingDisagreement raised by a genuinely wrong encoding: none occurred, and no stub injects one",
    "pyeq above 9 input bits or 7 bits of width: the oracle enumerates every input",
    "pyeq's python_error field: no generated function raises in Python",
    "ProofRejected: no proof was rejected, and no stub injects a bad proof into pyeq",
    "pyeq on methods, closures and callables without source, beyond the probes",
    "examples/ and docs/tutorial/ programs",
]


class Tally:
    """Counters, plus every mismatch with whatever explains it."""

    def __init__(self) -> None:
        self.counts: Counter = Counter()
        self.mismatches: list[dict] = []
        self.steps = 0

    def step(self, category: str | None = None, n: int = 1) -> None:
        self.steps += n
        if category:
            self.counts[category] += n

    def bad(self, kind: str, detail: str, features=()) -> None:
        labels = sorted({FEATURE_FINDING[f] for f in features if f in FEATURE_FINDING})
        self.mismatches.append({"kind": kind, "detail": detail[:600], "labels": labels})

    @property
    def unexplained(self) -> list[dict]:
        return [m for m in self.mismatches if not m["labels"]]


# ==========================================================================
# Part 1: models
# ==========================================================================

AMO_METHODS = ("auto", "pairwise", "binary", "commander", "sequential", "totalizer")
AMK_METHODS = ("auto", "sequential", "totalizer")
OVERRIDES = (None, None, "pairwise", "binary", "commander", "sequential", "totalizer")
DIFF_METHODS = (
    ("pairwise", "commander"),
    ("binary", "sequential"),
    ("sequential", "totalizer"),
    ("pairwise", "totalizer"),
)


class Spec:
    """A model, as a recipe to build it and a predicate to judge it."""

    def __init__(self) -> None:
        self.nbools = 0
        self.domains: list[tuple[list[int], bool]] = []  # (domain, order)
        self.constraints: list[tuple] = []  # (build, holds, kind)
        self.features: set[str] = set()
        self.split = 0  # incremental: constraints before the first solve

    def names(self):
        return list(range(self.nbools)), list(range(len(self.domains)))

    def assignments(self):
        spaces = [(False, True)] * self.nbools + [sorted(set(d)) for d, _ in self.domains]
        return itertools.product(*spaces)

    def solutions(self):
        return {a for a in self.assignments()
                if all(holds(a) for _, holds, _ in self.constraints)}


class Handles:
    def __init__(self, spec: Spec, m) -> None:
        self.m = m
        self.bools = m.bool_vars(spec.nbools)
        self.ints = [m.int_var(d, f"n{i}", order=o)
                     for i, (d, o) in enumerate(spec.domains)]

    def all_vars(self):
        return [*self.bools, *self.ints]

    def read(self, sol):
        return tuple(sol[v] for v in self.all_vars())


def build_all(spec: Spec, impl=Model, encoding_method=None, upto=None):
    m = impl(encoding_method=encoding_method)
    h = Handles(spec, m)
    for build, _, _ in spec.constraints[:upto]:
        build(m, h)
    return m, h


def make_atom(rng: random.Random, spec: Spec, order_ok: bool = True):
    """A single literal: returns (render(h) -> BoolVar|int, holds(a) -> bool, plain)."""
    nb = spec.nbools
    choices = []
    if nb:
        choices += ["bool", "bool", "notbool"]
    if spec.domains:
        choices += ["is", "is", "eqc"]
        if order_ok:
            choices += ["ge", "le"]
    if not choices:
        return None
    kind = rng.choice(choices)
    if kind == "bool":
        i = rng.randrange(nb)
        return (lambda h: h.bools[i]), (lambda a: a[i])
    if kind == "notbool":
        i = rng.randrange(nb)
        return (lambda h: ~h.bools[i]), (lambda a: not a[i])
    j = rng.randrange(len(spec.domains))
    dom = spec.domains[j][0]
    pos = nb + j
    span = (min(dom), max(dom)) if dom else (0, 0)
    c = rng.randint(span[0] - 1, span[1] + 1)
    if kind == "is":
        return (lambda h: h.ints[j].is_(c)), (lambda a: a[pos] == c)
    if kind == "eqc":
        return (lambda h: h.ints[j] == c), (lambda a: a[pos] == c)
    if not dom:
        return (lambda h: h.ints[j].is_(c)), (lambda a: a[pos] == c)
    if list(dom) != sorted(dom):
        spec.features.add("unsorted_order")
    if len(set(dom)) != len(dom):
        spec.features.add("dup_domain")
    if kind == "ge":
        return (lambda h: h.ints[j].ge(c)), (lambda a: a[pos] >= c)
    return (lambda h: h.ints[j].le(c)), (lambda a: a[pos] <= c)


def _raw(x):
    """Tuple trees take ints and tuples, not BoolVar."""
    return x.lit if hasattr(x, "lit") else x


def make_expr(rng: random.Random, spec: Spec, depth: int, traps: bool):
    """An expression tree: (render(h), holds(a))."""
    roll = rng.random()
    if depth <= 0 or roll < 0.25:
        leaf = rng.random()
        nints = len(spec.domains)
        if nints >= 2 and leaf < 0.2:
            j, k = rng.randrange(nints), rng.randrange(nints)
            pj, pk = spec.nbools + j, spec.nbools + k
            if rng.random() < 0.5:
                return (lambda h: h.ints[j] == h.ints[k]), (lambda a: a[pj] == a[pk])
            return (lambda h: h.ints[j] != h.ints[k]), (lambda a: a[pj] != a[pk])
        if nints and leaf < 0.35:
            j = rng.randrange(nints)
            pos = spec.nbools + j
            dom = spec.domains[j][0]
            c = rng.randint(min(dom) - 1, max(dom) + 1) if dom else 0
            return (lambda h: h.ints[j] != c), (lambda a: a[pos] != c)
        if nints and leaf < 0.5:
            j = rng.randrange(nints)
            pos = spec.nbools + j
            dom = spec.domains[j][0]
            vals = {rng.randint(-3, 7) for _ in range(rng.randint(0, 3))}
            if dom and rng.random() < 0.7:
                vals.add(rng.choice(dom))
            return (lambda h: h.ints[j].in_(vals)), (lambda a: a[pos] in vals)
        atom = make_atom(rng, spec)
        if atom is not None:
            return atom
        # nothing to refer to at all: a constant tree
        if rng.random() < 0.5:
            return (lambda h: ("and",)), (lambda a: True)
        return (lambda h: ("or",)), (lambda a: False)

    left = make_expr(rng, spec, depth - 1, traps)
    right = make_expr(rng, spec, depth - 1, traps)
    lr, lh = left
    rr, rh = right

    if traps and spec.nbools and rng.random() < 0.15:
        # `_as_expr` passes a Python bool through on purpose
        i = rng.randrange(spec.nbools)
        c = rng.random() < 0.5
        spec.features.add("bool_const")
        if rng.random() < 0.5:
            return (lambda h: h.bools[i] | c), (lambda a: a[i] or c)
        return (lambda h: h.bools[i] & c), (lambda a: a[i] and c)

    if spec.nbools and rng.random() < 0.5:
        # the operator surface: the left operand must be a BoolVar
        i = rng.randrange(spec.nbools)
        negated = rng.random() < 0.3
        base = (lambda h: ~h.bools[i]) if negated else (lambda h: h.bools[i])
        bh = (lambda a: not a[i]) if negated else (lambda a: a[i])
        op = rng.choice(("and", "or", "xor", "imp", "iff"))
        if op == "and":
            return (lambda h: base(h) & rr(h)), (lambda a: bh(a) and rh(a))
        if op == "or":
            return (lambda h: base(h) | rr(h)), (lambda a: bh(a) or rh(a))
        if op == "xor":
            return (lambda h: base(h) ^ rr(h)), (lambda a: bool(bh(a)) != bool(rh(a)))
        if op == "imp":
            return (lambda h: base(h) >> rr(h)), (lambda a: (not bh(a)) or rh(a))
        return (lambda h: base(h).iff(rr(h))), (lambda a: bool(bh(a)) == bool(rh(a)))

    # raw tuple trees, which is what examples/zebra.py writes
    op = rng.choice(("and", "or", "not", "xor", "imp", "iff", "ite", "and3", "or3"))
    if op == "not":
        return (lambda h: ("not", _raw(lr(h)))), (lambda a: not lh(a))
    if op == "and":
        return (lambda h: ("and", _raw(lr(h)), _raw(rr(h)))), (lambda a: lh(a) and rh(a))
    if op == "or":
        return (lambda h: ("or", _raw(lr(h)), _raw(rr(h)))), (lambda a: lh(a) or rh(a))
    if op == "xor":
        return (lambda h: ("xor", _raw(lr(h)), _raw(rr(h)))), (lambda a: bool(lh(a)) != bool(rh(a)))
    if op == "imp":
        return (lambda h: ("imp", _raw(lr(h)), _raw(rr(h)))), (lambda a: (not lh(a)) or rh(a))
    if op == "iff":
        return (lambda h: ("iff", _raw(lr(h)), _raw(rr(h)))), (lambda a: bool(lh(a)) == bool(rh(a)))
    third = make_expr(rng, spec, depth - 1, traps)
    tr, th = third
    if op == "ite":
        return (lambda h: ("ite", _raw(lr(h)), _raw(rr(h)), _raw(tr(h)))), \
               (lambda a: rh(a) if lh(a) else th(a))
    if op == "and3":
        return (lambda h: ("and", _raw(lr(h)), _raw(rr(h)), _raw(tr(h)))), \
               (lambda a: lh(a) and rh(a) and th(a))
    return (lambda h: ("or", _raw(lr(h)), _raw(rr(h)), _raw(tr(h)))), \
           (lambda a: lh(a) or rh(a) or th(a))


def make_items(rng: random.Random, spec: Spec, lo=0, hi=5):
    """A multiset of literals, duplicates and complements included on purpose."""
    n = rng.randint(lo, hi)
    items = [make_atom(rng, spec) for _ in range(n)]
    items = [x for x in items if x is not None]
    if items and rng.random() < 0.2:
        items.append(rng.choice(items))
    renders = [r for r, _ in items]
    holds = [h for _, h in items]
    return renders, holds


def make_constraint(rng: random.Random, spec: Spec, traps: bool):
    kind = rng.choice((
        "add", "add", "add", "clause", "alldiff", "perm", "amo", "exactly_one",
        "amk", "alk", "exk", "sum_leq", "sum_geq", "parity",
    ))
    nints = len(spec.domains)

    if kind == "add":
        render, holds = make_expr(rng, spec, rng.randint(0, 3), traps)
        def build(m, h, render=render):
            m.add(render(h))
        return build, holds, "c_add"

    if kind == "clause":
        renders, hs = make_items(rng, spec, 0, 4)
        def build(m, h, renders=renders):
            m.add_clause([r(h) for r in renders])
        return build, (lambda a: any(x(a) for x in hs)), "c_add_clause"

    if kind in ("alldiff", "perm") and nints:
        chosen = [rng.randrange(nints) for _ in range(rng.randint(1, nints + 1))]
        if rng.random() < 0.8:
            chosen = list(dict.fromkeys(chosen))
        poss = [spec.nbools + j for j in chosen]
        def holds(a, poss=poss):
            vals = [a[p] for p in poss]
            return len(vals) == len(set(vals))
        if kind == "alldiff":
            def build(m, h, chosen=chosen):
                m.all_different([h.ints[j] for j in chosen])
            return build, holds, "c_all_different"
        def build(m, h, chosen=chosen):
            m.all_different_permutation([h.ints[j] for j in chosen])
        return build, holds, "c_all_different_permutation"

    if kind == "amo":
        renders, hs = make_items(rng, spec, 0, 8)
        method = rng.choice(AMO_METHODS)
        if method == "totalizer" and not renders:
            spec.features.add("empty_totalizer")
        def build(m, h, renders=renders, method=method):
            m.at_most_one([r(h) for r in renders], method=method)
        return build, (lambda a: sum(bool(x(a)) for x in hs) <= 1), f"c_at_most_one_{method}"

    if kind == "exactly_one":
        renders, hs = make_items(rng, spec, 0, 8)
        method = rng.choice(AMO_METHODS)
        if method == "totalizer" and not renders:
            spec.features.add("empty_totalizer")
        def build(m, h, renders=renders, method=method):
            m.exactly_one([r(h) for r in renders], method=method)
        return build, (lambda a: sum(bool(x(a)) for x in hs) == 1), f"c_exactly_one_{method}"

    if kind in ("amk", "alk", "exk"):
        renders, hs = make_items(rng, spec, 0, 7)
        n = len(renders)
        k = rng.randint(0, n + 1)
        if traps and rng.random() < 0.3:
            k = rng.randint(-2, -1)
        method = rng.choice(AMK_METHODS)
        if k < 0 and kind in ("amk", "exk"):
            spec.features.add("negative_k")
        if kind == "amk":
            def build(m, h, renders=renders, k=k, method=method):
                m.at_most_k([r(h) for r in renders], k, method=method)
            return build, (lambda a: sum(bool(x(a)) for x in hs) <= k), f"c_at_most_k_{method}"
        if kind == "alk":
            def build(m, h, renders=renders, k=k, method=method):
                m.at_least_k([r(h) for r in renders], k, method=method)
            return build, (lambda a: sum(bool(x(a)) for x in hs) >= k), f"c_at_least_k_{method}"
        def build(m, h, renders=renders, k=k, method=method):
            m.exactly_k([r(h) for r in renders], k, method=method)
        return build, (lambda a: sum(bool(x(a)) for x in hs) == k), f"c_exactly_k_{method}"

    if kind in ("sum_leq", "sum_geq"):
        renders, hs = make_items(rng, spec, 0, 6)
        weights = [rng.randint(-4, 7) for _ in renders]
        low = sum(w for w in weights if w < 0)
        high = sum(w for w in weights if w > 0)
        bound = rng.randint(low - 2, high + 2)
        def total(a, hs=hs, weights=weights):
            return sum(w for w, x in zip(weights, hs) if x(a))
        if kind == "sum_leq":
            def build(m, h, renders=renders, weights=weights, bound=bound):
                m.sum_leq(weights, [r(h) for r in renders], bound)
            return build, (lambda a: total(a) <= bound), "c_sum_leq"
        def build(m, h, renders=renders, weights=weights, bound=bound):
            m.sum_geq(weights, [r(h) for r in renders], bound)
        return build, (lambda a: total(a) >= bound), "c_sum_geq"

    # parity, and the fallback when there are no ints for all_different
    renders, hs = make_items(rng, spec, 0, 6)
    odd = rng.random() < 0.5
    def build(m, h, renders=renders, odd=odd):
        m.parity([r(h) for r in renders], odd=odd)
    return build, (lambda a: (sum(bool(x(a)) for x in hs) % 2 == 1) == odd), \
        ("c_parity_odd" if odd else "c_parity_even")


def make_spec(rng: random.Random, trap_rate: float = 0.12) -> Spec:
    spec = Spec()
    traps = rng.random() < trap_rate
    spec.nbools = rng.randint(0, 5)
    for _ in range(rng.randint(0 if spec.nbools else 1, 3)):
        lo = rng.randint(-3, 4)
        dom = rng.sample(range(lo, lo + 6), rng.randint(1, 4))
        dom.sort()
        if rng.random() < 0.15:
            dom = list(range(lo, lo + len(dom)))
        if rng.random() < 0.02:
            dom = []
        order = rng.random() < 0.2 and bool(dom)
        if traps and dom and rng.random() < 0.4:
            rng.shuffle(dom)
            if dom != sorted(dom):
                order = True
        if traps and dom and rng.random() < 0.15:
            dom = dom + [dom[0]]
            spec.features.add("dup_domain")
        spec.domains.append((dom, order))

    # keep direct enumeration cheap
    while True:
        size = 2 ** spec.nbools
        for d, _ in spec.domains:
            size *= max(1, len(set(d)))
        if size <= 400:
            break
        if spec.nbools > 1:
            spec.nbools -= 1
        else:
            spec.domains.pop()

    for d, o in spec.domains:
        if o and d != sorted(d):
            spec.features.add("unsorted_order")

    for _ in range(rng.randint(0, 5)):
        spec.constraints.append(make_constraint(rng, spec, traps))
    spec.split = rng.randint(0, len(spec.constraints))
    return spec


def cnf_dimacs(cnf: CNF):
    return [[to_dimacs(l) for l in c] for c in cnf.clauses]


def bits_satisfy(cnf: CNF, bits) -> bool:
    return all(any(bits[l >> 1] != bool(l & 1) for l in c) for c in cnf.clauses)


def user_units(spec: Spec, h, a):
    """DIMACS units saying the user's variables take assignment `a`."""
    out = []
    for i, b in enumerate(h.bools):
        d = to_dimacs(b.lit)
        out.append(d if a[i] else -d)
    for j, x in enumerate(h.ints):
        val = a[spec.nbools + j]
        for v, l in zip(x.domain, x.lits):
            d = to_dimacs(l)
            out.append(d if v == val else -d)
    return out


def read_checked(spec: Spec, h, sol, t: Tally, where: str):
    """Read a Solution, and require each integer to be exactly one-hot."""
    for x in h.ints:
        hot = [v for v, l in zip(x.domain, x.lits) if sol[l]]
        if len(hot) != 1:
            t.bad("not_one_hot", f"{where}: {x} has {hot}", spec.features)
    return h.read(sol)


def describe(spec: Spec) -> str:
    return (f"nbools={spec.nbools} domains={spec.domains} "
            f"kinds={[k for _, _, k in spec.constraints]} features={sorted(spec.features)}")


def check_model(spec: Spec, rng: random.Random, t: Tally, impl=Model, use_native=True) -> None:
    truth = spec.solutions()
    t.counts["model_instances"] += 1
    t.counts["model_sat" if truth else "model_unsat"] += 1
    for _, _, kind in spec.constraints:
        t.counts[kind] += 1
    if spec.nbools:
        t.counts["var_bool"] += 1
    if spec.domains:
        t.counts["var_int"] += 1
    if any(o for _, o in spec.domains):
        t.counts["var_int_order"] += 1
    feats = spec.features
    d = describe(spec)

    # A. solve()
    method = rng.choice(OVERRIDES)
    m, h = build_all(spec, impl, method)
    if method:
        t.counts[f"override_{method}"] += 1
    sol = m.solve()
    t.step("check_solve")
    if (sol is not None) != bool(truth):
        t.bad("solve_verdict", f"solve()={'SAT' if sol else 'UNSAT'} truth has "
                               f"{len(truth)} solutions: {d}", feats)
    if sol is not None and truth:
        got = read_checked(spec, h, sol, t, "solve")
        if got not in truth:
            t.bad("solve_model", f"solve() gave {got}, not a solution: {d}", feats)
        if not bits_satisfy(m.cnf, sol.bits):
            t.bad("solve_bits", f"solve() bits violate its own CNF: {d}", feats)

    # repeated solve() on an unchanged model must keep its answer
    again = m.solve()
    t.step("check_resolve_unchanged")
    if (again is not None) != (sol is not None):
        t.bad("resolve_verdict", f"second solve() changed verdict: {d}", feats)

    # B. solutions(project=...)
    m, h = build_all(spec, impl)
    sols = [read_checked(spec, h, s, t, "solutions") for s in m.solutions(project=h.all_vars())]
    t.step("check_solutions_set")
    if set(sols) != truth:
        t.bad("solutions_set",
              f"solutions()={sorted(set(sols), key=repr)[:8]} truth={sorted(truth, key=repr)[:8]}: {d}",
              feats)
    if len(sols) != len(set(sols)):
        t.bad("solutions_duplicates", f"projected solutions() repeated one: {d}", feats)
    if len(truth) >= 2:
        t.counts["model_multi_solution"] += 1
        limit = rng.randint(1, len(truth) - 1)
        m, h = build_all(spec, impl)
        limited = [h.read(s) for s in m.solutions(project=h.all_vars(), limit=limit)]
        t.step("check_solutions_limit")
        if len(limited) != limit or not set(limited) <= truth:
            t.bad("solutions_limit", f"limit={limit} gave {limited}: {d}", feats)

    # C. unprojected solutions must cover the same user-level set
    if rng.random() < 0.25:
        m, h = build_all(spec, impl)
        seen = []
        for s in m.solutions(limit=2000):
            seen.append(h.read(s))
        t.step("check_solutions_unprojected")
        if len(seen) < 2000 and set(seen) != truth:
            t.bad("solutions_unprojected", f"{sorted(set(seen), key=repr)[:8]} vs "
                                           f"{sorted(truth, key=repr)[:8]}: {d}", feats)
        if len(seen) != len(set(seen)):
            t.counts["note_unprojected_duplicates"] += 1

    # D. an UNSAT answer carries a proof, and the proof replays
    if not truth:
        m, h = build_all(spec, impl)
        proof = MemoryProof()
        res = m.solve(proof=proof)
        t.step("check_unsat_proof")
        if res is not None:
            t.bad("proof_verdict", f"solve(proof=...) said SAT on an UNSAT model: {d}", feats)
        else:
            for engine in ("python", "native") if use_native else ("python",):
                chk = check_proof(m.cnf, proof.steps, engine=engine)
                t.counts[f"unsat_proof_{engine}"] += 1
                if not chk.ok:
                    t.bad("proof_rejected", f"{engine}: {chk.reason}: {d}", feats)

    # E. the Rust engine on the same CNF
    if use_native:
        m, h = build_all(spec, impl)
        py = Solver(m.cnf.nvars)
        ok = py.add_cnf(m.cnf)
        py_res = py.solve() if ok else False
        from cdclkit import native
        ns = native.require().Solver(m.cnf.nvars)
        nok = all([ns.add_clause(list(c)) for c in m.cnf.clauses])
        n_res = ns.solve() if nok else False
        t.step("check_native_cnf")
        if bool(py_res) != bool(n_res) or (py_res and list(ns.model) != list(py.model)) \
                or py.stats.conflicts != ns.conflicts:
            t.bad("native_cnf", f"python={py_res}/{py.stats.conflicts} "
                                f"native={n_res}/{ns.conflicts}: {d}", feats)

    # F. the CNF itself, judged by DPLL with its auxiliary variables
    m, h = build_all(spec, impl)
    dim = cnf_dimacs(m.cnf)
    t.counts["max_cnf_vars"] = max(t.counts["max_cnf_vars"], m.cnf.nvars)
    if m.cnf.nvars > 16:
        t.counts["cnf_past_16_vars"] += 1
    if "dup_domain" not in feats:
        everything = list(spec.assignments())
        sample = everything if len(everything) <= 32 else rng.sample(everything, 32)
        for a in sample:
            want = a in truth
            got = dpll.satisfiable(dim + [[u] for u in user_units(spec, h, a)])
            t.step("check_dpll_assignment")
            if got != want:
                t.bad("dpll_assignment", f"CNF says {got} for {a}, truth {want}: {d}", feats)
        # no integer can be two values, or none
        for x in h.ints:
            lits = [to_dimacs(l) for l in x.lits]
            if not lits:
                continue
            t.step("check_dpll_one_hot")
            if dpll.satisfiable(dim + [[-l] for l in lits]):
                t.bad("dpll_no_value", f"{x} can take no value: {d}", feats)
            if len(lits) >= 2:
                i, j = rng.sample(range(len(lits)), 2)
                if dpll.satisfiable(dim + [[lits[i]], [lits[j]]]):
                    t.bad("dpll_two_values", f"{x} can take two values: {d}", feats)

    # G. assumptions, and that they are retracted afterwards
    atoms = []
    for i in range(spec.nbools):
        atoms.append((lambda h, i=i: h.bools[i].lit, lambda a, i=i: a[i]))
        atoms.append((lambda h, i=i: neg(h.bools[i].lit), lambda a, i=i: not a[i]))
    for j, (dom, _) in enumerate(spec.domains):
        for v in dom:
            pos = spec.nbools + j
            atoms.append((lambda h, j=j, v=v: h.ints[j].is_(v), lambda a, pos=pos, v=v: a[pos] == v))
    if atoms and "dup_domain" not in feats:
        chosen = rng.sample(atoms, min(len(atoms), rng.randint(1, 2)))
        m, h = build_all(spec, impl)
        lits = [r(h) for r, _ in chosen]
        expect = {a for a in truth if all(x(a) for _, x in chosen)}
        sol = m.solve(assumptions=lits)
        t.step("check_assumptions")
        t.counts["assumption_sat" if expect else "assumption_unsat"] += 1
        if (sol is not None) != bool(expect):
            t.bad("assumption_verdict", f"under {lits}: {'SAT' if sol else 'UNSAT'}, "
                                        f"expected {len(expect)}: {d}", feats)
        elif sol is not None and h.read(sol) not in expect:
            t.bad("assumption_model", f"under {lits}: {h.read(sol)}: {d}", feats)
        after = m.solve()
        t.step("check_assumptions_retracted")
        if (after is not None) != bool(truth):
            t.bad("assumption_retract", f"after assumptions, solve() "
                                        f"{'SAT' if after else 'UNSAT'}: {d}", feats)

    # H. differential_solve must not disagree, and must return a real answer
    if rng.random() < 0.35:
        methods = rng.choice(DIFF_METHODS)
        captured = []
        def build(mm):
            hh = Handles(spec, mm)
            for b, _, _ in spec.constraints:
                b(mm, hh)
            captured.append(hh)
        t.step("check_differential")
        a_m, _ = build_all(spec, impl, methods[0])
        b_m, _ = build_all(spec, impl, methods[1])
        t.counts["note_differential_same_cnf" if a_m.cnf.clauses == b_m.cnf.clauses
                 else "differential_varied_cnf"] += 1
        try:
            sol = differential_solve(build, methods=methods)
        except EncodingDisagreement as e:
            t.bad("differential_disagree", f"{methods}: {e}: {d}", feats)
        else:
            if (sol is not None) != bool(truth):
                t.bad("differential_verdict", f"{methods}: {'SAT' if sol else 'UNSAT'}: {d}", feats)
            elif sol is not None and captured[0].read(sol) not in truth:
                t.bad("differential_model", f"{methods}: {captured[0].read(sol)}: {d}", feats)

    # I. the optimum, through the one optimisation API there is
    if atoms and "dup_domain" not in feats and rng.random() < 0.35:
        soft = rng.sample(atoms, min(len(atoms), rng.randint(1, 5)))
        minimise = rng.random() < 0.5
        assumption_based = rng.random() < 0.5
        m, h = build_all(spec, impl)
        s = m.build_solver()
        lits = [r(h) for r, _ in soft]
        res = optimise(s, lits, minimise=minimise, assumption_based=assumption_based)
        t.step("check_optimum")
        scores = [sum(bool(x(a)) for _, x in soft) for a in truth]
        want = (min(scores) if minimise else max(scores)) if scores else None
        t.counts["optimum_exists" if scores else "optimum_infeasible"] += 1
        if (res is None) != (want is None):
            t.bad("optimum_verdict", f"optimise={res} want={want}: {d}", feats)
        elif res is not None:
            if res[0] != want:
                t.bad("optimum_value", f"optimise={res[0]} want={want} "
                                       f"minimise={minimise} assumption={assumption_based}: {d}", feats)
            achieved = sum(res[1][l >> 1] != bool(l & 1) for l in lits)
            if achieved != res[0]:
                t.bad("optimum_model", f"claims {res[0]}, its model scores {achieved}: {d}", feats)
            if not bits_satisfy(m.cnf, res[1]):
                t.bad("optimum_bits", f"optimum model violates the CNF: {d}", feats)

    # J. a weighted optimum, by bounding with sum_leq on fresh models
    if atoms and truth and "dup_domain" not in feats and rng.random() < 0.15:
        soft = rng.sample(atoms, min(len(atoms), rng.randint(1, 4)))
        weights = [rng.randint(-3, 5) for _ in soft]
        scores = [sum(w for w, (_, x) in zip(weights, soft) if x(a)) for a in truth]
        best = min(scores)
        for bound, want_sat in ((best, True), (best - 1, False)):
            m, h = build_all(spec, impl)
            m.sum_leq(weights, [r(h) for r, _ in soft], bound)
            s = m.solve()
            t.step("check_weighted_optimum")
            if (s is not None) != want_sat:
                t.bad("weighted_optimum", f"sum_leq bound={bound} (best {best}) "
                                          f"gave {'SAT' if s else 'UNSAT'}: {d}", feats)

    # K. constraints added after a first solve(), which `solve` advertises by
    # rebuilding "when there are new constraints since the last build"
    if spec.constraints and rng.random() < 0.3:
        fs = feats | {"incremental"}
        m = impl()
        h = Handles(spec, m)
        for b, _, _ in spec.constraints[:spec.split]:
            b(m, h)
        m.solve()
        nvars_before = m.cnf.nvars
        for b, _, _ in spec.constraints[spec.split:]:
            b(m, h)
        t.counts["incremental_same_vars" if m.cnf.nvars == nvars_before
                 else "incremental_new_vars"] += 1
        sol = m.solve()
        t.step("check_incremental")
        if (sol is not None) != bool(truth):
            t.bad("incremental_verdict", f"{'SAT' if sol else 'UNSAT'} after adding "
                                         f"constraints, truth {len(truth)}: {d}", fs)
        elif sol is not None and h.read(sol) not in truth:
            t.bad("incremental_model", f"{h.read(sol)} violates a constraint added "
                                       f"after the first solve(): {d}", fs)

    # L. solve() after enumerating solutions must still see the same problem
    if truth and rng.random() < 0.2:
        fs = feats | {"sols_then_solve"}
        m, h = build_all(spec, impl)
        list(m.solutions(project=h.all_vars()))
        sol = m.solve()
        t.step("check_solve_after_solutions")
        if sol is None or h.read(sol) not in truth:
            t.bad("solve_after_solutions", f"solutions() then solve() gave "
                                           f"{'UNSAT' if sol is None else h.read(sol)} on a "
                                           f"problem with {len(truth)} solutions: {d}", fs)


def guarded_check_model(spec, rng, t, impl=Model, use_native=True):
    try:
        check_model(spec, rng, t, impl, use_native)
    except RecursionError:
        t.bad("model_crash", f"RecursionError: {describe(spec)}", spec.features)
    except Exception as e:  # any crash on valid input is a finding, never a pass
        t.bad("model_crash", f"{type(e).__name__}: {e}: {describe(spec)}", spec.features)


# ==========================================================================
# Part 2: pyeq
# ==========================================================================
#
# Expressions and statements are tuples. render_* turns them into source that
# pyeq reads through inspect; Eval runs them at a fixed width. Neither shares
# anything with cdclkit.pyeq.

CMP_OPS = ("==", "!=", "<", "<=", ">", ">=")
BIN_OPS = ("+", "-", "*", "&", "|", "^")


def render_expr(e) -> str:
    tag = e[0]
    if tag == "var":
        return e[1]
    if tag == "const":
        return str(e[1]) if e[1] >= 0 else f"(-{-e[1]})"
    if tag == "bool":
        return "True" if e[1] else "False"
    if tag == "bin":
        return f"({render_expr(e[2])} {e[1]} {render_expr(e[3])})"
    if tag == "shift":
        return f"({render_expr(e[2])} {e[1]} {e[3]})"
    if tag == "fdiv":
        return f"({render_expr(e[1])} // {1 << e[2]})"
    if tag == "mod":
        return f"({render_expr(e[1])} % {1 << e[2]})"
    if tag == "un":
        return f"({e[1]}{render_expr(e[2])})"
    if tag == "cmp":
        return f"({render_expr(e[2])} {e[1]} {render_expr(e[3])})"
    if tag == "not":
        return f"(not {render_expr(e[1])})"
    if tag == "boolop":
        return "(" + f" {e[1]} ".join(render_expr(x) for x in e[2]) + ")"
    if tag == "ifexp":
        return f"({render_expr(e[2])} if {render_expr(e[1])} else {render_expr(e[3])})"
    raise AssertionError(tag)


def render_block(body, indent) -> list[str]:
    pad = " " * indent
    out = []
    for s in body:
        tag = s[0]
        if tag == "assign":
            out.append(f"{pad}{s[1]} = {render_expr(s[2])}")
        elif tag == "aug":
            out.append(f"{pad}{s[1]} {s[2]}= {render_expr(s[3])}")
        elif tag == "pass":
            out.append(f"{pad}pass")
        elif tag == "doc":
            out.append(f'{pad}"""a docstring"""')
        elif tag == "return":
            out.append(f"{pad}return {render_expr(s[1])}")
        elif tag == "if":
            out.append(f"{pad}if {render_expr(s[1])}:")
            out += render_block(s[2] or [("pass",)], indent + 4)
            if s[3]:
                out.append(f"{pad}else:")
                out += render_block(s[3], indent + 4)
        elif tag == "for":
            args = ", ".join(str(a) for a in s[2])
            out.append(f"{pad}for {s[1]} in range({args}):")
            out += render_block(s[3] or [("pass",)], indent + 4)
        else:
            raise AssertionError(tag)
    return out


def render_function(name, params, body) -> str:
    return "\n".join([f"def {name}({', '.join(params)}):"] + render_block(body, 4)) + "\n"


class _Return(Exception):
    def __init__(self, value) -> None:
        self.value = value


class Eval:
    """Fixed-width two's complement, wrapping after every operation.

    `overflowed` records whether wrapping ever changed a value. When it did
    not, the result must equal real Python's, and the harness checks that.
    """

    def __init__(self, width: int) -> None:
        self.width = width
        self.mod = 1 << width
        self.half = 1 << (width - 1)
        self.overflowed = False

    def wrap(self, v: int) -> int:
        u = int(v) % self.mod
        s = u - self.mod if u >= self.half else u
        if s != v:
            self.overflowed = True
        return s

    def value(self, e, env) -> int:
        tag = e[0]
        if tag == "var":
            return env[e[1]]
        if tag == "const":
            return self.wrap(e[1])
        if tag == "bool":
            return self.wrap(1 if e[1] else 0)
        if tag == "bin":
            a, b = self.value(e[2], env), self.value(e[3], env)
            op = e[1]
            r = (a + b if op == "+" else a - b if op == "-" else a * b if op == "*"
                 else a & b if op == "&" else a | b if op == "|" else a ^ b)
            return self.wrap(r)
        if tag == "shift":
            a = self.value(e[2], env)
            return self.wrap(a << e[3] if e[1] == "<<" else a >> e[3])
        if tag == "fdiv":
            return self.wrap(self.value(e[1], env) // (1 << e[2]))
        if tag == "mod":
            return self.wrap(self.value(e[1], env) % (1 << e[2]))
        if tag == "un":
            a = self.value(e[2], env)
            return self.wrap(-a if e[1] == "-" else a if e[1] == "+" else ~a)
        if tag in ("cmp", "not"):
            return self.wrap(1 if self.truth(e, env) else 0)
        if tag == "boolop":
            # Python's own rule: the operand that decided it, not a bool.
            v = 0
            for x in e[2]:
                v = self.value(x, env)
                if (v != 0) == (e[1] == "or"):
                    return v
            return v
        if tag == "ifexp":
            return self.value(e[2] if self.truth(e[1], env) else e[3], env)
        raise AssertionError(tag)

    def truth(self, e, env) -> bool:
        tag = e[0]
        if tag == "cmp":
            a, b = self.value(e[2], env), self.value(e[3], env)
            op = e[1]
            return (a == b if op == "==" else a != b if op == "!=" else a < b if op == "<"
                    else a <= b if op == "<=" else a > b if op == ">" else a >= b)
        if tag == "not":
            return not self.truth(e[1], env)
        if tag == "boolop":
            if e[1] == "and":
                return all(self.truth(x, env) for x in e[2])
            return any(self.truth(x, env) for x in e[2])
        if tag == "bool":
            return e[1]
        return self.value(e, env) != 0

    def block(self, body, env) -> None:
        for s in body:
            tag = s[0]
            if tag == "assign":
                env[s[1]] = self.value(s[2], env)
            elif tag == "aug":
                op = s[2]
                if op in ("<<", ">>"):
                    expr = ("shift", op, ("var", s[1]), s[3][1])
                elif op == "//":
                    expr = ("fdiv", ("var", s[1]), s[3][1].bit_length() - 1)
                elif op == "%":
                    expr = ("mod", ("var", s[1]), s[3][1].bit_length() - 1)
                else:
                    expr = ("bin", op, ("var", s[1]), s[3])
                env[s[1]] = self.value(expr, env)
            elif tag in ("pass", "doc"):
                pass
            elif tag == "return":
                raise _Return(self.value(s[1], env))
            elif tag == "if":
                self.block(s[2] if self.truth(s[1], env) else s[3], env)
            elif tag == "for":
                for i in range(*s[2]):
                    env[s[1]] = self.wrap(i)
                    self.block(s[3], env)
            else:
                raise AssertionError(tag)

    def run(self, body, inputs) -> int:
        env = dict(inputs)
        try:
            self.block(body, env)
        except _Return as r:
            return r.value
        raise AssertionError("generated body fell off the end")


class ProgramGen:
    def __init__(self, rng: random.Random, params, width: int, traps: bool) -> None:
        self.rng = rng
        self.params = params
        self.width = width
        self.traps = traps

    def const(self):
        rng = self.rng
        roll = rng.random()
        if roll < 0.6:
            return rng.randint(-3, 7)
        if roll < 0.8:
            return rng.randint(-(1 << (self.width - 1)), (1 << self.width))
        return rng.choice((0, 1, -1, 1 << (self.width - 1), (1 << self.width) - 1, 1 << self.width))

    def value(self, names, depth):
        rng = self.rng
        if depth <= 0 or rng.random() < 0.2:
            roll = rng.random()
            if roll < 0.7 and names:
                return ("var", rng.choice(names))
            if roll < 0.75:
                return ("bool", rng.random() < 0.5)
            return ("const", self.const())
        roll = rng.random()
        if roll < 0.45:
            return ("bin", rng.choice(BIN_OPS), self.value(names, depth - 1), self.value(names, depth - 1))
        if roll < 0.55:
            return ("shift", rng.choice(("<<", ">>")), self.value(names, depth - 1),
                    rng.randint(0, self.width + 1))
        if roll < 0.62:
            return ("fdiv", self.value(names, depth - 1), rng.randint(0, self.width + 1))
        if roll < 0.69:
            return ("mod", self.value(names, depth - 1), rng.randint(0, self.width + 1))
        if roll < 0.77:
            return ("un", rng.choice("-+~"), self.value(names, depth - 1))
        if roll < 0.84:
            return ("cmp", rng.choice(CMP_OPS), self.value(names, depth - 1), self.value(names, depth - 1))
        if roll < 0.88:
            return ("not", self.test(names, depth - 1))
        if self.traps and roll < 0.94:
            # `x and y` in a value position, which Python defines as an operand
            return ("boolop", rng.choice(("and", "or")),
                    [self.value(names, depth - 1) for _ in range(rng.randint(2, 3))])
        return ("ifexp", self.test(names, depth - 1), self.value(names, depth - 1),
                self.value(names, depth - 1))

    def test(self, names, depth):
        rng = self.rng
        roll = rng.random()
        if depth <= 0 or roll < 0.5:
            return ("cmp", rng.choice(CMP_OPS), self.value(names, depth - 1), self.value(names, depth - 1))
        if roll < 0.7:
            return ("boolop", rng.choice(("and", "or")),
                    [self.test(names, depth - 1) for _ in range(rng.randint(2, 3))])
        if roll < 0.8:
            return ("not", self.test(names, depth - 1))
        if roll < 0.85:
            return ("bool", rng.random() < 0.5)
        return self.value(names, depth - 1)

    def block(self, names, depth, stmts, must_return):
        """Returns (statements, names defined afterwards)."""
        rng = self.rng
        names = list(names)
        out = []
        for _ in range(rng.randint(0, stmts)):
            roll = rng.random()
            if roll < 0.4:
                target = rng.choice(names) if names and rng.random() < 0.4 else f"t{rng.randint(0, 2)}"
                out.append(("assign", target, self.value(names, 2)))
                if target not in names:
                    names.append(target)
            elif roll < 0.55 and names:
                target = rng.choice(names)
                op = rng.choice(("+", "-", "*", "&", "|", "^", "<<", ">>", "//", "%"))
                if op in ("<<", ">>"):
                    arg = ("const", rng.randint(0, self.width))
                elif op in ("//", "%"):
                    arg = ("const", 1 << rng.randint(0, self.width))
                else:
                    arg = self.value(names, 1)
                out.append(("aug", target, op, arg))
            elif roll < 0.8 and depth > 0:
                cond = self.test(names, 2)
                then, then_names = self.block(names, depth - 1, 2, rng.random() < 0.3)
                other, other_names = self.block(names, depth - 1, 2, rng.random() < 0.3)
                out.append(("if", cond, then, other))
                names = [n for n in then_names if n in other_names]
            elif roll < 0.92 and depth > 0:
                # now and then the loop rebinds a parameter or an existing name
                var = rng.choice(names) if names and rng.random() < 0.1 else f"i{rng.randint(0, 1)}"
                shape = rng.random()
                if shape < 0.6:
                    args = (rng.randint(0, 3),)
                elif shape < 0.85:
                    a = rng.randint(0, 3)
                    args = (a, a + rng.randint(0, 3))
                else:
                    a = rng.randint(0, 3)
                    args = (a, a + rng.randint(1, 5), rng.randint(1, 2))
                count = len(range(*args))
                inner = names + ([var] if count and var not in names else [])
                body, body_names = self.block(inner, depth - 1, 2, rng.random() < 0.15)
                out.append(("for", var, args, body))
                # only an executed loop defines anything
                if count:
                    names = [n for n in body_names]
            elif roll < 0.96:
                out.append(("pass",))
            else:
                out.append(("doc",))
        if must_return:
            out.append(("return", self.value(names, 2)))
        return out, names

    def function(self):
        depth = self.rng.randint(0, 2)
        body, _ = self.block(self.params, depth, 4, True)
        return body


def rewrite_expr(rng, e, width):
    """A rewrite that holds at every width; the oracle decides regardless."""
    tag = e[0]
    if tag == "bin":
        a = rewrite_expr(rng, e[2], width)
        b = rewrite_expr(rng, e[3], width)
        op = e[1]
        roll = rng.random()
        if roll < 0.3 and op in "+*&|^":
            return ("bin", op, b, a)
        if roll < 0.5:
            if op == "-":
                return ("bin", "+", a, ("un", "-", b))
            if op == "+":
                return ("bin", "-", a, ("un", "-", b))
            if op == "^":
                return ("bin", "-", ("bin", "|", a, b), ("bin", "&", a, b))
            if op == "|":
                return ("un", "~", ("bin", "&", ("un", "~", a), ("un", "~", b)))
            if op == "&":
                return ("un", "~", ("bin", "|", ("un", "~", a), ("un", "~", b)))
        if roll < 0.6 and op == "+":
            return ("bin", "+", ("bin", "^", a, b), ("shift", "<<", ("bin", "&", a, b), 1))
        return ("bin", op, a, b)
    if tag == "shift":
        a = rewrite_expr(rng, e[2], width)
        if e[1] == "<<" and rng.random() < 0.5:
            return ("bin", "*", a, ("const", 1 << e[3]))
        return ("shift", e[1], a, e[3])
    if tag == "fdiv":
        a = rewrite_expr(rng, e[1], width)
        return ("shift", ">>", a, e[2]) if rng.random() < 0.5 else ("fdiv", a, e[2])
    if tag == "mod":
        a = rewrite_expr(rng, e[1], width)
        if rng.random() < 0.5:
            return ("bin", "&", a, ("const", (1 << e[2]) - 1))
        return ("mod", a, e[2])
    if tag == "un":
        a = rewrite_expr(rng, e[2], width)
        if e[1] == "-" and rng.random() < 0.3:
            return ("bin", "+", ("un", "~", a), ("const", 1))
        if e[1] == "~" and rng.random() < 0.3:
            return ("bin", "-", ("un", "-", a), ("const", 1))
        return ("un", e[1], a)
    if tag == "cmp":
        a, b = rewrite_expr(rng, e[2], width), rewrite_expr(rng, e[3], width)
        flip = {"<": ">", ">": "<", "<=": ">=", ">=": "<=", "==": "==", "!=": "!="}
        inverse = {"<": ">=", ">=": "<", ">": "<=", "<=": ">", "==": "!=", "!=": "=="}
        roll = rng.random()
        if roll < 0.3:
            return ("cmp", flip[e[1]], b, a)
        if roll < 0.5:
            return ("not", ("cmp", inverse[e[1]], a, b))
        return ("cmp", e[1], a, b)
    if tag == "not":
        return ("not", rewrite_expr(rng, e[1], width))
    if tag == "boolop":
        parts = [rewrite_expr(rng, x, width) for x in e[2]]
        return ("boolop", e[1], parts)
    if tag == "ifexp":
        t = rewrite_expr(rng, e[1], width)
        a, b = rewrite_expr(rng, e[2], width), rewrite_expr(rng, e[3], width)
        if rng.random() < 0.3:
            return ("ifexp", ("not", t), b, a)
        return ("ifexp", t, a, b)
    return e


def rewrite_block(rng, body, width):
    out = []
    n = 0
    for s in body:
        tag = s[0]
        if tag == "assign":
            out.append(("assign", s[1], rewrite_expr(rng, s[2], width)))
        elif tag == "aug":
            if s[2] in ("<<", ">>"):
                out.append(("assign", s[1], ("shift", s[2], ("var", s[1]), s[3][1])))
            elif s[2] == "//":
                out.append(("assign", s[1], ("fdiv", ("var", s[1]), s[3][1].bit_length() - 1)))
            elif s[2] == "%":
                out.append(("assign", s[1], ("mod", ("var", s[1]), s[3][1].bit_length() - 1)))
            else:
                out.append(("assign", s[1], ("bin", s[2], ("var", s[1]), rewrite_expr(rng, s[3], width))))
        elif tag == "return":
            if rng.random() < 0.3:
                n += 1
                name = f"r{n}"
                out.append(("assign", name, rewrite_expr(rng, s[1], width)))
                out.append(("return", ("var", name)))
            else:
                out.append(("return", rewrite_expr(rng, s[1], width)))
        elif tag == "if":
            cond = rewrite_expr(rng, s[1], width)
            a = rewrite_block(rng, s[2], width)
            b = rewrite_block(rng, s[3], width)
            if rng.random() < 0.3:
                out.append(("if", ("not", cond), b, a))
            else:
                out.append(("if", cond, a, b))
        elif tag == "for":
            if len(range(*s[2])) <= 3 and rng.random() < 0.5:
                inner = rewrite_block(rng, s[3], width)
                for i in range(*s[2]):
                    out.append(("assign", s[1], ("const", i)))
                    out.extend(inner)
            else:
                out.append(("for", s[1], s[2], rewrite_block(rng, s[3], width)))
        else:
            out.append(s)
    if rng.random() < 0.1:
        out.insert(0, ("pass",))
    return out


def mutate_expr(rng, e, width):
    tag = e[0]
    if tag == "const":
        return ("const", e[1] + rng.choice((-1, 1, 2, width)))
    if tag == "bin":
        if rng.random() < 0.5:
            return ("bin", rng.choice(BIN_OPS), e[2], e[3])
        return ("bin", e[1], mutate_expr(rng, e[2], width), e[3])
    if tag == "cmp":
        if rng.random() < 0.6:
            return ("cmp", rng.choice(CMP_OPS), e[2], e[3])
        return ("cmp", e[1], mutate_expr(rng, e[2], width), e[3])
    if tag == "shift":
        return ("shift", e[1], e[2], max(0, e[3] + rng.choice((-1, 1))))
    if tag == "un":
        return ("un", rng.choice("-+~"), e[2])
    if tag == "ifexp":
        return ("ifexp", e[1], e[3], e[2]) if rng.random() < 0.3 else \
            ("ifexp", e[1], mutate_expr(rng, e[2], width), e[3])
    if tag == "var":
        return ("bin", "+", e, ("const", 1))
    return e


def mutate_block(rng, body, width):
    body = list(body)
    spots = [i for i, s in enumerate(body) if s[0] in ("assign", "return", "if", "for")]
    if not spots:
        return body
    i = rng.choice(spots)
    s = body[i]
    if s[0] == "assign":
        body[i] = ("assign", s[1], mutate_expr(rng, s[2], width))
    elif s[0] == "return":
        body[i] = ("return", mutate_expr(rng, s[1], width))
    elif s[0] == "if":
        if rng.random() < 0.5:
            body[i] = ("if", mutate_expr(rng, s[1], width), s[2], s[3])
        else:
            body[i] = ("if", s[1], mutate_block(rng, s[2], width), s[3])
    else:
        body[i] = ("for", s[1], s[2], mutate_block(rng, s[3], width))
    return body


# (f expression, g expression) over a single parameter x: pairs known to live
# near the fixed-width/Python boundary, so overflow_only actually gets exercised.
TEMPLATES = [
    (("fdiv", ("bin", "*", ("var", "x"), ("const", 4)), 2), ("var", "x")),
    (("cmp", ">", ("bin", "+", ("var", "x"), ("const", 1)), ("var", "x")), ("const", 1)),
    (("un", "-", ("un", "-", ("var", "x"))), ("var", "x")),
    (("shift", ">>", ("shift", "<<", ("var", "x"), 1), 1), ("var", "x")),
    (("bin", "-", ("bin", "+", ("var", "x"), ("const", 9)), ("const", 9)), ("var", "x")),
    (("fdiv", ("var", "x"), 1), ("shift", ">>", ("var", "x"), 1)),
    (("mod", ("var", "x"), 2), ("bin", "&", ("var", "x"), ("const", 3))),
    (("cmp", "<", ("un", "-", ("var", "x")), ("const", 0)), ("cmp", ">", ("var", "x"), ("const", 0))),
    (("bin", "*", ("var", "x"), ("const", 3)), ("bin", "+", ("shift", "<<", ("var", "x"), 1), ("var", "x"))),
    (("cmp", "==", ("bin", "*", ("var", "x"), ("var", "x")), ("const", 1)),
     ("boolop", "or", [("cmp", "==", ("var", "x"), ("const", 1)), ("cmp", "==", ("var", "x"), ("const", -1))])),
]


class Pair:
    def __init__(self, params, widths, body_f, body_g, strategy, features=()) -> None:
        self.params = params
        self.widths = widths
        self.body_f = body_f
        self.body_g = body_g
        self.strategy = strategy
        self.features = set(features)

    def source(self) -> str:
        return (render_function("f", self.params, self.body_f) + "\n"
                + render_function("g", self.params, self.body_g))


def has_value_boolop(e, truth_ctx=False) -> bool:
    tag = e[0]
    if tag == "boolop":
        if not truth_ctx:
            return True
        return any(has_value_boolop(x, True) for x in e[2])
    if tag == "not":
        return has_value_boolop(e[1], True)
    if tag == "ifexp":
        return has_value_boolop(e[1], True) or has_value_boolop(e[2]) or has_value_boolop(e[3])
    if tag in ("bin", "cmp"):
        return has_value_boolop(e[2]) or has_value_boolop(e[3])
    if tag in ("shift", "un"):
        return has_value_boolop(e[2])
    if tag in ("fdiv", "mod"):
        return has_value_boolop(e[1])
    return False


def block_has_value_boolop(body) -> bool:
    for s in body:
        tag = s[0]
        if tag == "assign" and has_value_boolop(s[2]):
            return True
        if tag == "aug" and has_value_boolop(s[3]):
            return True
        if tag == "return" and has_value_boolop(s[1]):
            return True
        if tag == "if" and (has_value_boolop(s[1], True) or block_has_value_boolop(s[2])
                            or block_has_value_boolop(s[3])):
            return True
        if tag == "for" and block_has_value_boolop(s[3]):
            return True
    return False


def make_pair(rng: random.Random, trap_rate: float = 0.08) -> Pair:
    traps = rng.random() < trap_rate
    shape = rng.random()
    if shape < 0.5:
        params = ["x"]
        widths = {"x": rng.randint(1, 7)}
    elif shape < 0.9:
        params = ["x", "y"]
        widths = {"x": rng.randint(1, 4), "y": rng.randint(1, 4)}
    else:
        params = ["x", "y", "z"]
        widths = {"x": rng.randint(1, 3), "y": rng.randint(1, 3), "z": rng.randint(1, 3)}
    width = max(widths.values())
    gen = ProgramGen(rng, params, width, traps)
    roll = rng.random()
    if roll < 0.08:
        strategy = "template"
        f_e, g_e = rng.choice(TEMPLATES)
        params = ["x"]
        widths = {"x": rng.randint(2, 7)}
        body_f, body_g = [("return", f_e)], [("return", g_e)]
    else:
        body_f = gen.function()
        if roll < 0.14:
            strategy = "identical"
            body_g = body_f
        elif roll < 0.6:
            strategy = "rewrite"
            body_g = rewrite_block(rng, body_f, width)
        elif roll < 0.88:
            strategy = "mutate"
            body_g = mutate_block(rng, body_f, width)
        else:
            strategy = "independent"
            body_g = gen.function()
    pair = Pair(params, widths, body_f, body_g, strategy)
    if block_has_value_boolop(body_f) or block_has_value_boolop(body_g):
        pair.features.add("value_boolop")
    return pair


def load_functions(source: str, workdir: str, serial: int):
    """Real functions with real source files, because pyeq reads them by inspect."""
    path = os.path.join(workdir, f"m{serial}.py")
    with open(path, "w") as fh:
        fh.write(source)
    scope: dict = {"__name__": f"gen_modelling_m{serial}"}
    exec(compile(source, path, "exec"), scope)
    return scope


def signed_range(w: int):
    return range(-(1 << (w - 1)), 1 << (w - 1))


def judge_pair(pair: Pair, f, g, t: Tally):
    """Every input, at the declared widths. Returns the disagreement table."""
    width = max(pair.widths.values())
    table = {}
    disagreements = []
    ranges = [signed_range(pair.widths[p]) for p in pair.params]
    for combo in itertools.product(*ranges):
        inputs = dict(zip(pair.params, combo))
        ef, eg = Eval(width), Eval(width)
        vf, vg = ef.run(pair.body_f, inputs), eg.run(pair.body_g, inputs)
        pf, pg = f(**inputs), g(**inputs)
        table[combo] = (vf, vg, pf, pg)
        t.counts["eval_inputs"] += 1
        # The evaluator earns its place here: with no overflow, it is Python.
        if not ef.overflowed:
            t.counts["eval_crosschecks"] += 1
            if vf != pf:
                t.bad("evaluator_vs_python", f"f{inputs}: eval {vf} python {pf}\n{pair.source()}")
        if not eg.overflowed:
            t.counts["eval_crosschecks"] += 1
            if vg != pg:
                t.bad("evaluator_vs_python", f"g{inputs}: eval {vg} python {pg}\n{pair.source()}")
        if vf != vg:
            disagreements.append(combo)
    return table, disagreements


def check_one_result(pair, r, table, disagreements, t, where, fs):
    src = pair.source()
    truth_equal = not disagreements
    ctx = f"{where} widths={pair.widths}\n{src}"
    t.step("pyeq_checks")
    if r.proved is True:
        t.counts["proved_true"] += 1
        if not truth_equal:
            combo = disagreements[0]
            t.bad("wrong_proved_true", f"proved=True but at {dict(zip(pair.params, combo))}: "
                                       f"{table[combo][:2]} {ctx}", fs)
        if r.counterexample is not None:
            t.bad("proved_with_cex", f"proved=True with a counterexample: {ctx}", fs)
    elif r.proved is False:
        t.counts["proved_false"] += 1
        if truth_equal:
            t.bad("wrong_proved_false", f"proved=False cex={r.counterexample} on functions "
                                        f"equal everywhere: {ctx}", fs)
        cex = r.counterexample
        if cex is None:
            t.bad("no_cex", f"proved=False without a counterexample: {ctx}", fs)
        elif set(cex) != set(pair.params):
            t.bad("cex_keys", f"counterexample {cex}: {ctx}", fs)
        else:
            combo = tuple(cex[p] for p in pair.params)
            if combo not in table:
                t.bad("cex_range", f"counterexample {cex} is outside the widths: {ctx}", fs)
            else:
                vf, vg, pf, pg = table[combo]
                if vf == vg:
                    t.bad("cex_spurious", f"counterexample {cex}: both are {vf} at this width: {ctx}", fs)
                if r.outputs != (vf, vg):
                    t.bad("cex_outputs", f"outputs={r.outputs} oracle=({vf}, {vg}) at {cex}: {ctx}", fs)
                if r.python_outputs != (pf, pg):
                    t.bad("cex_python_outputs", f"python_outputs={r.python_outputs} oracle="
                                                f"({pf}, {pg}) at {cex}: {ctx}", fs)
                if r.overflow_only != (pf == pg):
                    t.bad("overflow_only", f"overflow_only={r.overflow_only} python=({pf}, {pg}): {ctx}", fs)
                t.counts["overflow_only" if pf == pg else "real_difference"] += 1
    elif r.proved is None:
        t.bad("undecided_without_budget", f"proved=None with no budget: {ctx}", fs)
    else:
        t.bad("proved_not_three_valued", f"proved={r.proved!r}: {ctx}", fs)
    if bool(r) != (r.proved is True):
        t.bad("bool_of_result", f"bool(result)={bool(r)} proved={r.proved}: {ctx}", fs)
    expected_width = max(pair.widths[p] for p in pair.params)
    if r.width != expected_width:
        t.bad("width_claim", f"r.width={r.width}, the circuit is at {expected_width}: {ctx}", fs)
    if not isinstance(r.report(), str):
        t.bad("report", f"report() is not text: {ctx}", fs)


ENGINE_FIELDS = ("proved", "counterexample", "width", "vars", "clauses", "outputs",
                 "python_outputs", "overflow_only", "proof_checked", "conflicts",
                 "python_error")


def compare_engines(pair, rp, rn, t, fs) -> None:
    t.step("engine_comparisons")
    for field in ENGINE_FIELDS:
        a, b = getattr(rp, field), getattr(rn, field)
        if a != b:
            t.bad("engine_field", f"{field}: python={a!r} native={b!r}\n{pair.source()}", fs)
    # Not a mismatch: tests/test_pyeq.py documents that the engines emit
    # different proofs from the same search. See finding modelling-14.
    t.counts["note_proof_steps_differ" if rp.proof_steps != rn.proof_steps
             else "proof_steps_same"] += 1


def miter_cnf(f, g, widths) -> CNF:
    """The miter, built through the module's public compiler."""
    formula = CNF()
    enc = Encoder(formula)
    out_f, inputs = compile_function(f, enc, widths)
    out_g, _ = compile_function(g, enc, widths, inputs=inputs)
    w = max(out_f.width, out_g.width)
    a, b = out_f.extend(w), out_g.extend(w)
    enc.add([enc.xor_gate(x, y) for x, y in zip(a.bits, b.bits)])
    return formula


def check_pair(pair: Pair, rng, t: Tally, workdir: str, serial: int,
               equivalent=real_equivalent, use_native=True) -> None:
    scope = load_functions(pair.source(), workdir, serial)
    f, g = scope["f"], scope["g"]
    table, disagreements = judge_pair(pair, f, g, t)
    fs = set(pair.features)
    t.counts["pyeq_pairs"] += 1
    t.counts[f"strategy_{pair.strategy}"] += 1
    t.counts["pairs_equal" if not disagreements else "pairs_differ"] += 1
    if len(pair.params) > 1 and len({pair.widths[p] for p in pair.params}) > 1:
        t.counts["pairs_mixed_widths"] += 1
    if disagreements and len(disagreements) * 8 <= len(table):
        t.counts["pairs_rare_difference"] += 1

    try:
        rp = equivalent(f, g, pair.widths, engine="python")
    except UnsupportedConstruct as e:
        t.bad("rejected_in_subset", f"{e}\n{pair.source()}", fs)
        return
    check_one_result(pair, rp, table, disagreements, t, "python", fs)
    if rp.proved is True:
        if not rp.proof_checked:
            t.bad("proof_not_checked", f"proved=True, verify on, no proof check\n{pair.source()}", fs)
        t.counts["proof_checked"] += 1
        if rp.proof_steps:
            t.counts["proof_nonempty"] += 1

    if use_native:
        rn = equivalent(f, g, pair.widths, engine="native")
        check_one_result(pair, rn, table, disagreements, t, "native", fs)
        compare_engines(pair, rp, rn, t, fs)

    # the default engine is one of the two, and must answer as they do
    if use_native and rng.random() < 0.2:
        ra = equivalent(f, g, pair.widths)
        t.step("auto_engine_runs")
        check_one_result(pair, ra, table, disagreements, t, "auto", fs)
        compare_engines(pair, rn, ra, t, fs)

    # verify=False must not change the answer, and must say it did not check
    if rng.random() < 0.3:
        r = equivalent(f, g, pair.widths, engine="python", verify=False)
        check_one_result(pair, r, table, disagreements, t, "python verify=False", fs)
        t.counts["verify_false_runs"] += 1
        if r.proof_checked:
            t.bad("verify_false_checked", f"verify=False claims a checked proof\n{pair.source()}", fs)

    # a budget may stop it, and then it must claim nothing
    if rp.conflicts >= 1 and rng.random() < 0.6:
        budget = rng.randint(0, rp.conflicts - 1) if rp.conflicts > 1 else 0
        for engine in ("python", "native") if use_native else ("python",):
            r = equivalent(f, g, pair.widths, engine=engine, max_conflicts=budget)
            t.step("budget_runs")
            if r.proved is None:
                t.counts["proved_none"] += 1
                if bool(r) or r.counterexample is not None or r.outputs is not None:
                    t.bad("undecided_claims", f"proved=None with claims, budget {budget}\n{pair.source()}", fs)
                if "UNDECIDED" not in r.report():
                    t.bad("undecided_report", f"report on None: {r.report()}\n{pair.source()}", fs)
            else:
                check_one_result(pair, r, table, disagreements, t, f"{engine} budget={budget}", fs)

    # the miter itself, judged without the solver
    if rng.random() < 0.08:
        cnf = miter_cnf(f, g, pair.widths)
        t.step("dpll_miters")
        t.counts["max_miter_vars"] = max(t.counts["max_miter_vars"], cnf.nvars)
        if dpll.satisfiable(cnf_dimacs(cnf)) != (rp.proved is False):
            t.bad("dpll_miter", f"DPLL disagrees with proved={rp.proved}\n{pair.source()}", fs)

    # declaring a width for something that is not a parameter
    if rng.random() < 0.05:
        widths = dict(pair.widths)
        widths["unused_key"] = max(widths.values()) + 3
        r = equivalent(f, g, widths, engine="python")
        t.step("extra_width_runs")
        expected = max(pair.widths[p] for p in pair.params)
        if r.width != expected:
            t.bad("width_claim", f"widths={widths}: r.width={r.width}, circuit at {expected}",
                  fs | {"extra_width"})


# --------------------------------------------------------------------------
# hand-written probes: what lies outside the generator's grammar
# --------------------------------------------------------------------------

# Each must raise UnsupportedConstruct.
MUST_REJECT = {
    "while": "def f(x):\n    while x:\n        x = 0\n    return x\n",
    "floordiv3": "def f(x):\n    return x // 3\n",
    "mod3": "def f(x):\n    return x % 3\n",
    "floordiv0": "def f(x):\n    return x // 0\n",
    "truediv": "def f(x):\n    return x / 2\n",
    "pow": "def f(x):\n    return x ** 2\n",
    "matmul": "def f(x):\n    return x @ x\n",
    "shift_var": "def f(x):\n    return x << x\n",
    "shift_negative": "def f(x):\n    return x << -1\n",
    "call": "def f(x):\n    return abs(x)\n",
    "call_stmt": "def f(x):\n    print(x)\n    return x\n",
    "chain": "def f(x):\n    return 0 < x < 3\n",
    "tuple_assign": "def f(x):\n    a, b = x, x\n    return a\n",
    "multi_assign": "def f(x):\n    a = b = x\n    return a\n",
    "no_return": "def f(x):\n    x = 1\n",
    "fall_through": "def f(x):\n    if x:\n        return 1\n",
    "loop_return_only": "def f(x):\n    for i in range(3):\n        return i\n",
    "bare_return": "def f(x):\n    return\n",
    "return_none": "def f(x):\n    return None\n",
    "string": "def f(x):\n    return 'a'\n",
    "float": "def f(x):\n    return x + 1.5\n",
    "float_shift": "def f(x):\n    return x << 1.0\n",
    "list": "def f(x):\n    return [x]\n",
    "lambda": "def f(x):\n    return (lambda y: y)(x)\n",
    "global_read": "def f(x):\n    return UNDEFINED_GLOBAL\n",
    "global_stmt": "def f(x):\n    global G\n    G = x\n    return x\n",
    "for_else": "def f(x):\n    for i in range(2):\n        pass\n    else:\n        x = 1\n    return x\n",
    "range_var": "def f(x):\n    for i in range(x):\n        pass\n    return x\n",
    "range_large": "def f(x):\n    for i in range(300):\n        pass\n    return x\n",
    "for_list": "def f(x):\n    for i in [1, 2]:\n        pass\n    return x\n",
    "break": "def f(x):\n    for i in range(2):\n        break\n    return x\n",
    "continue": "def f(x):\n    for i in range(2):\n        continue\n    return x\n",
    "default": "def f(x=1):\n    return x\n",
    "varargs": "def f(*x):\n    return 1\n",
    "kwargs": "def f(**x):\n    return 1\n",
    "kwonly": "def f(*, x):\n    return x\n",
    "try": "def f(x):\n    try:\n        return x\n    except Exception:\n        return 0\n",
    "with": "def f(x):\n    with x:\n        return x\n",
    "assert": "def f(x):\n    assert x\n    return x\n",
    "raise": "def f(x):\n    raise ValueError\n",
    "del": "def f(x):\n    del x\n    return 0\n",
    "is": "def f(x):\n    return x is x\n",
    "in": "def f(x):\n    return x in x\n",
    "nested_def": "def f(x):\n    def h():\n        return 1\n    return x\n",
    "class": "def f(x):\n    class C:\n        pass\n    return x\n",
    "import": "def f(x):\n    import os\n    return x\n",
    "annassign": "def f(x):\n    y: int = x\n    return y\n",
    "walrus_expr": "def f(x):\n    return (y := x)\n",
    "one_branch_name": "def f(x):\n    if x:\n        y = 1\n    return y\n",
    "subscript": "def f(x):\n    return x[0]\n",
    "attribute": "def f(x):\n    return x.real\n",
}

# Python either raises on these or behaves differently from what is compiled,
# so anything but UnsupportedConstruct or proved=False needs explaining.
SILENT_ACCEPT = {
    "walrus_stmt": ("bare_expr", "def f(x):\n    (x := x + 1)\n    return x\n",
                    "def g(x):\n    return x\n"),
    "yield_stmt": ("bare_expr", "def f(x):\n    yield x\n    return x\n",
                   "def g(x):\n    return x\n"),
    "mod_zero_stmt": ("bare_expr", "def f(x):\n    x % 0\n    return x\n",
                      "def g(x):\n    return x\n"),
    "name_error_stmt": ("bare_expr", "def f(x):\n    UNDEFINED_NAME\n    return x\n",
                        "def g(x):\n    return x\n"),
    "subscript_stmt": ("bare_expr", "def f(x):\n    x[0]\n    return x\n",
                       "def g(x):\n    return x\n"),
    "nested_call_stmt": ("bare_expr", "def f(x):\n    [exit_marker() for i in range(1)]\n    return x\n",
                         "def g(x):\n    return x\n"),
    "decorator": ("decorator", "@double\ndef f(x):\n    return x\n", "def g(x):\n    return x\n"),
    "range_noargs": ("range_shape", "def f(x):\n    for i in range():\n        x = x + 1\n    return x\n",
                     "def g(x):\n    return x\n"),
    "range_keyword": ("range_shape", "def f(x):\n    for i in range(stop=3):\n        x = x + 1\n    return x\n",
                      "def g(x):\n    return x\n"),
    "range_shadowed": ("range_shape",
                       "def f(x):\n    range = 7\n    for i in range(1):\n        x = x + 1\n    return x\n",
                       "def g(x):\n    return x + 1\n"),
    "value_and": ("value_boolop", "def f(x, y):\n    return x and y\n",
                  "def g(x, y):\n    return 1 if (x != 0 and y != 0) else 0\n"),
    "value_or": ("value_boolop", "def f(x, y):\n    return x or y\n",
                 "def g(x, y):\n    return 1 if (x != 0 or y != 0) else 0\n"),
    "positional_only": ("posonly", "def f(a, /, x):\n    return x\n",
                        "def g(a, /, x):\n    return x + 1\n"),
}

PROBE_PRELUDE = '''
import functools
def double(fn):
    @functools.wraps(fn)
    def wrapper(*args, **kwargs):
        return fn(*args, **kwargs) * 2
    return wrapper
def exit_marker():
    raise RuntimeError("side effect")
'''


def python_outcome(fn, inputs, width):
    try:
        v = fn(**inputs)
    except Exception as e:
        return ("raised", type(e).__name__)
    if isinstance(v, int):
        u = int(v) % (1 << width)
        return ("value", u - (1 << width) if u >= 1 << (width - 1) else u)
    return ("not-int", type(v).__name__)


def run_probes(t: Tally, workdir: str, equivalent=real_equivalent, use_native=True) -> None:
    serial = 0
    for name, src in MUST_REJECT.items():
        serial += 1
        scope = load_functions(src, workdir, 100000 + serial)
        t.step("probe_must_reject")
        try:
            r = equivalent(scope["f"], scope["f"], {"x": 3}, engine="python")
        except UnsupportedConstruct:
            t.counts["probe_rejected"] += 1
        except Exception as e:
            t.bad("probe_wrong_exception", f"{name}: {type(e).__name__}: {e}")
        else:
            t.bad("probe_not_rejected", f"{name}: proved={r.proved}\n{src}")

    for name, (feature, src_f, src_g) in SILENT_ACCEPT.items():
        serial += 1
        scope = load_functions(PROBE_PRELUDE + "\n" + src_f + "\n" + src_g, workdir, 100000 + serial)
        f, g = scope["f"], scope["g"]
        params = list(inspect.signature(f).parameters)
        widths = {p: 3 for p in params}
        agree = True
        for combo in itertools.product(*[signed_range(3) for _ in params]):
            kw = dict(zip(params, combo))
            if name == "positional_only":
                oc_f = python_outcome(lambda **k: f(k["a"], k["x"]), kw, 3)
                oc_g = python_outcome(lambda **k: g(k["a"], k["x"]), kw, 3)
            else:
                oc_f, oc_g = python_outcome(f, kw, 3), python_outcome(g, kw, 3)
            if oc_f != oc_g or oc_f[0] != "value":
                agree = False
        t.step("probe_silent_accept")
        for engine in ("python", "native") if use_native else ("python",):
            try:
                r = equivalent(f, g, widths, engine=engine)
            except UnsupportedConstruct:
                t.counts["probe_silent_rejected"] += 1
                continue
            except Exception as e:
                t.bad("probe_crash", f"{name} ({engine}): {type(e).__name__}: {e}", {feature})
                continue
            if r.proved is True and not agree:
                t.bad("probe_wrong_proved_true",
                      f"{name} ({engine}): proved=True, Python disagrees\n{src_f}{src_g}", {feature})
            else:
                t.counts["probe_silent_ok"] += 1

    # no parameters at all: the circuit is at 8 bits, whatever the report says
    scope = load_functions("def f():\n    return 300\ndef g():\n    return 44\n", workdir, 100899)
    t.step("probe_no_params")
    r = equivalent(scope["f"], scope["g"], {}, engine="python")
    if r.proved is True and r.width != 8:
        t.bad("width_claim", f"no parameters: 300 and 44 proved equal, r.width={r.width}, circuit at 8",
              {"extra_width"})

    # signature checks and missing widths
    scope = load_functions("def f(x):\n    return x\ndef g(y):\n    return y\n", workdir, 100900)
    t.step("probe_signature")
    try:
        equivalent(scope["f"], scope["g"], {"x": 3, "y": 3}, engine="python")
        t.bad("probe_signature", "different parameter names were accepted")
    except UnsupportedConstruct:
        t.counts["probe_rejected"] += 1
    scope = load_functions("def f(x, y):\n    return x\ndef g(x, y):\n    return x\n", workdir, 100901)
    t.step("probe_missing_width")
    try:
        equivalent(scope["f"], scope["g"], {"x": 3}, engine="python")
        t.bad("probe_missing_width", "a parameter without a width was accepted")
    except UnsupportedConstruct:
        t.counts["probe_rejected"] += 1


# ==========================================================================
# the run
# ==========================================================================

# Every category claimed as covered: zero in any of them fails the run.
REQUIRED = (
    "model_sat", "model_unsat", "model_multi_solution", "var_bool", "var_int", "var_int_order",
    "c_add", "c_add_clause", "c_all_different", "c_all_different_permutation", "c_sum_leq", "c_sum_geq",
    "c_parity_odd", "c_parity_even",
    *[f"c_at_most_one_{m}" for m in AMO_METHODS], *[f"c_exactly_one_{m}" for m in AMO_METHODS],
    *[f"c_at_most_k_{m}" for m in AMK_METHODS], *[f"c_at_least_k_{m}" for m in AMK_METHODS],
    *[f"c_exactly_k_{m}" for m in AMK_METHODS],
    "override_pairwise", "override_binary", "override_commander", "override_sequential", "override_totalizer",
    "differential_varied_cnf", "auto_engine_runs",
    "check_solve", "check_solutions_set", "check_solutions_limit", "check_solutions_unprojected",
    "check_unsat_proof", "unsat_proof_python", "unsat_proof_native", "check_native_cnf",
    "check_dpll_assignment", "check_dpll_one_hot", "cnf_past_16_vars",
    "assumption_sat", "assumption_unsat", "check_differential",
    "check_optimum", "optimum_exists", "optimum_infeasible", "check_weighted_optimum",
    "check_incremental", "incremental_same_vars", "incremental_new_vars", "check_solve_after_solutions",
    "pyeq_pairs", "strategy_rewrite", "strategy_mutate", "strategy_independent", "strategy_identical",
    "strategy_template", "pairs_equal", "pairs_differ", "pairs_mixed_widths", "pairs_rare_difference",
    "proved_true", "proved_false", "proved_none", "proof_checked", "proof_nonempty",
    "overflow_only", "real_difference", "eval_crosschecks", "verify_false_runs", "budget_runs",
    "engine_comparisons", "dpll_miters", "extra_width_runs",
    "probe_must_reject", "probe_rejected", "probe_silent_accept",
)


def run(seed: int, instances: int, use_native=True, model_impl=Model,
        equivalent=real_equivalent, probes=True, pairs: int | None = None) -> Tally:
    t = Tally()
    rng = random.Random(seed)
    for _ in range(instances):
        spec = make_spec(rng)
        guarded_check_model(spec, rng, t, model_impl, use_native)
    with tempfile.TemporaryDirectory(prefix="gen_modelling") as workdir:
        for serial in range(instances if pairs is None else pairs):
            pair = make_pair(rng)
            try:
                check_pair(pair, rng, t, workdir, serial, equivalent, use_native)
            except Exception as e:  # a crash on a valid pair is a finding
                t.bad("pair_crash", f"{type(e).__name__}: {e}\n{pair.source()}", pair.features)
        if probes:
            run_probes(t, workdir, equivalent, use_native)
    return t


# ==========================================================================
# --self-test: a harness that cannot catch a wrong tool is worthless
# ==========================================================================


class _StubResult:
    def __init__(self, proved, cex=None) -> None:
        self.proved = proved
        self.counterexample = cex
        self.outputs = None
        self.python_outputs = None
        self.overflow_only = False
        self.proof_checked = proved is True
        self.proof_steps = 0
        self.conflicts = 0
        self.width = 0
        self.vars = 0
        self.clauses = 0
        self.python_error = None

    def __bool__(self):
        return self.proved is True

    def report(self):
        return "stub"


def stub_always_proved(f, g, widths, **kw):
    return _StubResult(True)


def stub_always_differ(f, g, widths, **kw):
    return _StubResult(False, {k: 0 for k in widths})


def stub_always_undecided(f, g, widths, **kw):
    return _StubResult(None)


def stub_lying_cex(f, g, widths, **kw):
    r = real_equivalent(f, g, widths, **kw)
    if r.proved is False:
        r.counterexample = {k: 0 for k in r.counterexample}
    return r


def stub_flip_truthy(f, g, widths, **kw):
    r = real_equivalent(f, g, widths, **kw)
    if r.proved is False:
        r.proved = True
        r.counterexample = None
    return r


class StubModelUnsat(Model):
    """Rejects everything."""

    def solve(self, proof=None, assumptions=()):
        super().solve(proof, assumptions)
        return None


class StubModelNoCardinality(Model):
    """A cardinality encoding that encodes nothing."""

    def at_most_k(self, items, k, method="auto"):
        return None

    def exactly_k(self, items, k, method="auto"):
        return None

    def at_most_one(self, items, method="auto"):
        return None


class StubModelDropsSolution(Model):
    """Enumeration that loses the last solution."""

    def solutions(self, project=None, limit=0):
        found = list(super().solutions(project=project, limit=limit))
        yield from found[:-1]


class StubModelWrongPB(Model):
    """A pseudo-Boolean bound off by one."""

    def sum_leq(self, weights, items, bound):
        super().sum_leq(weights, items, bound + 1)


class WrongEval(Eval):
    """A logical right shift: the evaluator cross-check must notice."""

    def value(self, e, env):
        if e[0] == "shift" and e[1] == ">>":
            a = self.value(e[2], env)
            return self.wrap((a % self.mod) >> e[3])
        return super().value(e, env)


def self_test() -> int:
    failures = []

    def expect_flagged(label, kinds=None, models=0, pairs=0, **kw):
        t = run(4242, models, probes=False, pairs=pairs, **kw)
        hits = [m for m in t.mismatches if kinds is None or m["kind"] in kinds]
        print(f"  {label}: {len(hits)} of {len(t.mismatches)} mismatches flagged")
        if not hits:
            failures.append(label)

    print("models:")
    expect_flagged("rejects everything", {"solve_verdict"}, models=100, model_impl=StubModelUnsat)
    expect_flagged("cardinality encodes nothing", {"solve_verdict", "solve_model", "solutions_set"},
                   models=100, model_impl=StubModelNoCardinality)
    expect_flagged("enumeration drops a solution", {"solutions_set"}, models=100,
                   model_impl=StubModelDropsSolution)
    expect_flagged("PB bound off by one", {"solve_verdict", "solve_model", "solutions_set"},
                   models=400, model_impl=StubModelWrongPB)

    print("pyeq:")
    expect_flagged("always proved", {"wrong_proved_true"}, pairs=100,
                   equivalent=stub_always_proved, use_native=False)
    expect_flagged("always differs", {"wrong_proved_false"}, pairs=100,
                   equivalent=stub_always_differ, use_native=False)
    expect_flagged("always undecided", {"undecided_without_budget"}, pairs=100,
                   equivalent=stub_always_undecided, use_native=False)
    expect_flagged("lying counterexample", {"cex_spurious", "cex_outputs", "cex_range", "cex_python_outputs"},
                   pairs=100, equivalent=stub_lying_cex, use_native=False)
    expect_flagged("turns differences into proofs", {"wrong_proved_true"}, pairs=100,
                   equivalent=stub_flip_truthy, use_native=False)

    print("evaluator:")
    global Eval
    original = Eval
    Eval = WrongEval
    try:
        expect_flagged("logical right shift in the oracle", {"evaluator_vs_python"}, pairs=100)
    finally:
        Eval = original

    print("probes:")
    t = Tally()
    with tempfile.TemporaryDirectory(prefix="gen_modelling") as workdir:
        run_probes(t, workdir, stub_always_proved, use_native=False)
    wrong = [m for m in t.mismatches if m["kind"] in ("probe_not_rejected", "probe_wrong_proved_true")]
    print(f"  always-proved stub through the probes: {len(wrong)} flagged")
    if not wrong:
        failures.append("probes")

    print("categories:")
    t = run(4242, 5, probes=False)
    missing = [c for c in REQUIRED if not t.counts[c]]
    print(f"  a 5-instance run leaves {len(missing)} categories at zero, and the run reports that")
    if not missing:
        failures.append("the category check cannot fail")

    if failures:
        print(f"SELF-TEST FAILED, not flagged: {failures}")
        return 1
    print("self-test passed: every stub was flagged")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--seed", type=int, default=DEFAULT_SEED)
    ap.add_argument("--instances", type=int, default=DEFAULT_INSTANCES,
                    help="models, and separately pyeq pairs")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--no-results", action="store_true", help="do not write the results file")
    ap.add_argument("--show", type=int, default=3, help="mismatches to print per kind")
    args = ap.parse_args()

    if args.self_test:
        return self_test()

    if not native_available():
        print("the native engine is not installed; this corner compares both engines")
        return 2

    t0 = time.perf_counter()
    t = run(args.seed, args.instances)
    seconds = time.perf_counter() - t0

    by_kind: Counter = Counter()
    for m in t.mismatches:
        by_kind[(m["kind"], ",".join(m["labels"]) or "UNEXPLAINED")] += 1
    shown: Counter = Counter()
    for m in t.mismatches:
        key = (m["kind"], tuple(m["labels"]))
        if shown[key] < args.show:
            print(f"--- {m['kind']} [{','.join(m['labels']) or 'UNEXPLAINED'}]\n{m['detail']}\n")
        shown[key] += 1

    missing = [c for c in REQUIRED if not t.counts[c]]
    print(f"seed={args.seed} instances={args.instances} steps={t.steps} seconds={seconds:.1f}")
    print("counts:", json.dumps(dict(sorted(t.counts.items()))))
    print("mismatches:", {f"{k}[{v}]": n for (k, v), n in sorted(by_kind.items())})
    print(f"labelled={len(t.mismatches) - len(t.unexplained)} unexplained={len(t.unexplained)}")
    if missing:
        print(f"CATEGORIES AT ZERO: {missing}")

    if not args.no_results:
        findings_seen = sorted({l for m in t.mismatches for l in m["labels"]})
        payload = {
            "corner": "modelling",
            "seeds": [args.seed],
            "instances": args.instances * 2,
            "steps": t.steps,
            "per_category_counts": dict(sorted(t.counts.items())),
            "runtime_seconds": round(seconds, 1),
            "mismatches_by_kind": {f"{k}[{v}]": n for (k, v), n in sorted(by_kind.items())},
            "findings_observed_in_this_run": findings_seen,
            "findings": FINDINGS,
            "not_checked": NOT_CHECKED,
        }
        with open(RESULTS_PATH, "w") as fh:
            json.dump(payload, fh, indent=2)
            fh.write("\n")

    return 1 if t.mismatches or missing else 0


if __name__ == "__main__":
    sys.exit(main())
