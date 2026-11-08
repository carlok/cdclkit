# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness campaign, encodings corner: exact solution sets, not just counts.

Run from the repository root: python -m campaign.gen_encodings
Self-test against deliberately wrong encoders: python -m campaign.gen_encodings --self-test

What it checks:

* The grid. at_most_one, at_least_one, exactly_one, at_most_k, at_least_k and
  exactly_k with every method name, every n from 0 to 10 and every k from 0 to
  n, each under several literal signs and orders. The satisfying assignments
  projected on the input variables must equal the combinatorial set. The judge
  is campaign.dpll.projected_models, and the oracle where the formula is small
  enough. A method name a cell rejects must raise ValueError and emit nothing.
* The same cells through the Python solver, the native engine and the
  preprocessor (a model must be a model, SAT iff the set is non-empty), and
  through the Solver sink (every input assignment as assumptions).
* Totalizer: bounds tightened one at a time on one object, truncated counters,
  output semantics, assumptions retracted, bounds past the cut.
* optimise and Optimiser against the brute-force optimum.
* Off the grid: k < 0 and k > n, repeated and complementary inputs, the amo_* /
  amk_* methods directly, stacked constraints, undeclared inputs, inputs fixed
  at the root, and the arc consistency the module documents.

Known findings stay mismatches and the run exits non-zero while they stand.
They are labelled with their finding id; anything else prints as UNEXPLAINED.
"""

from __future__ import annotations

import argparse
import collections
import itertools
import json
import multiprocessing
import os
import pathlib
import random
import sys
import time

from campaign import dpll, oracle
from cdclkit import solve
from cdclkit import encodings as enc_mod
from cdclkit.encodings import Encoder, Optimiser, Totalizer
from cdclkit.pipeline import solve_adaptive
from cdclkit.solver import Solver
from dratify.cnf import CNF
from dratify.lits import from_dimacs, neg, to_dimacs

MAX_N = 10
DEFAULT_SEED = 20261108
DEFAULT_INSTANCES = 4      # random sign-and-order patterns per grid cell
DEFAULT_OPT_INSTANCES = 1500
FIXED_PATTERNS = 3         # identity, all negated, reversed
SOLVER_SINK_ALL_PATTERNS_N = 6

AMO_METHODS = ("auto", "pairwise", "binary", "commander", "sequential", "totalizer")
ALL_METHODS = AMO_METHODS + ("bogus",)
ALWAYS_ACCEPTED_K = ("auto", "sequential", "totalizer")

FNS = ("at_most_one", "at_least_one", "exactly_one", "at_most_k", "at_least_k", "exactly_k")

PRED = {
    "at_most_one": lambda s, k: s <= 1,
    "at_least_one": lambda s, k: s >= 1,
    "exactly_one": lambda s, k: s == 1,
    "at_most_k": lambda s, k: s <= k,
    "at_least_k": lambda s, k: s >= k,
    "exactly_k": lambda s, k: s == k,
}

FINDINGS = {
    "encodings-1": ("Bug", "Totalizer over no inputs recurses forever: at_most_one([], 'totalizer'), "
                           "exactly_one([], 'totalizer') and amk_totalizer([], k) raise RecursionError"),
    "encodings-2": ("Bug", "A truncated Totalizer answers bounds past its cut wrongly: at-most is "
                           "dropped as 'vacuous' and at-least becomes false, so the solutions are wrong"),
    "encodings-3": ("Bug", "at_most_k and exactly_k with k < 0 leave the all-false assignment "
                           "instead of no solutions, unlike amk_sequential and amk_totalizer"),
    "encodings-4": ("Bug", "Inputs not yet declared to the sink collide with auxiliary variables: "
                           "new_var hands out the input's own variable, and the solutions are wrong"),
    "encodings-5": ("Bug", "Optimiser.best can get worse: a later run overwrites it with a worse "
                           "model, against 'from the current best' and 'the best solution found'"),
    "encodings-6": ("Note", "An Optimiser with no soft literals ignores a negative bound: "
                            "solve_with_bound(-1) and run(target=-1) return a model of count 0"),
}

#: Filed by another corner of the campaign and met here on the grid: at_least_one([]) and
#: exactly_one([]) emit the empty clause, which the preprocessors cannot take.
FOREIGN_FINDINGS = {
    "preprocess-2": ("Bug", "Filed by the preprocess corner, met here at n = 0: the empty clause "
                            "crashes both preprocessors, so solve_adaptive(always_preprocess=True) "
                            "raises on at_least_one([]) and exactly_one([])"),
}


# --------------------------------------------------------------------------
# implementations under test, so that --self-test can swap in wrong ones
# --------------------------------------------------------------------------


class Real:
    at_most_one = staticmethod(enc_mod.at_most_one)
    at_least_one = staticmethod(enc_mod.at_least_one)
    exactly_one = staticmethod(enc_mod.exactly_one)
    at_most_k = staticmethod(enc_mod.at_most_k)
    at_least_k = staticmethod(enc_mod.at_least_k)
    exactly_k = staticmethod(enc_mod.exactly_k)
    Totalizer = Totalizer
    Optimiser = Optimiser
    optimise = staticmethod(enc_mod.optimise)


def _nothing(*a, **k):
    return None


def _reject(target, *a, **k):
    Encoder(target).add([])


class StubAcceptAll(Real):
    """Every constraint is empty, so every assignment is a solution."""
    at_most_one = at_least_one = exactly_one = staticmethod(_nothing)
    at_most_k = at_least_k = exactly_k = staticmethod(_nothing)


class StubRejectAll(Real):
    """Every constraint is the empty clause, so nothing is a solution."""
    at_most_one = at_least_one = exactly_one = staticmethod(_reject)
    at_most_k = at_least_k = exactly_k = staticmethod(_reject)


def _same_count_wrong_set(target, lits, k, method="auto"):
    """As many solutions as the right answer, but not the same ones."""
    enc_mod.at_most_k(target, [neg(lits[0])] + list(lits[1:]) if lits else lits, k, method)


def _off_by_one(target, lits, k, method="auto"):
    enc_mod.at_most_k(target, lits, k + 1, method)


def _wrong_when(cond):
    def stub(target, lits, k, method="auto"):
        if cond(list(lits), k, method):
            enc_mod.at_most_k(target, lits, k + 1, method)
        else:
            enc_mod.at_most_k(target, lits, k, method)
    return stub


def _extra_clause_at_kn(target, lits, k, method="auto"):
    enc_mod.at_most_k(target, lits, k, method)
    if lits and k == len(lits):
        Encoder(target).add([neg(lits[0])])


def _binary_broken(target, lits, method="auto"):
    if method == "binary" and len(lits) == 3:
        return
    enc_mod.at_most_one(target, lits, method)


def _rejects_everything(target, lits, k, method="auto"):
    raise ValueError("this stub takes no method")


def _crashes(target, lits, k, method="auto"):
    raise RuntimeError("this stub falls over")


class StubCrashes(Real):
    at_most_k = staticmethod(_crashes)


class StubSameCount(Real):
    at_most_k = staticmethod(_same_count_wrong_set)


class StubOffByOne(Real):
    at_most_k = staticmethod(_off_by_one)


class StubOnlyK0(Real):
    at_most_k = staticmethod(_wrong_when(lambda l, k, m: k == 0))


class StubOnlyKn(Real):
    at_most_k = staticmethod(_extra_clause_at_kn)


class StubOnlyN10(Real):
    at_most_k = staticmethod(_wrong_when(lambda l, k, m: len(l) == 10 and k == 7))


class StubOnlyNegated(Real):
    at_most_k = staticmethod(_wrong_when(lambda l, k, m: any(x & 1 for x in l) and not all(x & 1 for x in l)))


class StubOnlyUnsorted(Real):
    at_most_k = staticmethod(_wrong_when(lambda l, k, m: l != sorted(l) and l != sorted(l, reverse=True)))


class StubOnlyTotalizerMethod(Real):
    at_most_k = staticmethod(_wrong_when(lambda l, k, m: m == "totalizer"))


class StubBinaryN3(Real):
    at_most_one = staticmethod(_binary_broken)


class StubRejectsMethods(Real):
    at_most_k = staticmethod(_rejects_everything)


class _TighteningIgnored(Totalizer):
    def assert_at_most(self, k):
        pass


class _SecondTighteningIgnored(Totalizer):
    def assert_at_most(self, k):
        self._seen = getattr(self, "_seen", 0) + 1
        if self._seen <= 1:
            super().assert_at_most(k)


class _ShiftedOutput(Totalizer):
    def at_most_lit(self, k):
        return super().at_most_lit(k + 1)


class _LyingOutputs(Totalizer):
    def __init__(self, enc, lits, max_count=None):
        super().__init__(enc, lits, max_count)
        self.outputs = list(reversed(self.outputs))


class StubTotalizerNoop(Real):
    Totalizer = _TighteningIgnored


class StubTotalizerSecond(Real):
    Totalizer = _SecondTighteningIgnored


class StubTotalizerShift(Real):
    Totalizer = _ShiftedOutput


class StubTotalizerOutputs(Real):
    Totalizer = _LyingOutputs


def _opt_first_model(solver, soft, minimise=True, assumption_based=True, on_improve=None):
    opt = Optimiser(solver, soft, minimise=minimise)
    return opt.run(max_iterations=1)


def _opt_wrong_count(solver, soft, minimise=True, assumption_based=True, on_improve=None):
    r = enc_mod.optimise(solver, soft, minimise, assumption_based, on_improve)
    return None if r is None else (r[0] + 1, r[1])


def _opt_none(solver, soft, minimise=True, assumption_based=True, on_improve=None):
    return None


def _opt_bad_model(solver, soft, minimise=True, assumption_based=True, on_improve=None):
    r = enc_mod.optimise(solver, soft, minimise, assumption_based, on_improve)
    return None if r is None else (r[0], [not b for b in r[1]])


def _opt_ignores_direction(solver, soft, minimise=True, assumption_based=True, on_improve=None):
    return enc_mod.optimise(solver, soft, True, assumption_based, on_improve)


class StubOptFirst(Real):
    optimise = staticmethod(_opt_first_model)


class StubOptCount(Real):
    optimise = staticmethod(_opt_wrong_count)


class StubOptNone(Real):
    optimise = staticmethod(_opt_none)


class StubOptModel(Real):
    optimise = staticmethod(_opt_bad_model)


class StubOptDirection(Real):
    optimise = staticmethod(_opt_ignores_direction)


IMPLS = {c.__name__: c for c in (
    Real, StubAcceptAll, StubRejectAll, StubSameCount, StubOffByOne, StubOnlyK0, StubOnlyKn,
    StubOnlyN10, StubOnlyNegated, StubOnlyUnsorted, StubOnlyTotalizerMethod, StubBinaryN3,
    StubRejectsMethods, StubCrashes, StubTotalizerNoop, StubTotalizerSecond, StubTotalizerShift,
    StubTotalizerOutputs, StubOptFirst, StubOptCount, StubOptNone, StubOptModel, StubOptDirection,
)}


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------


class Report:
    """What one task saw: counters, mismatches, and checks judged."""

    def __init__(self):
        self.c = collections.Counter()
        self.bad = []
        self.steps = 0
        self.instances = 0

    def mismatch(self, kind, label=None, **detail):
        self.bad.append({"kind": kind, "label": label, **detail})


def pattern(seed, tag, n, pat):
    """(declared variable count, input literals in DIMACS) for one sign and order."""
    if pat == 0:
        return n, list(range(1, n + 1))
    if pat == 1:
        return n, [-v for v in range(1, n + 1)]
    if pat == 2:
        return n, list(range(n, 0, -1))
    rng = random.Random(f"{seed}|{tag}|{n}|{pat}")
    nv = n + rng.randint(0, 2)
    variables = rng.sample(range(1, nv + 1), n)
    return nv, [v if rng.random() < 0.5 else -v for v in variables]


def note_pattern(r, dims, nv):
    if any(d < 0 for d in dims):
        r.c["inputs.some_negated"] += 1
    if any(d < 0 for d in dims) and any(d > 0 for d in dims):
        r.c["inputs.mixed_signs"] += 1
    if [abs(d) for d in dims] != sorted(abs(d) for d in dims):
        r.c["inputs.out_of_order"] += 1
    if nv > len({abs(d) for d in dims}):
        r.c["inputs.with_bystander_variables"] += 1


def to_dimacs_clauses(clauses):
    return [[to_dimacs(l) for l in c] for c in clauses]


def fresh_cnf(nv, dims):
    f = CNF()
    for _ in range(nv):
        f.new_var()
    return f, [from_dimacs(d) for d in dims]


def input_variables(dims):
    return sorted({abs(d) for d in dims})


def true_count(dims, values):
    return sum(1 for d in dims if values[abs(d)] == (d > 0))


def expected_set(variables, dims, pred):
    out = set()
    for bits in itertools.product((False, True), repeat=len(variables)):
        if pred(true_count(dims, dict(zip(variables, bits)))):
            out.add(bits)
    return out


def sample(items, limit=3):
    return [list(x) for x in sorted(items)[:limit]]


def judge(r, kind, clauses, variables, expected, label=None, **detail):
    """The check every encoding goes through: the same set, not just the same size."""
    got = dpll.projected_models(clauses, variables)
    r.steps += 2 ** len(variables)
    r.c["checks.projected_sets"] += 1
    r.c["checks.assignments_judged"] += 2 ** len(variables)
    if got != expected:
        r.mismatch(kind, label, variables=variables,
                   same_count=len(got) == len(expected),
                   expected_count=len(expected), got_count=len(got),
                   missing=sample(expected - got), spurious=sample(got - expected), **detail)
        return False
    return True


def call(impl, fn, target, lits, k, method):
    if fn == "at_least_one":
        impl.at_least_one(target, lits)
    elif fn in ("at_most_one", "exactly_one"):
        getattr(impl, fn)(target, lits, method)
    else:
        getattr(impl, fn)(target, lits, k, method)


def call_encoder(enc, fn, lits, k, method):
    if fn == "at_least_one":
        enc.at_least_one(lits)
    elif fn in ("at_most_one", "exactly_one"):
        getattr(enc, fn)(lits, method)
    else:
        getattr(enc, fn)(lits, k, method)


def model_is_good(model, clauses, variables, dims, expected):
    """A model must satisfy every clause and its inputs must be a legal assignment."""
    needed = max((abs(l) for c in clauses for l in c), default=0)
    if model is None or len(model) < needed:
        return False
    for c in clauses:
        if not any(model[abs(l) - 1] == (l > 0) for l in c):
            return False
    return tuple(model[v - 1] for v in variables) in expected


def check_engines(r, f, clauses, variables, dims, expected, detail):
    """The encoded formula through the solvers. Their answers are judged, not trusted."""
    runs = [
        ("python", lambda: solve(f)),
        ("native", lambda: solve_adaptive(f, engine="native")),
        ("native_preprocessed", lambda: solve_adaptive(f, engine="native", always_preprocess=True)),
        ("python_preprocessed", lambda: solve_adaptive(f, engine="python", always_preprocess=True)),
    ]
    for name, run in runs:
        try:
            res = run()
        except (KeyboardInterrupt, SystemExit):
            raise
        except BaseException as e:  # noqa: BLE001 - a Rust panic is a BaseException
            known = "preprocess-2" if name.endswith("_preprocessed") and [] in clauses else None
            r.c["engines.crashed"] += 1
            r.mismatch("engine_crash", known, engine=name, error=repr(e), clauses=clauses, **detail)
            continue
        sat, model = res if isinstance(res, tuple) else (res.sat, res.model)
        r.steps += 1
        r.c[f"engines.{name}.{'sat' if sat else 'unsat'}"] += 1
        if sat is None or bool(sat) != bool(expected):
            r.mismatch("engine_wrong_answer", None, engine=name, sat=sat, clauses=clauses, **detail)
        elif sat and not model_is_good(model, clauses, variables, dims, expected):
            r.mismatch("engine_bad_model", None, engine=name, model=model, clauses=clauses, **detail)


def check_with_oracle(r, clauses, variables, expected, nvars, n, detail):
    if nvars > oracle.MAX_VARS:
        r.c["oracle.past_its_limit"] += 1
        return
    answer = oracle.satisfiable(clauses)
    r.steps += 1
    r.c["oracle.satisfiable_calls"] += 1
    if answer != bool(expected):
        r.mismatch("oracle_disagrees", None, oracle_says=answer, clauses=clauses, **detail)
    if n > 6 or nvars > 12:
        return
    r.c["oracle.projected_sets"] += 1
    for bits in itertools.product((False, True), repeat=len(variables)):
        units = [[v if b else -v] for v, b in zip(variables, bits)]
        if oracle.satisfiable(clauses + units) != (bits in expected):
            r.mismatch("oracle_projection", None, bits=list(bits), clauses=clauses, **detail)
            break


def check_solver_sink(r, impl, fn, nv, dims, k, method, expected, variables, detail):
    """Encode into a Solver and put every input assignment to it as assumptions."""
    s = Solver()
    for _ in range(nv):
        s.new_var()
    lits = [from_dimacs(d) for d in dims]
    call(impl, fn, s, lits, k, method)
    r.c["solver_sink.cells"] += 1
    for bits in itertools.product((False, True), repeat=len(variables)):
        assumptions = [from_dimacs(v if b else -v) for v, b in zip(variables, bits)]
        got = s.solve(assumptions)
        r.steps += 1
        r.c["solver_sink.solves"] += 1
        if bool(got) != (bits in expected):
            r.mismatch("solver_sink", None, bits=list(bits), got=got, **detail)
            return


# --------------------------------------------------------------------------
# the grid
# --------------------------------------------------------------------------


def grid_cells(fns=FNS, max_n=MAX_N):
    for fn in fns:
        for n in range(max_n + 1):
            ks = [None] if fn.endswith("_one") else range(n + 1)
            methods = ("n/a",) if fn == "at_least_one" else ALL_METHODS
            for k in ks:
                for method in methods:
                    yield fn, n, k, method


def expects_acceptance(fn, method):
    if method == "bogus":
        return False
    if fn.endswith("_one"):
        return True
    return method in ALWAYS_ACCEPTED_K


def task_grid(impl, cfg, fn, n, k, method, pat):
    r = Report()
    tag = f"{fn}|{k}|{method}"
    nv, dims = pattern(cfg["seed"], tag, n, pat)
    detail = {"fn": fn, "n": n, "k": k, "method": method, "lits": dims}
    f, lits = fresh_cnf(nv, dims)
    cell = f"grid.{fn}.{method}"
    r.c["grid.cell_patterns"] += 1
    r.instances += 1
    if pat == 0:
        r.c["grid.cells_visited"] += 1
    note_pattern(r, dims, nv)
    try:
        call(impl, fn, f, lits, k, method)
    except ValueError as e:
        r.c[f"{cell}.rejected"] += 1
        r.c["grid.rejected_a_method"] += 1
        if expects_acceptance(fn, method):
            r.mismatch("method_rejected", None, error=str(e), **detail)
        if f.clauses or f.nvars != nv:
            if method == "bogus":
                r.c["observed.bad_method_left_clauses_behind"] += 1
            else:
                r.mismatch("partial_emission", None, clauses=to_dimacs_clauses(f.clauses), **detail)
        return r
    except Exception as e:  # noqa: BLE001 - a crash is a result
        known = "encodings-1" if (isinstance(e, RecursionError) and n == 0 and method == "totalizer") else None
        r.c["grid.crashed"] += 1
        r.mismatch("crash", known, error=type(e).__name__, **detail)
        return r
    r.c[f"{cell}.accepted"] += 1
    if method == "bogus":
        r.c["observed.bad_method_accepted"] += 1
    clauses = to_dimacs_clauses(f.clauses)
    variables = input_variables(dims)
    expected = expected_set(variables, dims, lambda s: PRED[fn](s, k))
    if fn.endswith("_k"):
        if k == 0:
            r.c["grid.k_is_0"] += 1
        if k == n:
            r.c["grid.k_is_n"] += 1
        if k == 1:
            r.c["grid.k_is_1"] += 1
    if n == 0:
        r.c["grid.n_is_0"] += 1
    if n == MAX_N:
        r.c["grid.n_is_10"] += 1
    if not expected:
        r.c["grid.no_solutions"] += 1
    if len(expected) == 2 ** len(variables):
        r.c["grid.all_solutions"] += 1
    if f.nvars > n:
        r.c["grid.with_auxiliary_variables"] += 1
    if f.nvars > oracle.MAX_VARS:
        r.c["grid.past_oracle_limit"] += 1
    judge(r, "wrong_solutions", clauses, variables, expected, **detail)
    mentioned = {abs(l) for c in clauses for l in c}
    bystanders = set(range(1, nv + 1)) - set(variables)
    if mentioned & bystanders:
        r.mismatch("touched_a_bystander", None, clauses=clauses, **detail)
    if cfg.get("cross_checks", True):
        check_with_oracle(r, clauses, variables, expected, f.nvars, n, detail)
        check_engines(r, f, clauses, variables, dims, expected, detail)
        f2, lits2 = fresh_cnf(nv, dims)
        try:
            call_encoder(Encoder(f2), fn, lits2, k, method if method != "n/a" else "auto")
            same_path = f2.clauses == f.clauses
        except ValueError:
            same_path = False
        if not same_path:
            r.mismatch("encoder_path_differs", None, **detail)
        r.c["checks.encoder_path_identical"] += 1
        if pat == FIXED_PATTERNS or n <= SOLVER_SINK_ALL_PATTERNS_N:
            check_solver_sink(r, impl, fn, nv, dims, k, method, expected, variables, detail)
    return r


# --------------------------------------------------------------------------
# totalizer
# --------------------------------------------------------------------------


def build_totalizer(impl, nv, dims, m):
    f, lits = fresh_cnf(nv, dims)
    enc = Encoder(f)
    return f, enc, impl.Totalizer(enc, lits, max_count=m)


def task_totalizer(impl, cfg, n, pat, m):
    """Bounds tightened in sequence on one object, judged after every step."""
    r = Report()
    nv, dims = pattern(cfg["seed"], f"tot|{m}", n, pat)
    variables = input_variables(dims)
    detail = {"n": n, "max_count": m, "lits": dims}
    note_pattern(r, dims, nv)
    r.instances += 1
    try:
        f, enc, t = build_totalizer(impl, nv, dims, m)
    except RecursionError:
        r.mismatch("crash", "encodings-1" if n == 0 else None, error="RecursionError", **detail)
        return r
    cut = len(t.outputs)
    full = cut >= n
    r.c["totalizer.objects_full" if full else "totalizer.objects_truncated"] += 1

    # at-most, tightened from the top on one object
    top = n + 1 if full else cut - 1
    for k in range(top, -2, -1):
        t.assert_at_most(k)
        r.c["totalizer.at_most_tightenings"] += 1
        if k < 0:
            r.c["totalizer.at_most_below_zero"] += 1
        judge(r, "totalizer_at_most", to_dimacs_clauses(f.clauses), variables,
              expected_set(variables, dims, lambda s: s <= k), k=k, **detail)

    # at-least, tightened from the bottom on a fresh object
    f, enc, t = build_totalizer(impl, nv, dims, m)
    top = n + 1 if full else cut
    for k in range(-1, top + 1):
        t.assert_at_least(k)
        r.c["totalizer.at_least_tightenings"] += 1
        judge(r, "totalizer_at_least", to_dimacs_clauses(f.clauses), variables,
              expected_set(variables, dims, lambda s: s >= k), k=k, **detail)

    # both ends closing in, in a seeded order
    f, enc, t = build_totalizer(impl, nv, dims, m)
    rng = random.Random(f"{cfg['seed']}|window|{n}|{pat}|{m}")
    lo, hi = 0, n
    ceiling = n if full else cut - 1
    while lo <= hi:
        if rng.random() < 0.5:
            hi = min(hi, ceiling) - rng.randint(0, 2)
            t.assert_at_most(hi)
        else:
            if lo >= cut:
                break
            lo += rng.randint(0, 2)
            lo = min(lo, cut)
            t.assert_at_least(lo)
        r.c["totalizer.window_steps"] += 1
        low, high = lo, hi
        judge(r, "totalizer_window", to_dimacs_clauses(f.clauses), variables,
              expected_set(variables, dims, lambda s: low <= s <= high), lo=low, hi=high, **detail)

    # past the cut: a single bound each, on a fresh object
    if not full:
        for k in range(cut, n):
            f, enc, t = build_totalizer(impl, nv, dims, m)
            t.assert_at_most(k)
            r.c["totalizer.past_cut_at_most"] += 1
            judge(r, "totalizer_past_cut_at_most", to_dimacs_clauses(f.clauses), variables,
                  expected_set(variables, dims, lambda s: s <= k), label="encodings-2", k=k, **detail)
        for k in range(cut + 1, n + 1):
            f, enc, t = build_totalizer(impl, nv, dims, m)
            t.assert_at_least(k)
            r.c["totalizer.past_cut_at_least"] += 1
            judge(r, "totalizer_past_cut_at_least", to_dimacs_clauses(f.clauses), variables,
                  expected_set(variables, dims, lambda s: s >= k), label="encodings-2", k=k, **detail)
    return r


def task_totalizer_outputs(impl, cfg, n, pat, m):
    """out[i] is true iff at least i+1 inputs are, and neither value is free."""
    r = Report()
    nv, dims = pattern(cfg["seed"], f"totout|{m}", n, pat)
    variables = input_variables(dims)
    detail = {"n": n, "max_count": m, "lits": dims}
    r.instances += 1
    f, _, t = build_totalizer(impl, nv, dims, m)
    clauses = to_dimacs_clauses(f.clauses)
    outs = [to_dimacs(o) for o in t.outputs]
    r.c["totalizer.output_objects"] += 1
    for bits in itertools.product((False, True), repeat=len(variables)):
        units = [[v if b else -v] for v, b in zip(variables, bits)]
        count = true_count(dims, dict(zip(variables, bits)))
        base = clauses + units
        for i, o in enumerate(outs):
            want = o if count >= i + 1 else -o
            r.steps += 2
            r.c["totalizer.output_values"] += 1
            if not dpll.satisfiable(base + [[want]]) or dpll.satisfiable(base + [[-want]]):
                r.mismatch("totalizer_output", None, bits=list(bits), output=i, count=count, **detail)
                return r
    return r


def task_totalizer_solver(impl, cfg, n, pat, m):
    """On a Solver: bounds as assumptions, retracted, then made permanent."""
    r = Report()
    nv, dims = pattern(cfg["seed"], f"totsolver|{m}", n, pat)
    variables = input_variables(dims)
    detail = {"n": n, "max_count": m, "lits": dims}
    r.instances += 1
    s = Solver()
    for _ in range(nv):
        s.new_var()
    enc = Encoder(s)
    t = impl.Totalizer(enc, [from_dimacs(d) for d in dims], max_count=m)
    cut = len(t.outputs)
    full = cut >= n

    def sweep(kind, pred, extra=()):
        for bits in itertools.product((False, True), repeat=len(variables)):
            assumptions = [from_dimacs(v if b else -v) for v, b in zip(variables, bits)] + list(extra)
            want = pred(true_count(dims, dict(zip(variables, bits))))
            r.steps += 1
            r.c["totalizer.solver_solves"] += 1
            if bool(s.solve(assumptions)) != want:
                r.mismatch(kind, None, bits=list(bits), **detail)
                return

    for k in range(cut - 1, -2, -1):
        lit = t.at_most_lit(k)
        sweep("totalizer_assumption_at_most", lambda c: c <= k, [] if lit is None else [lit])
        r.c["totalizer.assumed_at_most"] += 1
    for k in range(0, cut + 1):
        lit = t.at_least_lit(k)
        sweep("totalizer_assumption_at_least", lambda c: c >= k, [] if lit is None else [lit])
        r.c["totalizer.assumed_at_least"] += 1
    sweep("totalizer_assumption_not_retracted", lambda c: True)
    r.c["totalizer.retracted"] += 1
    for k in range(n if full else cut - 1, -1, -1):
        t.assert_at_most(k)
        sweep("totalizer_permanent_at_most", lambda c: c <= k)
        r.c["totalizer.permanent_at_most"] += 1
    return r


def task_amk_totalizer(impl, cfg, n, pat, k):
    """The object amk_totalizer returns, tightened below the bound it was built for."""
    r = Report()
    nv, dims = pattern(cfg["seed"], f"amk|{k}", n, pat)
    variables = input_variables(dims)
    detail = {"n": n, "k": k, "lits": dims}
    r.instances += 1
    f, lits = fresh_cnf(nv, dims)
    enc = Encoder(f)
    try:
        t = enc.amk_totalizer(lits, k)
    except RecursionError:
        r.mismatch("crash", "encodings-1" if n == 0 else None, error="RecursionError", **detail)
        return r
    judge(r, "amk_totalizer", to_dimacs_clauses(f.clauses), variables,
          expected_set(variables, dims, lambda s: s <= k), **detail)
    for k2 in range(k - 1, -2, -1):
        t.assert_at_most(k2)
        r.c["totalizer.amk_tightenings"] += 1
        judge(r, "amk_totalizer_tightened", to_dimacs_clauses(f.clauses), variables,
              expected_set(variables, dims, lambda s: s <= k2), tightened_to=k2, **detail)
    return r


# --------------------------------------------------------------------------
# optimise
# --------------------------------------------------------------------------


def random_problem(seed, idx):
    rng = random.Random(f"{seed}|opt|{idx}")
    n = rng.randint(0, MAX_N)
    density = rng.choice((0, 0.5, 1, 2, 3, 4, 6))
    base = []
    if n:
        for _ in range(int(density * n)):
            width = rng.randint(1, 3) if density >= 1 else rng.randint(2, 3)
            base.append([rng.choice((1, -1)) * rng.randint(1, n) for _ in range(width)])
    mode = rng.choice(("distinct", "distinct", "distinct", "repeats", "complements"))
    size = rng.randint(0, n) if n else 0
    if mode == "distinct" or not n:
        soft = [v if rng.random() < 0.5 else -v for v in rng.sample(range(1, n + 1), size)]
    elif mode == "repeats":
        soft = [rng.choice((1, -1)) * rng.randint(1, n) for _ in range(size)]
        soft += soft[: rng.randint(0, len(soft))]
    else:
        soft = [v if rng.random() < 0.5 else -v for v in rng.sample(range(1, n + 1), size)]
        soft += [-d for d in soft[: rng.randint(0, len(soft))]]
    card = None
    if n and rng.random() < 0.3:
        card = (rng.choice(("at_most_k", "at_least_k", "exactly_k")), rng.randint(0, n),
                rng.choice(("auto", "sequential", "totalizer")))
    return n, base, soft, card


def feasible_assignments(n, base, card):
    variables = list(range(1, n + 1))
    dims = variables
    out = []
    for bits in itertools.product((False, True), repeat=n):
        values = dict(zip(variables, bits))
        if not all(any(values[abs(l)] == (l > 0) for l in c) for c in base):
            continue
        if card and not PRED[card[0]](true_count(dims, values), card[1]):
            continue
        out.append(values)
    return out


def make_solver(impl, n, base, card):
    s = Solver()
    for _ in range(n):
        s.new_var()
    for c in base:
        s.add_clause_dimacs(c)
    if card:
        getattr(Real, card[0])(s, [from_dimacs(v) for v in range(1, n + 1)], card[1], card[2])
    return s


def model_counts(model, n, base, card, soft):
    """The true soft count of a model, or None when it is not a model at all."""
    if model is None or len(model) < n:
        return None
    values = {v: model[v - 1] for v in range(1, n + 1)}
    if not all(any(values[abs(l)] == (l > 0) for l in c) for c in base):
        return None
    if card and not PRED[card[0]](true_count(list(range(1, n + 1)), values), card[1]):
        return None
    return true_count(soft, values)


def task_optimise(impl, cfg, idx):
    r = Report()
    n, base, soft, card = random_problem(cfg["seed"], idx)
    detail = {"idx": idx, "n": n, "base": base, "soft": soft, "card": card}
    r.instances += 1
    feasible = feasible_assignments(n, base, card)
    if not card:
        answer = oracle.satisfiable(base)
        r.steps += 1
        r.c["optimise.oracle_calls"] += 1
        if answer != bool(feasible):
            r.mismatch("oracle_disagrees", None, oracle_says=answer, **detail)
    counts = [true_count(soft, v) for v in feasible]
    r.c["optimise.sat" if feasible else "optimise.unsat"] += 1
    if not soft:
        r.c["optimise.no_soft_literals"] += 1
    if len(soft) != len({abs(d) for d in soft}):
        r.c["optimise.repeated_soft_variables"] += 1
    if card:
        r.c["optimise.with_cardinality"] += 1
    int_soft = [from_dimacs(d) for d in soft]

    for minimise, assumption_based in itertools.product((True, False), repeat=2):
        d = dict(detail, minimise=minimise, assumption_based=assumption_based)
        best = (min(counts) if minimise else max(counts)) if counts else None
        s = make_solver(impl, n, base, card)
        seen = []
        res = impl.optimise(s, int_soft, minimise=minimise, assumption_based=assumption_based,
                            on_improve=lambda c, m: seen.append((c, list(m))))
        r.steps += 1
        r.c[f"optimise.{'min' if minimise else 'max'}.{'assume' if assumption_based else 'permanent'}"] += 1
        if res is None:
            if best is not None:
                r.mismatch("optimise_none_on_sat", None, optimum=best, **d)
            continue
        if best is None:
            r.mismatch("optimise_answer_on_unsat", None, result=res[0], **d)
            continue
        value, model = res
        actual = model_counts(model, n, base, card, soft)
        if actual is None:
            r.mismatch("optimise_bad_model", None, value=value, **d)
        elif actual != value:
            r.mismatch("optimise_count_is_not_the_models", None, value=value, actual=actual, **d)
        if value != best:
            r.mismatch("optimise_not_optimal", None, value=value, optimum=best, **d)
            continue
        if len(seen) > 1:
            r.c["optimise.improved_more_than_once"] += 1
        # intermediate models are real, in the counted direction, and strictly improve
        total = len(soft)
        last = None
        for c, m in seen:
            a = model_counts(m, n, base, card, soft)
            counted = a if minimise else (None if a is None else total - a)
            if a is None or counted != c or (last is not None and c >= last):
                r.mismatch("optimise_on_improve", None, reported=c, actual=a, previous=last, **d)
                break
            last = c
        if not minimise and seen:
            r.c["observed.maximise_on_improve_reports_false_count"] += 1
    if cfg.get("optimiser_class", True):
        check_optimiser(r, impl, n, base, soft, card, counts, detail)
    return r


def check_optimiser(r, impl, n, base, soft, card, counts, detail):
    int_soft = [from_dimacs(d) for d in soft]
    total = len(soft)
    no_soft = None if soft else "encodings-6"
    for minimise in (True, False):
        d = dict(detail, minimise=minimise)
        counted_values = [c if minimise else total - c for c in counts]
        optimum = min(counted_values) if counted_values else None
        report = (lambda c: c) if minimise else (lambda c: total - c)

        # run(target=t) on a fresh object: the optimum when t allows it, else None
        for t in range(-1, total + 2):
            s = make_solver(impl, n, base, card)
            opt = impl.Optimiser(s, int_soft, minimise=minimise)
            res = opt.run(target=t)
            r.steps += 1
            r.c["optimiser.target_runs"] += 1
            want = None if optimum is None or optimum > t else report(optimum)
            if want is None:
                r.c["optimiser.target_too_strong"] += 1
            got = None if res is None else res[0]
            if got != want:
                r.mismatch("optimiser_target", no_soft, target=t, got=got, want=want, **d)
            # an assumed bound must not outlive its solve
            again = opt.solve_with_bound(None)
            if (again is not None) != (optimum is not None):
                r.mismatch("optimiser_bound_outlived_its_solve", None, target=t, **d)

        # solve_with_bound against every bound, assumed
        s = make_solver(impl, n, base, card)
        opt = impl.Optimiser(s, int_soft, minimise=minimise)
        for b in range(-1, total + 2):
            m = opt.solve_with_bound(b)
            r.steps += 1
            r.c["optimiser.bounds_assumed"] += 1
            feasible = optimum is not None and optimum <= b
            if (m is not None) != feasible:
                r.mismatch("optimiser_bound", no_soft, bound=b, got=m is not None, want=feasible, **d)
            elif m is not None and opt.count(m) > b:
                r.mismatch("optimiser_bound_ignored", None, bound=b, count=opt.count(m), **d)

        # the same, permanent and descending
        s = make_solver(impl, n, base, card)
        opt = impl.Optimiser(s, int_soft, minimise=minimise)
        for b in range(total, -2, -1):
            m = opt.solve_with_bound(b, permanent=True)
            r.steps += 1
            r.c["optimiser.bounds_permanent"] += 1
            feasible = optimum is not None and optimum <= b
            if (m is not None) != feasible:
                r.mismatch("optimiser_permanent_bound", no_soft, bound=b, got=m is not None, want=feasible, **d)

        if optimum is None:
            continue

        # one step, then resume; the docstring's own pattern
        s = make_solver(impl, n, base, card)
        opt = impl.Optimiser(s, int_soft, minimise=minimise)
        opt.run(max_iterations=1)
        first = opt.best[0]
        if first > optimum:
            r.c["optimiser.stopped_early_above_optimum"] += 1
        opt.run(target=first - 1)
        r.steps += 1
        r.c["optimiser.resumed"] += 1
        if opt.best[0] != optimum:
            r.mismatch("optimiser_resume", None, best=opt.best[0], optimum=optimum, **d)

        # stopping early must leave the best found, whatever later runs do
        before = opt.best[0]
        opt.run(max_iterations=1)
        r.steps += 1
        r.c["optimiser.loose_rerun"] += 1
        if opt.best[0] > before:
            r.c["optimiser.best_got_worse"] += 1
            r.mismatch("optimiser_best_got_worse", "encodings-5", before=before, after=opt.best[0],
                       optimum=optimum, **d)
        actual = model_counts(opt.best[1], n, base, card, soft)
        if actual is None or (actual if minimise else total - actual) != opt.best[0]:
            r.mismatch("optimiser_best_is_inconsistent", None, best=opt.best[0], actual=actual, **d)


# --------------------------------------------------------------------------
# off the grid
# --------------------------------------------------------------------------


def task_k_out_of_range(impl, cfg, fn, n, k, method):
    r = Report()
    nv, dims = pattern(cfg["seed"], f"kout|{fn}|{k}|{method}", n, FIXED_PATTERNS)
    detail = {"fn": fn, "n": n, "k": k, "method": method, "lits": dims}
    r.instances += 1
    f, lits = fresh_cnf(nv, dims)
    r.c["off_grid.k_below_0" if k < 0 else "off_grid.k_above_n"] += 1
    try:
        call(impl, fn, f, lits, k, method)
    except ValueError:
        r.c["off_grid.k_out_of_range_rejected"] += 1
        return r
    except RecursionError:
        r.mismatch("crash", "encodings-1" if n == 0 else None, error="RecursionError", **detail)
        return r
    variables = input_variables(dims)
    label = "encodings-3" if k < 0 and fn in ("at_most_k", "exactly_k") else None
    judge(r, "k_out_of_range", to_dimacs_clauses(f.clauses), variables,
          expected_set(variables, dims, lambda s: PRED[fn](s, k)), label=label, **detail)
    return r


def task_repeats(impl, cfg, idx):
    """Repeated and complementary inputs, counted with their multiplicity."""
    r = Report()
    rng = random.Random(f"{cfg['seed']}|rep|{idx}")
    n = rng.randint(2, 7)
    m = rng.randint(1, max(1, n - 1))
    dims = [rng.choice((1, -1)) * rng.randint(1, m) for _ in range(n)]
    fn = rng.choice(FNS)
    k = None if fn.endswith("_one") else rng.randint(0, n)
    method = rng.choice(AMO_METHODS)
    detail = {"fn": fn, "n": n, "k": k, "method": method, "lits": dims}
    r.instances += 1
    nv = m
    f, lits = fresh_cnf(nv, dims)
    if len({abs(d) for d in dims}) < n:
        r.c["off_grid.repeated_variable"] += 1
    if any(-d in dims for d in dims):
        r.c["off_grid.complementary_inputs"] += 1
    try:
        call(impl, fn, f, lits, k, method)
    except ValueError:
        r.c["off_grid.repeats_rejected"] += 1
        return r
    variables = input_variables(dims)
    judge(r, "repeated_inputs", to_dimacs_clauses(f.clauses), variables,
          expected_set(variables, dims, lambda s: PRED[fn](s, k)), **detail)
    return r


def task_direct(impl, cfg, name, n, arg, pat):
    """The amo_* and amk_* methods, called by name."""
    r = Report()
    nv, dims = pattern(cfg["seed"], f"direct|{name}|{arg}", n, pat)
    detail = {"name": name, "n": n, "arg": arg, "lits": dims}
    r.instances += 1
    f, lits = fresh_cnf(nv, dims)
    enc = Encoder(f)
    variables = input_variables(dims)
    r.c[f"direct.{name}"] += 1
    try:
        if name == "amo_commander":
            enc.amo_commander(lits, arg)
            k = 1
        elif name in ("amo_pairwise", "amo_binary"):
            getattr(enc, name)(lits)
            k = 1
        else:
            getattr(enc, name)(lits, arg)
            k = arg
    except RecursionError:
        r.mismatch("crash", "encodings-1" if n == 0 else None, error="RecursionError", **detail)
        return r
    judge(r, "direct_method", to_dimacs_clauses(f.clauses), variables,
          expected_set(variables, dims, lambda s: s <= k), **detail)
    return r


def task_stacked(impl, cfg, idx):
    """Two constraints in one formula, the second's inputs declared after the first's aux."""
    r = Report()
    rng = random.Random(f"{cfg['seed']}|stack|{idx}")
    f = CNF()
    enc = Encoder(f)
    all_dims = []
    preds = []
    detail = {"idx": idx, "constraints": []}
    pool = []
    for _ in range(2):
        pool += [f.new_var() + 1 for _ in range(rng.randint(1, 3))]
        chosen = rng.sample(pool, rng.randint(1, min(len(pool), 5)))
        dims = [v if rng.random() < 0.5 else -v for v in chosen]
        fn = rng.choice(FNS)
        k = None if fn.endswith("_one") else rng.randint(0, len(dims))
        method = rng.choice(("auto", "sequential", "totalizer"))
        call_encoder(enc, fn, [from_dimacs(d) for d in dims], k, method)
        preds.append((dims, fn, k))
        all_dims.extend(dims)
        detail["constraints"].append({"fn": fn, "k": k, "method": method, "lits": dims})
    variables = sorted(pool)
    expected = set()
    for bits in itertools.product((False, True), repeat=len(variables)):
        values = dict(zip(variables, bits))
        if all(PRED[fn](true_count(dims, values), k) for dims, fn, k in preds):
            expected.add(bits)
    r.instances += 1
    r.c["off_grid.stacked"] += 1
    clauses = to_dimacs_clauses(f.clauses)
    if not expected:
        r.c["off_grid.stacked_unsat"] += 1
    judge(r, "stacked", clauses, variables, expected, **detail)
    # the grid's only UNSAT cells are at n = 0, so this is where the solvers get refutations
    check_engines(r, f, clauses, variables, all_dims, expected, detail)
    return r


def task_undeclared(impl, cfg, fn, n, k, method, sink):
    """Inputs the sink has not seen yet: CNF.add and Solver.add_clause both grow on sight."""
    r = Report()
    dims = list(range(1, n + 1))
    variables = dims
    detail = {"fn": fn, "n": n, "k": k, "method": method, "sink": sink, "lits": dims}
    r.instances += 1
    lits = [from_dimacs(d) for d in dims]
    expected = expected_set(variables, dims, lambda s: PRED[fn](s, k))
    r.c[f"off_grid.undeclared_{sink}"] += 1
    if sink == "cnf":
        f = CNF()
        call(impl, fn, f, lits, k, method)
        judge(r, "undeclared_inputs", to_dimacs_clauses(f.clauses), variables, expected,
              label="encodings-4", **detail)
        return r
    s = Solver()
    call(impl, fn, s, lits, k, method)
    s.ensure_vars(n)
    for bits in itertools.product((False, True), repeat=n):
        assumptions = [from_dimacs(v if b else -v) for v, b in zip(variables, bits)]
        r.steps += 1
        if bool(s.solve(assumptions)) != (bits in expected):
            r.mismatch("undeclared_inputs", "encodings-4", bits=list(bits), **detail)
            return r
    return r


def task_root_fixed(impl, cfg, idx):
    """A Solver sink with some inputs fixed at the root, or solved before encoding."""
    r = Report()
    rng = random.Random(f"{cfg['seed']}|root|{idx}")
    n = rng.randint(1, 7)
    dims = [v if rng.random() < 0.5 else -v for v in rng.sample(range(1, n + 1), n)]
    fn = rng.choice(FNS)
    k = None if fn.endswith("_one") else rng.randint(0, n)
    method = rng.choice(("auto", "sequential", "totalizer"))
    fixed = [v if rng.random() < 0.5 else -v for v in rng.sample(range(1, n + 1), rng.randint(0, n))]
    solved_first = rng.random() < 0.5
    detail = {"fn": fn, "n": n, "k": k, "method": method, "lits": dims, "fixed": fixed,
              "solved_first": solved_first}
    r.instances += 1
    r.c["off_grid.root_fixed"] += 1
    s = Solver()
    for _ in range(n):
        s.new_var()
    for u in fixed:
        s.add_clause_dimacs([u])
    if solved_first:
        s.solve()
        r.c["off_grid.encoded_after_a_solve"] += 1
    call(impl, fn, s, [from_dimacs(d) for d in dims], k, method)
    variables = list(range(1, n + 1))
    for bits in itertools.product((False, True), repeat=n):
        values = dict(zip(variables, bits))
        want = (PRED[fn](true_count(dims, values), k)
                and all(values[abs(u)] == (u > 0) for u in fixed))
        r.steps += 1
        got = s.solve([from_dimacs(v if b else -v) for v, b in zip(variables, bits)])
        if bool(got) != want:
            r.mismatch("root_fixed", None, bits=list(bits), got=got, want=want, **detail)
            return r
    return r


def task_arc_consistency(impl, cfg, fn, n, k, method):
    """The module's table says GAC. Unit propagation must fix what the constraint fixes."""
    r = Report()
    nv, dims = pattern(cfg["seed"], f"gac|{fn}|{k}|{method}", n, FIXED_PATTERNS)
    detail = {"fn": fn, "n": n, "k": k, "method": method, "lits": dims}
    f, lits = fresh_cnf(nv, dims)
    r.instances += 1
    call(impl, fn, f, lits, k, method)
    clauses = to_dimacs_clauses(f.clauses)
    r.c["arc_consistency.cells"] += 1
    is_at_most = fn in ("at_most_k", "at_most_one")
    bound = 1 if fn == "at_most_one" else k
    if not is_at_most:
        # sum(lits) >= k is sum(~lits) <= n - k; track the literals that count
        bound = n - k
    counted = dims if is_at_most else [-d for d in dims]
    for states in itertools.product((None, True, False), repeat=n):
        assumed = [d if st else -d for d, st in zip(dims, states) if st is not None]
        trues = sum(1 for d in counted if d in assumed)
        conflict, assigned = oracle.propagate(clauses, assumed)
        r.steps += 1
        r.c["arc_consistency.partial_assignments"] += 1
        if trues > bound:
            if not conflict:
                r.mismatch("not_arc_consistent", None, assumed=assumed, want="conflict", **detail)
                return r
            continue
        if conflict:
            r.mismatch("not_arc_consistent", None, assumed=assumed, want="no conflict", **detail)
            return r
        if trues == bound:
            r.c["arc_consistency.at_the_bound"] += 1
            missing = [-d for d in counted if d not in assumed and -d not in assumed and -d not in assigned]
            if missing:
                r.mismatch("not_arc_consistent", None, assumed=assumed, not_fixed=missing, **detail)
                return r
    return r


# --------------------------------------------------------------------------
# running
# --------------------------------------------------------------------------


TASKS = {
    "grid": task_grid,
    "totalizer": task_totalizer,
    "totalizer_outputs": task_totalizer_outputs,
    "totalizer_solver": task_totalizer_solver,
    "amk_totalizer": task_amk_totalizer,
    "optimise": task_optimise,
    "k_out_of_range": task_k_out_of_range,
    "repeats": task_repeats,
    "direct": task_direct,
    "stacked": task_stacked,
    "undeclared": task_undeclared,
    "root_fixed": task_root_fixed,
    "arc_consistency": task_arc_consistency,
}


def run_task(task):
    impl_name, cfg, name, args = task
    impl = IMPLS[impl_name]
    try:
        r = TASKS[name](impl, cfg, *args)
    except (KeyboardInterrupt, SystemExit):
        raise
    except BaseException as e:  # noqa: BLE001 - never lose a crash to the pool
        r = Report()
        r.mismatch("harness_or_library_crash", None, task=name, args=list(args), error=repr(e))
    return dict(r.c), r.bad, r.steps, r.instances


def build_tasks(impl_name, cfg, instances, opt_instances, sections, fns=FNS, max_patterns=None):
    tasks = []

    def add(name, *args):
        tasks.append((impl_name, cfg, name, args))

    patterns = FIXED_PATTERNS + instances
    if max_patterns is not None:
        patterns = min(patterns, max_patterns)
    if "grid" in sections:
        for fn, n, k, method in grid_cells(fns):
            for pat in range(patterns):
                add("grid", fn, n, k, method, pat)
    if "totalizer" in sections:
        for n in range(MAX_N + 1):
            for pat in range(patterns):
                add("totalizer", n, pat, None)
                # every truncation on the first patterns, and at every n
                if pat in (0, FIXED_PATTERNS):
                    for m in range(0, n):
                        add("totalizer", n, pat, m)
        for n in range(MAX_N + 1):
            for k in range(n + 1):
                add("amk_totalizer", n, FIXED_PATTERNS, k)
    if "totalizer_outputs" in sections:
        for n in range(1, MAX_N + 1):
            add("totalizer_outputs", n, FIXED_PATTERNS, None)
            if n <= 8:
                for m in range(1, n):
                    add("totalizer_outputs", n, FIXED_PATTERNS, m)
    if "totalizer_solver" in sections:
        for n in range(1, 8):
            add("totalizer_solver", n, FIXED_PATTERNS, None)
            for m in range(1, n):
                add("totalizer_solver", n, FIXED_PATTERNS, m)
    if "optimise" in sections:
        for i in range(opt_instances):
            add("optimise", i)
    if "off_grid" in sections:
        for fn in ("at_most_k", "at_least_k", "exactly_k"):
            for n in range(0, 7):
                for k in (-2, -1, n + 1, n + 2):
                    for method in ALL_METHODS:
                        add("k_out_of_range", fn, n, k, method)
        for i in range(400):
            add("repeats", i)
        for n in range(0, 9):
            add("direct", "amo_pairwise", n, None, FIXED_PATTERNS)
            add("direct", "amo_binary", n, None, FIXED_PATTERNS)
            for group in range(2, n + 2):
                add("direct", "amo_commander", n, group, FIXED_PATTERNS)
            for k in range(-1, n + 2):
                add("direct", "amk_sequential", n, k, FIXED_PATTERNS)
                add("direct", "amk_totalizer", n, k, FIXED_PATTERNS)
        for i in range(400):
            add("stacked", i)
        for n in range(1, 9):
            for method in ("auto", "binary", "commander", "sequential", "totalizer"):
                for sink in ("cnf", "solver"):
                    add("undeclared", "at_most_one", n, None, method, sink)
            for k in range(0, n + 1):
                for method in ("auto", "sequential", "totalizer"):
                    for sink in ("cnf", "solver"):
                        add("undeclared", "at_most_k", n, k, method, sink)
        for i in range(400):
            add("root_fixed", i)
    if "arc_consistency" in sections:
        for n in range(0, 7):
            for method in ("pairwise", "binary", "commander", "sequential", "totalizer"):
                if n == 0 and method == "totalizer":
                    continue        # encodings-1, counted by the grid
                add("arc_consistency", "at_most_one", n, None, method)
            for k in range(0, n + 1):
                for method in ("sequential", "totalizer"):
                    add("arc_consistency", "at_most_k", n, k, method)
                    add("arc_consistency", "at_least_k", n, k, method)
    return tasks


def execute(tasks, pool):
    counts = collections.Counter()
    bad = []
    steps = 0
    instances = 0
    results = pool.imap_unordered(run_task, tasks, chunksize=8) if pool else map(run_task, tasks)
    for c, b, s, i in results:
        counts.update(c)
        bad.extend(b)
        steps += s
        instances += i
    return counts, bad, steps, instances


ALL_SECTIONS = ("grid", "totalizer", "totalizer_outputs", "totalizer_solver", "optimise",
                "off_grid", "arc_consistency")


def required_categories(sections):
    req = []
    if "grid" in sections:
        for fn in FNS:
            if fn == "at_least_one":
                req.append("grid.at_least_one.n/a.accepted")
            elif fn.endswith("_one"):
                req.extend(f"grid.{fn}.{m}.accepted" for m in AMO_METHODS)
            else:
                req.extend(f"grid.{fn}.{m}.accepted" for m in AMO_METHODS)
                req.append(f"grid.{fn}.bogus.rejected")
                req.append(f"grid.{fn}.pairwise.rejected")
        req += ["grid.k_is_0", "grid.k_is_1", "grid.k_is_n", "grid.n_is_0", "grid.n_is_10",
                "grid.no_solutions", "grid.all_solutions", "grid.with_auxiliary_variables",
                "grid.past_oracle_limit", "grid.rejected_a_method", "inputs.some_negated",
                "inputs.mixed_signs", "inputs.out_of_order", "inputs.with_bystander_variables",
                "checks.assignments_judged", "checks.encoder_path_identical",
                "oracle.satisfiable_calls", "oracle.projected_sets", "solver_sink.solves",
                "engines.python.sat", "engines.python.unsat", "engines.native.sat",
                "engines.native.unsat", "engines.native_preprocessed.sat",
                "engines.python_preprocessed.sat"]
    if "totalizer" in sections:
        req += ["totalizer.objects_full", "totalizer.objects_truncated",
                "totalizer.at_most_tightenings", "totalizer.at_most_below_zero",
                "totalizer.at_least_tightenings", "totalizer.window_steps",
                "totalizer.past_cut_at_most", "totalizer.past_cut_at_least",
                "totalizer.amk_tightenings"]
    if "totalizer_outputs" in sections:
        req += ["totalizer.output_values"]
    if "totalizer_solver" in sections:
        req += ["totalizer.solver_solves", "totalizer.assumed_at_most", "totalizer.assumed_at_least",
                "totalizer.retracted", "totalizer.permanent_at_most"]
    if "optimise" in sections:
        req += ["optimise.sat", "optimise.unsat", "optimise.no_soft_literals",
                "optimise.repeated_soft_variables", "optimise.with_cardinality",
                "optimise.improved_more_than_once", "optimise.oracle_calls",
                "optimise.min.assume", "optimise.min.permanent", "optimise.max.assume",
                "optimise.max.permanent", "optimiser.target_runs", "optimiser.target_too_strong",
                "optimiser.bounds_assumed", "optimiser.bounds_permanent", "optimiser.resumed",
                "optimiser.stopped_early_above_optimum", "optimiser.loose_rerun"]
    if "off_grid" in sections:
        req += ["off_grid.k_below_0", "off_grid.k_above_n", "off_grid.repeated_variable",
                "off_grid.complementary_inputs", "off_grid.stacked", "off_grid.undeclared_cnf",
                "off_grid.undeclared_solver", "off_grid.root_fixed", "off_grid.encoded_after_a_solve",
                "direct.amo_commander", "direct.amk_sequential", "direct.amk_totalizer",
                "off_grid.stacked_unsat", "engines.native_preprocessed.unsat",
                "engines.python_preprocessed.unsat"]
    if "arc_consistency" in sections:
        req += ["arc_consistency.partial_assignments", "arc_consistency.at_the_bound"]
    return req


def grid_cell_count(fns=FNS):
    return sum(1 for _ in grid_cells(fns))


# --------------------------------------------------------------------------
# self-test
# --------------------------------------------------------------------------


GRID_K = dict(fns=("at_most_k",), sections=("grid",), max_patterns=FIXED_PATTERNS + 1)
CROSS_K = dict(fns=("at_most_k",), sections=("grid",), max_patterns=1, cross_checks=True)

SELF_TESTS = (
    # stub, build_tasks keyword arguments, mismatch kinds that must all appear
    ("StubAcceptAll", dict(fns=FNS, sections=("grid",), max_patterns=1), {"wrong_solutions"}),
    ("StubRejectAll", dict(fns=FNS, sections=("grid",), max_patterns=1), {"wrong_solutions"}),
    ("StubSameCount", GRID_K, {"wrong_solutions"}),
    ("StubOffByOne", GRID_K, {"wrong_solutions"}),
    ("StubOnlyK0", GRID_K, {"wrong_solutions"}),
    ("StubOnlyKn", GRID_K, {"wrong_solutions"}),
    ("StubOnlyN10", GRID_K, {"wrong_solutions"}),
    ("StubOnlyNegated", GRID_K, {"wrong_solutions"}),
    ("StubOnlyUnsorted", GRID_K, {"wrong_solutions"}),
    ("StubOnlyTotalizerMethod", GRID_K, {"wrong_solutions"}),
    ("StubBinaryN3", dict(fns=("at_most_one",), sections=("grid",), max_patterns=1), {"wrong_solutions"}),
    ("StubRejectsMethods", GRID_K, {"method_rejected"}),
    ("StubCrashes", dict(GRID_K, max_patterns=1), {"crash"}),
    # the cross-checks must fire too: a wrong formula gets past no judge of its own
    # at_least_k here, because the solver's default all-false model is legal for at_most_k
    ("StubAcceptAll", dict(CROSS_K, fns=("at_least_k",)),
     {"wrong_solutions", "engine_bad_model", "oracle_projection", "solver_sink",
      "encoder_path_differs"}),
    ("StubRejectAll", CROSS_K, {"wrong_solutions", "engine_wrong_answer", "oracle_disagrees",
                                "oracle_projection", "solver_sink", "encoder_path_differs"}),
    ("StubTotalizerNoop", dict(sections=("totalizer",), max_patterns=1), {"totalizer_at_most"}),
    ("StubTotalizerSecond", dict(sections=("totalizer",), max_patterns=1), {"totalizer_at_most"}),
    ("StubTotalizerShift", dict(sections=("totalizer_solver",), max_patterns=1),
     {"totalizer_assumption_at_most"}),
    ("StubTotalizerOutputs", dict(sections=("totalizer_outputs",), max_patterns=1), {"totalizer_output"}),
    ("StubOptFirst", dict(sections=("optimise",), opt_instances=150), {"optimise_not_optimal"}),
    ("StubOptCount", dict(sections=("optimise",), opt_instances=150), {"optimise_count_is_not_the_models"}),
    ("StubOptNone", dict(sections=("optimise",), opt_instances=150), {"optimise_none_on_sat"}),
    ("StubOptModel", dict(sections=("optimise",), opt_instances=150), {"optimise_bad_model"}),
    ("StubOptDirection", dict(sections=("optimise",), opt_instances=150), {"optimise_not_optimal"}),
)


def self_test(seed, pool):
    failures = 0
    print("stub                       flagged  kinds seen")
    for stub, kwargs, must in SELF_TESTS:
        kw = dict(kwargs)
        opt_instances = kw.pop("opt_instances", 0)
        sections = kw.pop("sections")
        cfg = {"seed": seed, "cross_checks": kw.pop("cross_checks", False), "optimiser_class": False}
        tasks = build_tasks(stub, cfg, 2, opt_instances, sections, **kw)
        counts, bad, _, _ = execute(tasks, pool)
        kinds = collections.Counter(m["kind"] for m in bad if not m["label"])
        ok = must <= set(kinds)
        if stub == "StubSameCount":
            # the point of this stub: a judge that compared only sizes would pass it
            same = [m for m in bad if m["kind"] == "wrong_solutions" and m.get("same_count")]
            ok = ok and bool(same)
        failures += not ok
        print(f"{stub:26} {'yes' if ok else 'NO ':7}  {dict(kinds)}")
    # the control: real code through every section, cross-checks on, must flag nothing
    # unlabelled and must reach the same categories the default run requires
    control_sections = ("grid", "totalizer", "totalizer_outputs", "totalizer_solver", "optimise")
    cfg = {"seed": seed, "cross_checks": True, "optimiser_class": True}
    tasks = build_tasks("Real", cfg, 2, 150, control_sections, max_patterns=FIXED_PATTERNS + 1)
    control_counts, bad, _, _ = execute(tasks, pool)
    unlabelled = [m for m in bad if not m["label"]]
    zero = [c for c in required_categories(control_sections) if not control_counts[c]]
    if zero:
        print("control left categories at zero:", zero)
        failures += 1
    print(f"{'Real (control)':26} {'clean' if not unlabelled else 'FLAGGED':7}  "
          f"{len(bad) - len(unlabelled)} labelled, {len(unlabelled)} unlabelled")
    failures += bool(unlabelled)
    # a zero category must fail the run
    missing = [c for c in required_categories(("grid",)) if not collections.Counter()[c]]
    if not missing:
        print("zero-category check did not fire")
        failures += 1
    else:
        print(f"zero-category check fires on an empty run: {len(missing)} categories")
    print("self-test:", "ok" if not failures else f"{failures} FAILED")
    return 1 if failures else 0


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=DEFAULT_SEED)
    ap.add_argument("--instances", type=int, default=DEFAULT_INSTANCES,
                    help="random sign-and-order patterns per grid cell, on top of the 3 fixed ones")
    ap.add_argument("--opt-instances", type=int, default=DEFAULT_OPT_INSTANCES,
                    help="random problems for optimise and Optimiser")
    ap.add_argument("--jobs", type=int, default=max(1, min(8, (os.cpu_count() or 2) - 1)))
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--no-write", action="store_true", help="do not write campaign/results/encodings.json")
    ap.add_argument("--sections", default=",".join(ALL_SECTIONS))
    args = ap.parse_args(argv)
    sections = tuple(args.sections.split(","))

    t0 = time.time()
    pool = multiprocessing.Pool(args.jobs) if args.jobs > 1 else None
    try:
        if args.self_test:
            return self_test(args.seed, pool)
        cfg = {"seed": args.seed}
        tasks = build_tasks("Real", cfg, args.instances, args.opt_instances, sections)
        counts, bad, steps, instances = execute(tasks, pool)
    finally:
        if pool:
            pool.close()
            pool.join()
    runtime = time.time() - t0

    missing = [c for c in required_categories(sections) if not counts[c]]
    want_cells = grid_cell_count()
    grid_ok = "grid" not in sections or counts["grid.cells_visited"] == want_cells

    labelled = collections.Counter(m["label"] for m in bad if m["label"])
    unexplained = [m for m in bad if not m["label"]]

    print(f"seed {args.seed}, {instances} instances, {steps} checks, {runtime:.1f}s, {args.jobs} jobs")
    print(f"grid cells visited: {counts['grid.cells_visited']} of {want_cells}")
    for key in sorted(counts):
        print(f"  {key}: {counts[key]}")
    for label, n in sorted(labelled.items()):
        sev, summary = {**FINDINGS, **FOREIGN_FINDINGS}[label]
        print(f"KNOWN {label} [{sev}] {n} mismatches: {summary}")
        example = next(m for m in bad if m["label"] == label)
        print(f"  first: {json.dumps(example)[:400]}")
    for m in unexplained[:20]:
        print("UNEXPLAINED", json.dumps(m)[:600])
    if len(unexplained) > 20:
        print(f"... and {len(unexplained) - 20} more unexplained")
    for c in missing:
        print("ZERO CATEGORY", c)
    if not grid_ok:
        print("GRID INCOMPLETE")

    if not args.no_write:
        out = pathlib.Path(__file__).parent / "results" / "encodings.json"
        out.parent.mkdir(exist_ok=True)
        out.write_text(json.dumps({
            "corner": "encodings",
            "seeds": [args.seed],
            "instances": instances,
            "steps": steps,
            "per_category_counts": dict(sorted(counts.items())),
            "runtime_seconds": round(runtime, 1),
            "jobs": args.jobs,
            "mismatches_labelled": dict(sorted(labelled.items())),
            "mismatches_unexplained": len(unexplained),
            "grid": {"cells": want_cells, "visited": counts["grid.cells_visited"],
                     "patterns_per_cell": FIXED_PATTERNS + args.instances},
            "findings": [{"id": i, "severity": {**FINDINGS, **FOREIGN_FINDINGS}[i][0],
                          "summary": {**FINDINGS, **FOREIGN_FINDINGS}[i][1]}
                         for i in sorted(labelled)],
            "observations": OBSERVATIONS,
            "not_checked": NOT_CHECKED,
        }, indent=2) + "\n")
    if missing or not grid_ok or bad:
        return 1
    return 0


OBSERVATIONS = [
    "An unknown method name is ignored wherever the code returns before it looks at the method "
    "(k >= n, k <= 0, at_least_k with k == 1): see observed.bad_method_accepted.",
    "exactly_one(lits, 'bogus') emits the at-least-one clause and then raises: see "
    "observed.bad_method_left_clauses_behind. No accepted method name does this.",
    "With minimise=False, on_improve receives the count of false soft literals, while optimise "
    "returns the count of true ones. The docstrings do not say which: see "
    "observed.maximise_on_improve_reports_false_count.",
    "With minimise=False, Optimiser.run(target=t) and solve_with_bound(b) bound the false soft "
    "literals, not the value run returns. Judged on that reading.",
    "Encoder.amo_commander(lits, group=1) with two or more inputs raises RecursionError. "
    "at_most_one never passes a group, so the public paths do not reach it.",
]

NOT_CHECKED = [
    "The auto thresholds past the grid: at_most_k switching to the totalizer at k*n > 20000 was not "
    "exercised, though the method it switches to is on the grid.",
    "Solver sink at n > 6 runs on one sign-and-order pattern per cell, not all of them.",
    "Truncated counters are tightened on 2 of the sign-and-order patterns per n, not all of them. "
    "Truncation on a Solver stops at n = 7, and output semantics of truncated counters at n = 8.",
    "Arc consistency stops at n = 6, on one pattern per cell, and exactly_k is excluded because "
    "the module does not claim it for a conjunction.",
    "Off the grid the sizes are smaller: k out of range to n = 6, repeated inputs and root-fixed "
    "inputs to n = 7, direct methods and undeclared inputs to n = 8, stacked constraints to 5 inputs "
    "each. Repeated, stacked and root-fixed are 400 random cases each, not a grid.",
    "optimise and Optimiser run on the Python Solver only: Optimiser asserts it, so the native engine "
    "is not reachable there. They are checked on random problems, not on a grid.",
    "Proof logging through the Solver sink: encoding with a proof attached was not exercised.",
    "The preprocessors answer UNSAT only on stacked constraints, not on the grid. The grid's only "
    "UNSAT cells are at n = 0, where the formula is the empty clause and they crash (preprocess-2).",
    "Gates, Tseitin, xor_chain and the pseudo-Boolean BDD are outside this corner.",
    "The modelling layer's use of these encodings (Model, differential_solve) is outside this corner.",
    "Encoding sizes in the module's table were not judged, only solution sets and propagation.",
    "Each grid cell sees a sample of sign and order patterns: 3 fixed plus the random ones, not all "
    "2^n * n! of them. For distinct inputs the code does not branch on a literal's value except in "
    "gates this corner does not use.",
]


if __name__ == "__main__":
    sys.exit(main())
