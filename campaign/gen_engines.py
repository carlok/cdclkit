# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness campaign, corner "engines": the native engine against Python.

Every entry point is reached (`solve`, `Solver`, `solve_adaptive`,
`solve_portfolio`, the native `Solver` binding, the portfolio's worker and the
CLI), on tiny formulas, across the search knobs. Then:

* every answer against `oracle.satisfiable`;
* every SAT model against the formula, clause by clause;
* every proof step by step through `oracle.replay`, under the flavours
  `specified`, `operational` and `length-one`, reported separately;
* every proof through dratify's Python and Rust checkers: `ok=True` requires
  `not satisfiable(F)`, and a refutation of an UNSAT formula must be accepted;
* the engines against each other: verdict, model, every exposed counter, and
  the proof stream.

Known findings stay as mismatches and the run stays non-zero while they exist;
`FINDINGS` only gives them a name. A mismatch without a known label prints as
UNEXPLAINED.

    python -m campaign.gen_engines                 # the reported numbers
    python -m campaign.gen_engines --self-test     # the harness catches stubs
"""

from __future__ import annotations

import argparse
import collections
import inspect
import json
import os
import random
import re
import subprocess
import sys
import tempfile
import time
import warnings

import dratify
from dratify.cnf import CNF
from dratify.lits import from_dimacs, to_dimacs

from campaign import dpll, oracle
from cdclkit import Config, MemoryProof, Solver, native, solve
from cdclkit.pipeline import solve_adaptive
from cdclkit.portfolio import _worker, default_configs, solve_portfolio

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

#: label -> (severity, summary). A label here names a mismatch; it does not
#: excuse one.
FINDINGS = {
    "engines-1": ("Note", "preprocessed proofs delete unit clauses and then "
                          "rely on them: they hold under `operational` and "
                          "`length-one`, not under `specified` (both engines)"),
    "engines-2": ("Bug", "the preprocessors are not bit-exact: on the "
                         "preprocessing paths of solve_adaptive the engines "
                         "disagree on model, clauses_after, conflicts and "
                         "proof, against AGENTS.md"),
    "engines-3": ("Bug", "proof streams differ on the search-only paths: "
                         "native add_clause logs no strengthening, the Python "
                         "pipeline keeps an abandoned probe's steps and a SAT "
                         "run's steps, the native one drops them"),
    "engines-4": ("Bug", "after a failed re-solve the native Solver still "
                         "reports the previous model; Python clears it"),
    "engines-5": ("Critical", "`cdclkit solve --preprocess --adaptive` prints "
                              "the reduced formula's model, unreconstructed: "
                              "`s SATISFIABLE` with a model that falsifies "
                              "the input"),
    "engines-6": ("Bug", "`solve --adaptive` and `-j N` ignore `--conflicts`, "
                         "which the 0.1.3 changelog lists as fixed: a run with "
                         "a budget of 0 decides instead of exiting 0 (unknown)"),
    "engines-7": ("Bug", "solve_portfolio crashes on its defaults: jobs=None "
                         "raises TypeError, configs=[] recurses without end"),
    "engines-8": ("Bug", "both preprocessors crash on a formula holding the "
                         "empty clause, Python with ValueError and native with a "
                         "Rust panic that `except Exception` cannot catch, so "
                         "`solve --preprocess -j 2` dies on any formula "
                         "--preprocess refutes, instead of exiting 20"),
    "engines-9": ("Bug", "a Config one engine accepts the other refuses: "
                         "rnd_seed outside u32 and glue_keep < 0 raise "
                         "OverflowError on native, an unknown restart or ccmin "
                         "runs silently on Python; solve_adaptive also runs an "
                         "unknown engine name as Python"),
}

KNOBS = ("restart ccmin phase_saving init_phase target_phase target_reset "
         "walk_flips walk_interval walk_patience walk_min_conflicts var_decay "
         "var_decay_max cla_decay luby_base first_reduce reduce_inc glue_keep "
         "block_restart rnd_freq rnd_seed").split()

COUNTERS = ("conflicts decisions propagations restarts learned learned_lits "
            "minimized_lits reductions blocked_restarts deleted "
            "max_trail").split()

FLAVOURS = ("specified", "operational", "length-one")


# --------------------------------------------------------------------------
# formulas: at most 16 variables wherever the oracle judges them
# --------------------------------------------------------------------------


def rand_k(rng, n, ratio, ks=(3,)):
    out = []
    for _ in range(max(1, int(n * ratio))):
        vs = rng.sample(range(1, n + 1), min(rng.choice(ks), n))
        out.append([v if rng.random() < 0.5 else -v for v in vs])
    return out


def php(holes):
    x = lambda p, h: p * holes + h + 1
    out = [[x(p, h) for h in range(holes)] for p in range(holes + 1)]
    for h in range(holes):
        for p in range(holes + 1):
            for q in range(p + 1, holes + 1):
                out.append([-x(p, h), -x(q, h)])
    return out


def parity_cycle(rng, n, odd):
    """x1^x2=b1, x2^x3=b2, ...: refutable by parity alone when the bs are odd."""
    bits = [rng.randint(0, 1) for _ in range(n)]
    if (sum(bits) % 2 == 1) != odd:
        bits[0] ^= 1
    out = []
    for i in range(n):
        a, b = i + 1, (i + 1) % n + 1
        if bits[i]:
            out += [[a, b], [-a, -b]]
        else:
            out += [[a, -b], [-a, b]]
    return out


def gates(rng, n):
    """AND-gate definitions and a random top, which gives BVE something to do."""
    k = max(2, n // 2)
    out = []
    for v in range(k + 1, n + 1):
        a, b = rng.sample(range(1, v), 2)
        a, b = rng.choice((a, -a)), rng.choice((b, -b))
        out += [[-v, a], [-v, b], [v, -a, -b]]
    return out + rand_k(rng, n, 1.5)


def instance(rng):
    """(family, DIMACS clauses, declared variable count)."""
    kind = rng.choice(("rand3", "rand3", "rand3", "mixed", "mixed", "php",
                       "parity", "gates", "units", "dups", "sparse"))
    if kind == "rand3":
        n = rng.randint(3, 16) if rng.random() < 0.15 else rng.randint(3, 12)
        return kind, rand_k(rng, n, rng.choice((3.8, 4.3, 4.3, 5.0, 6.0))), n
    if kind == "mixed":
        n = rng.randint(2, 13)
        return kind, rand_k(rng, n, rng.choice((2.5, 3.5, 4.5)),
                            (1, 2, 2, 3, 3, 3, 4, 5)), n
    if kind == "php":
        holes = rng.choice((2, 3))
        return kind, php(holes), holes * (holes + 1)
    if kind == "parity":
        n = rng.randint(3, 12)
        return kind, parity_cycle(rng, n, rng.random() < 0.8), n
    if kind == "gates":
        n = rng.randint(4, 14)
        return kind, gates(rng, n), n
    if kind == "units":
        n = rng.randint(3, 12)
        body = rand_k(rng, n, 4.0)
        units = [[rng.choice((v, -v))] for v in rng.sample(range(1, n + 1),
                                                           rng.randint(1, 2))]
        return kind, units + body, n
    if kind == "dups":
        n = rng.randint(3, 10)
        body = rand_k(rng, n, 3.5, (2, 3))
        body += [list(rng.sample(c, len(c))) for c in rng.sample(body, len(body) // 3)]
        rng.shuffle(body)
        return kind, body, n
    n = rng.randint(4, 16)  # sparse, with declared variables nothing mentions
    return kind, rand_k(rng, max(2, n // 2), 2.0), n


def raw_shapes(rng, clauses):
    """What a CNF would normalise away, for the entry points that take raw clauses."""
    out = []
    for c in clauses:
        c = list(c)
        roll = rng.random()
        if roll < 0.15:
            c.append(rng.choice(c))  # a repeated literal
        elif roll < 0.25:
            c.append(-rng.choice(c))  # a tautology
        out.append(c)
    return out


def to_cnf(clauses, nvars):
    f = CNF(nvars)
    for c in clauses:
        f.add_dimacs(c)
    f.nvars = max(nvars, f.nvars)
    return f


def satisfies(clauses, model):
    return all(any(0 < abs(l) <= len(model) and (l > 0) == model[abs(l) - 1]
                   for l in c) for c in clauses)


def dimacs_steps(steps):
    return [(k, tuple(to_dimacs(l) for l in lits)) for k, lits in steps]


def internal_steps(steps):
    return [(k, tuple(from_dimacs(l) for l in lits)) for k, lits in steps]


# --------------------------------------------------------------------------
# knobs
# --------------------------------------------------------------------------


def sample_config(rng):
    kw = {}
    pick = lambda name, *values: kw.__setitem__(name, rng.choice(values))
    if rng.random() < 0.7:  # thresholds a tiny formula can actually cross
        pick("first_reduce", 0, 1, 2, 5, 20)
        pick("reduce_inc", 0, 1, 3)
        pick("glue_keep", 0, 1, 2, 3)
        pick("luby_base", 1, 2, 3, 7, 2.5, 100)
        pick("walk_min_conflicts", 0, 1, 3)
        pick("walk_flips", 0, 1, 10, 100)
        pick("walk_interval", 1, 2, 3)
        pick("walk_patience", 0, 1, 3, 9)
        pick("target_reset", 0, 1, 2)
    if rng.random() < 0.6:
        pick("restart", "luby", "glucose", "none")
        pick("ccmin", "deep", "basic", "none")
        pick("phase_saving", True, False)
        pick("init_phase", True, False)
        pick("target_phase", True, False)
        pick("block_restart", True, False)
    if rng.random() < 0.5:
        pick("var_decay", 0.5, 0.7, 0.8, 0.95)
        pick("var_decay_max", 0.8, 0.95, 0.999)
        pick("cla_decay", 0.9, 0.999)
        pick("rnd_freq", 0.0, 0.02, 0.1, 0.5, 1.0)
        pick("rnd_seed", 0, 1, 7, 2 ** 31, 2 ** 32 - 1, rng.getrandbits(32))
    return kw


def native_kwargs(cfg):
    kw = {k: getattr(cfg, k) for k in KNOBS}
    kw["luby_base"] = float(kw["luby_base"])
    return kw


# --------------------------------------------------------------------------
# what is under test, replaceable by a stub
# --------------------------------------------------------------------------


class Run:
    __slots__ = ("sat", "model", "stats", "steps", "load")

    def __init__(self, sat, model, stats, steps, load=0):
        self.sat, self.model, self.stats = sat, model, stats
        self.steps, self.load = steps, load


class Real:
    """The engines as they are. `steps` is always DIMACS."""

    def python_solver(self, clauses, nvars, kw, budget=None, proof=True):
        p = MemoryProof() if proof else None
        s = Solver(nvars, proof=p, config=Config(**kw))
        for c in clauses:
            if not s.add_clause([from_dimacs(l) for l in c]):
                break
        load = len(p.steps) if p else 0
        sat = s.solve(max_conflicts=budget) if s.ok else False
        stats = {k: getattr(s.stats, k) for k in COUNTERS}
        stats["walks"] = s.stats.walks
        stats["simplifications"] = s.stats.simplifications
        return Run(sat, list(s.model) if sat else None, stats,
                   dimacs_steps(p.steps) if p else [], load)

    def native_solver(self, clauses, nvars, kw, budget=None, proof=True):
        s = native.require().Solver(nvars, **native_kwargs(Config(**kw)))
        if proof:
            s.enable_proof()
        for c in clauses:
            if not s.add_clause([from_dimacs(l) for l in c]):
                break
        load = len(s.proof_steps())
        sat = s.solve(budget) if s.ok else False
        stats = {k: getattr(s, k) for k in COUNTERS}
        return Run(sat, list(s.model) if sat else None, stats,
                   [(k, tuple(l)) for k, l in s.proof_steps()], load)

    def adaptive(self, clauses, nvars, engine, kw, mode):
        f = to_cnf(clauses, nvars)
        p = MemoryProof()
        r = solve_adaptive(f, engine=engine, proof=p, config=Config(**kw), **mode)
        fields = {k: getattr(r, k) for k in (
            "conflicts", "preprocessed", "probe_conflicts", "clauses_before",
            "clauses_after")}
        return Run(r.sat, r.model, fields, dimacs_steps(p.steps))

    def portfolio(self, clauses, nvars, **kw):
        return solve_portfolio(to_cnf(clauses, nvars), **kw)

    def api_solve(self, clauses, nvars, kw):
        p = MemoryProof()
        sat, model = solve(to_cnf(clauses, nvars), proof=p, config=Config(**kw))
        return Run(sat, model, {}, dimacs_steps(p.steps))


# --------------------------------------------------------------------------
# judging
# --------------------------------------------------------------------------


class Report:
    def __init__(self, verbose=False):
        self.counts = collections.Counter()
        self.mismatches = collections.Counter()
        self.examples = {}
        self.steps = 0
        self.memo = {}
        self.verbose = verbose

    def mismatch(self, label, what, example):
        key = (label, what)
        self.mismatches[key] += 1
        text = repr(example)
        if key not in self.examples or len(text) < len(self.examples[key]):
            self.examples[key] = text

    def count(self, name, n=1):
        self.counts[name] += n


def judge_answer(rep, path, clauses, nvars, truth, sat, model):
    rep.count(f"answers.{path}")
    rep.steps += 1
    if sat is None:
        rep.mismatch(None, f"{path}: no answer without a budget", clauses)
        return
    if bool(sat) != truth:
        rep.mismatch(None, f"{path}: answered {sat}, oracle says {truth}", clauses)
    if sat:
        rep.steps += 1
        if not model or not satisfies(clauses, model):
            if clauses or model is None:
                rep.mismatch(None, f"{path}: model falsifies the formula",
                             (clauses, model))
        elif len(model) != max(nvars, 0):
            rep.mismatch(None, f"{path}: model has {len(model)} of {nvars} vars",
                         (clauses, model))


def replay_one(clauses, steps, flavour):
    """(completed-and-acceptable, final multiset, judgements)."""
    judged, final = oracle.replay(clauses, steps, flavour)
    return len(judged) == len(steps) and all(s.acceptable for s in judged), final, judged


def judge_proof(rep, path, clauses, nvars, truth, steps, complete=True):
    """Replay under every flavour, and through both of dratify's checkers.

    `complete=False` is for a stream that need not end in a refutation (a solve
    under assumptions): its lemmas are still judged.
    """
    key = (repr(clauses), tuple(steps))
    verdicts = rep.memo.get(key)
    if verdicts is None:
        verdicts = {}
        stats = collections.Counter()
        for flavour in FLAVOURS:
            ok, final, judged = replay_one(clauses, steps, flavour)
            rep.steps += len(judged)
            refuted = oracle.propagate(final)[0]
            verdicts[flavour] = (ok, refuted)
            for s in judged:
                if s.kind == "a":
                    stats["steps.add"] += 1
                    if s.rup and not s.implied:
                        rep.mismatch(None, "oracle: RUP but not implied", (clauses, steps))
                    if not s.rup and s.rat_on_first:
                        stats[f"steps.rat_only.{flavour}"] += 1
                    if not s.acceptable:
                        stats[f"steps.rejected.{flavour}"] += 1
                        if not s.preserves_sat:
                            stats[f"steps.unsound.{flavour}"] += 1
                else:
                    stats["steps.del"] += 1
                    if not s.present:
                        stats[f"steps.del_absent.{flavour}"] += 1
                    elif not s.applied:
                        stats[f"steps.del_ignored.{flavour}"] += 1
                    elif len(set(s.clause)) <= 1:
                        stats[f"steps.del_unit_applied.{flavour}"] += 1
        chk = {}
        cnf = to_cnf(clauses, nvars)
        internal = internal_steps(steps)
        for engine in ("python", "native"):
            chk[engine] = dratify.check_proof(cnf.copy(), list(internal), engine=engine)
            rep.count(f"selfcheck.{engine}")
        verdicts["dratify"] = {e: (c.ok, c.reached_empty) for e, c in chk.items()}
        rep.counts.update(stats)
        rep.memo[key] = verdicts

    rep.count(f"proofs.{path}")
    has_unit_del = any(k == "d" and len(set(c)) <= 1 for k, c in steps)
    dr = verdicts["dratify"]
    if dr["python"] != dr["native"]:
        rep.mismatch(None, f"{path}: dratify's checkers disagree {dr}", (clauses, steps))
    if truth:
        # a satisfiable formula: nothing may refute it, under any reading
        for e, (ok, _) in dr.items():
            if ok:
                rep.mismatch(None, f"{path}: dratify {e} ok=True on a SAT formula",
                             (clauses, steps))
        if any(k == "a" and not c for k, c in steps):
            rep.mismatch(None, f"{path}: empty clause logged on a SAT formula",
                         (clauses, steps))
    elif complete:
        for e, (ok, reached) in dr.items():
            if not ok or not reached:
                rep.mismatch(None, f"{path}: dratify {e} rejects a refutation of an "
                                   f"UNSAT formula", (clauses, steps))
    for flavour in FLAVOURS:
        ok, refuted = verdicts[flavour]
        holds = ok and (truth or refuted or not complete)
        rep.count(f"replay.{flavour}.{'ok' if holds else 'fail'}")
        if truth:
            rep.count("replay.on_sat_formula")
        else:
            rep.count("replay.on_unsat_formula")
        if holds:
            continue
        rep.count(f"replay.{flavour}.fail.{path}")
        if flavour == "specified" and has_unit_del:
            rep.mismatch("engines-1", f"{path}: proof fails under specified only",
                         (clauses, steps))
        else:
            rep.mismatch(None, f"{path}: proof fails under {flavour}", (clauses, steps))
    only_op = verdicts["operational"][0] and not verdicts["specified"][0]
    if only_op:
        rep.count("replay.holds_only_without_unit_deletion")
    return verdicts


def compare_counters(rep, path, clauses, a, b, kw, label=None):
    rep.count(f"parity.runs.{path}")
    for name in COUNTERS:
        if name in a.stats and name in b.stats:
            rep.steps += 1
            if a.stats[name] != b.stats[name]:
                rep.mismatch(label, f"{path}: {name} differs",
                             (clauses, kw, a.stats[name], b.stats[name]))
    if a.sat != b.sat:
        rep.mismatch(label, f"{path}: verdict differs", (clauses, kw, a.sat, b.sat))
    if a.model != b.model:
        rep.mismatch(label, f"{path}: model differs", (clauses, kw, a.model, b.model))


def compare_streams(rep, path, clauses, py, nat, kw):
    """Proof parity: split into what was logged while loading and in the search."""
    rep.count(f"parity.streams.{path}")
    if py.steps == nat.steps:
        return
    if py.steps[py.load:] == nat.steps[nat.load:]:
        rep.mismatch("engines-3", f"{path}: add_clause strengthening logged by "
                                  f"Python only", (clauses, kw))
    else:
        rep.mismatch(None, f"{path}: proof stream differs in the search",
                     (clauses, kw, py.steps, nat.steps))


# --------------------------------------------------------------------------
# the entry points
# --------------------------------------------------------------------------


def note_config(rep, kw, run):
    for k in kw:
        rep.count(f"knob.{k}")
    s = run.stats
    for name in ("conflicts", "restarts", "reductions", "deleted", "learned",
                 "minimized_lits", "walks", "simplifications"):
        if s.get(name):
            rep.count(f"effect.{name}")
    if kw.get("rnd_freq"):
        rep.count("effect.random_branching")


def check_direct(rep, eng, clauses, nvars, truth, kw):
    py = eng.python_solver(clauses, nvars, kw)
    nat = eng.native_solver(clauses, nvars, kw)
    note_config(rep, kw, py)
    compare_counters(rep, "solver", clauses, py, nat, kw)
    compare_streams(rep, "solver", clauses, py, nat, kw)
    for name, r in (("solver.python", py), ("solver.native", nat)):
        judge_answer(rep, name, clauses, nvars, truth, r.sat, r.model)
        judge_proof(rep, name, clauses, nvars, truth, r.steps)
    # logging a proof must not change the search
    for name, r, plain in (
            ("noproof.python", py, eng.python_solver(clauses, nvars, kw, proof=False)),
            ("noproof.native", nat, eng.native_solver(clauses, nvars, kw, proof=False))):
        compare_counters(rep, name, clauses, r, plain, kw)
    # variables the constructor was not told about grow the solver, in both
    top = max((abs(l) for c in clauses for l in c), default=0)
    if clauses:
        a, b = eng.python_solver(clauses, 0, kw), eng.native_solver(clauses, 0, kw)
        rep.count("solver.undeclared_vars")
        compare_counters(rep, "solver.undeclared", clauses, a, b, kw)
        judge_answer(rep, "solver.undeclared.python", clauses, top, truth, a.sat, a.model)
        judge_answer(rep, "solver.undeclared.native", clauses, top, truth, b.sat, b.model)
    # the one-call API is the Python Solver
    api = eng.api_solve(clauses, nvars, kw)
    judge_answer(rep, "solve()", clauses, nvars, truth, api.sat, api.model)
    if api.sat is False and api.model is not None:
        rep.mismatch(None, "solve(): (False, model)", clauses)
    rep.count("parity.runs.solve()")
    if (api.sat, api.model, api.steps) != (py.sat, py.model, py.steps):
        # add_clause and add_cnf are the same loop, so this is a real difference
        rep.mismatch(None, "solve() differs from Solver", (clauses, kw))
    return py


def check_raw(rep, eng, rng, clauses, nvars, kw):
    """Repeated literals, tautologies and empty clauses, on the raw entry points."""
    raw = raw_shapes(rng, clauses)
    if rng.random() < 0.15:
        raw.insert(rng.randint(0, len(raw)), [])
    truth = oracle.satisfiable(raw)
    py = eng.python_solver(raw, nvars, kw)
    nat = eng.native_solver(raw, nvars, kw)
    rep.count("raw.runs")
    rep.count("raw.empty_clause", any(not c for c in raw))
    compare_counters(rep, "raw", raw, py, nat, kw)
    compare_streams(rep, "raw", raw, py, nat, kw)
    judge_answer(rep, "raw.python", raw, nvars, truth, py.sat, py.model)
    judge_answer(rep, "raw.native", raw, nvars, truth, nat.sat, nat.model)
    judge_proof(rep, "raw.python", raw, nvars, truth, py.steps)
    judge_proof(rep, "raw.native", raw, nvars, truth, nat.steps)


def check_budget(rep, eng, rng, clauses, nvars, truth, kw):
    """A conflict budget, resumed until decided. Same stops, same counters."""
    n = native.require()
    p = MemoryProof()
    py = Solver(nvars, proof=p, config=Config(**kw))
    na = n.Solver(nvars, **native_kwargs(Config(**kw)))
    na.enable_proof()
    for c in clauses:
        lits = [from_dimacs(l) for l in c]
        py.add_clause(lits)
        na.add_clause(lits)
    budget = rng.choice((1, 1, 2, 3, 7))
    for _ in range(100000):
        a = py.solve(max_conflicts=budget) if py.ok else False
        b = na.solve(budget) if na.ok else False
        rep.count("budget.calls")
        rep.steps += 1
        if a is None or b is None:
            rep.count("budget.exhausted")
        for name in ("conflicts", "decisions", "propagations", "restarts"):
            if getattr(py.stats, name) != getattr(na, name):
                rep.mismatch(None, f"budget: {name} differs",
                             (clauses, kw, budget, getattr(py.stats, name), getattr(na, name)))
        if a != b or py.ok != na.ok:
            rep.mismatch(None, "budget: verdict differs", (clauses, kw, budget, a, b))
        if a is None and (py.model or list(na.model)):
            rep.mismatch(None, "budget: a model without an answer", (clauses, kw, budget))
        if a is not None:
            break
    judge_answer(rep, "budget.python", clauses, nvars, truth, a, py.model if a else None)
    judge_answer(rep, "budget.native", clauses, nvars, truth, b, list(na.model) if b else None)
    judge_proof(rep, "budget.python", clauses, nvars, truth, dimacs_steps(p.steps))
    judge_proof(rep, "budget.native", clauses, nvars, truth,
                [(k, tuple(l)) for k, l in na.proof_steps()])
    # budget 0 stops before anything happens, unless loading already decided
    if py.ok:
        p0 = Solver(nvars, config=Config(**kw))
        n0 = n.Solver(nvars, **native_kwargs(Config(**kw)))
        for c in clauses:
            lits = [from_dimacs(l) for l in c]
            p0.add_clause(lits)
            n0.add_clause(lits)
        x = p0.solve(max_conflicts=0) if p0.ok else False
        y = n0.solve(0) if n0.ok else False
        rep.count("budget.zero")
        if x != y or p0.stats.propagations != n0.propagations:
            rep.mismatch(None, "budget 0: differs", (clauses, kw, x, y))


def check_adaptive(rep, eng, rng, clauses, nvars, truth, kw):
    modes = [("never", {"never_preprocess": True}),
             ("always", {"always_preprocess": True}),
             ("default", {}),
             ("probe0", {"probe": 0}),
             ("probe1", {"probe": 1}),
             ("probe3", {"probe": rng.choice((2, 3, 5))})]
    for name, mode in modes:
        if any(not c for c in clauses) and name in ("always",):
            continue  # engines-8: asserted by check_edges
        py = eng.adaptive(clauses, nvars, "python", kw, mode)
        nat = eng.adaptive(clauses, nvars, "native", kw, mode)
        rep.count(f"adaptive.{name}")
        if py.stats["preprocessed"] or nat.stats["preprocessed"]:
            rep.count("adaptive.preprocessing_ran")
        if py.stats["probe_conflicts"] != nat.stats["probe_conflicts"]:
            rep.mismatch(None, f"adaptive.{name}: probe differs", (clauses, kw, mode))
        for e, r in (("python", py), ("native", nat)):
            path = f"adaptive.{name}.{e}"
            judge_answer(rep, path, clauses, nvars, truth, r.sat, r.model)
            judge_proof(rep, path, clauses, nvars, truth, r.steps)
        ran_prep = py.stats["preprocessed"] and nat.stats["preprocessed"]
        label = "engines-2" if ran_prep else None
        for field in ("conflicts", "preprocessed", "clauses_before", "clauses_after"):
            rep.steps += 1
            if py.stats[field] != nat.stats[field]:
                rep.mismatch(label, f"adaptive.{name}: {field} differs",
                             (clauses, kw, mode, py.stats[field], nat.stats[field]))
        if py.sat != nat.sat:
            rep.mismatch(None, f"adaptive.{name}: verdict differs", (clauses, kw, mode))
        if py.model != nat.model:
            rep.mismatch(label, f"adaptive.{name}: model differs",
                         (clauses, kw, mode, py.model, nat.model))
        rep.steps += 1
        if py.steps != nat.steps:
            if ran_prep:
                if nat.steps and py.steps[-len(nat.steps):] == nat.steps:
                    rep.mismatch("engines-3", f"adaptive.{name}: an abandoned probe's "
                                              f"steps kept by Python only", (clauses, kw, mode))
                else:
                    rep.mismatch("engines-2", f"adaptive.{name}: proof differs",
                                 (clauses, kw, mode))
            elif py.sat and not nat.steps:
                rep.mismatch("engines-3", f"adaptive.{name}: SAT run's steps kept "
                                          f"by Python, dropped by native", (clauses, kw, mode))
            else:
                # a run that stopped in its first stage is exactly a plain run,
                # so the difference must be the one compare_streams explains
                budget = None if "never_preprocess" in mode else mode.get("probe", 1000)
                a = eng.python_solver(clauses, nvars, kw, budget)
                b = eng.native_solver(clauses, nvars, kw, budget)
                if (a.steps == py.steps and b.steps == nat.steps
                        and a.steps[a.load:] == b.steps[b.load:]):
                    rep.mismatch("engines-3", f"adaptive.{name}: add_clause strengthening "
                                              f"logged by Python only", (clauses, kw, mode))
                else:
                    rep.mismatch(None, f"adaptive.{name}: proof differs without "
                                       f"preprocessing", (clauses, kw, mode, py.steps, nat.steps))
    # the parallel path, which takes no proof
    for engine in ("python", "native"):
        f = to_cnf(clauses, nvars)
        try:
            solve_adaptive(f, engine=engine, jobs=2, proof=MemoryProof())
            rep.mismatch(None, "adaptive: jobs=2 with a proof did not refuse", clauses)
        except ValueError:
            rep.count("adaptive.refused_parallel_proof")
    f = to_cnf(clauses, nvars)
    before = list(f.clauses)
    r = solve_adaptive(f, engine="native", jobs=rng.choice((2, 3)), probe=rng.choice((0, 1)),
                       config=Config(**kw))
    rep.count("adaptive.parallel.native")
    judge_answer(rep, "adaptive.parallel.native", clauses, nvars, truth, r.sat, r.model)
    if f.clauses != before:
        rep.mismatch(None, "adaptive: the input formula was mutated", clauses)


def check_portfolio_threads(rep, eng, rng, clauses, nvars, truth):
    jobs = rng.choice((2, 2, 3, 4, 6, 12))
    want_proof = rng.random() < 0.6
    workers = rng.choice((0, 0, 1, 2, None)) if not want_proof else 0
    configs = None
    if rng.random() < 0.4:
        configs = [Config(**sample_config(rng)) for _ in range(jobs)]
    r = eng.portfolio(clauses, nvars, jobs=jobs, want_proof=want_proof,
                      configs=configs, engine="native", preprocess_workers=workers)
    path = "portfolio.threads" + (".proof" if want_proof else "")
    rep.count(path)
    if not r.finished:
        rep.mismatch(None, f"{path}: unfinished without a timeout", clauses)
    judge_answer(rep, path, clauses, nvars, truth, r.sat, r.model)
    if want_proof and not r.sat:
        if not r.proof_steps:
            rep.mismatch(None, f"{path}: UNSAT without a proof", clauses)
        else:
            judge_proof(rep, path, clauses, nvars, truth, dimacs_steps(r.proof_steps))
    if workers == 0 and r.winner_config is not None:
        # the winner's search is the same search a plain run of that config does
        kw = {k: getattr(r.winner_config, k) for k in KNOBS}
        seq = eng.python_solver(clauses, nvars, kw)
        rep.count("portfolio.winner_vs_sequential")
        for name in ("conflicts", "decisions", "propagations", "restarts"):
            rep.steps += 1
            if r.stats.get(name) != seq.stats[name]:
                rep.mismatch(None, f"{path}: winner's {name} differs from a sequential "
                                   f"run of its config", (clauses, kw))
        if r.sat != seq.sat or (r.sat and r.model != seq.model):
            rep.mismatch(None, f"{path}: winner's answer differs from a sequential "
                               f"run of its config", (clauses, kw))
        if want_proof and not r.sat:
            nat = eng.native_solver(clauses, nvars, kw)
            if dimacs_steps(r.proof_steps) != nat.steps:
                rep.mismatch(None, f"{path}: winner's proof differs from a sequential "
                                   f"native run of its config", (clauses, kw))


def check_portfolio_one(rep, eng, clauses, nvars, truth, kw):
    """jobs=1 is documented as byte-for-byte a plain solver run."""
    runs = {}
    for engine in ("python", "native"):
        r = eng.portfolio(clauses, nvars, jobs=1, want_proof=True, engine=engine,
                          configs=[Config(**kw)])
        path = f"portfolio.jobs1.{engine}"
        rep.count(path)
        judge_answer(rep, path, clauses, nvars, truth, r.sat, r.model)
        steps = dimacs_steps(r.proof_steps or [])
        if not r.sat:
            judge_proof(rep, path, clauses, nvars, truth, steps)
        seq = (eng.python_solver if engine == "python" else eng.native_solver)(
            clauses, nvars, kw)
        for name in ("conflicts", "decisions", "propagations", "restarts"):
            rep.steps += 1
            if r.stats.get(name) != seq.stats[name]:
                rep.mismatch(None, f"{path}: {name} differs from a plain run", (clauses, kw))
        if r.sat != seq.sat or r.model != seq.model or (not r.sat and steps != seq.steps):
            rep.mismatch(None, f"{path}: differs from a plain run", (clauses, kw))
        runs[engine] = r
    a, b = runs["python"], runs["native"]
    rep.count("parity.runs.portfolio.jobs1")
    if (a.sat, a.model) != (b.sat, b.model):
        rep.mismatch(None, "portfolio.jobs1: engines differ", (clauses, kw))
    for name in ("conflicts", "decisions", "propagations", "restarts"):
        if a.stats.get(name) != b.stats.get(name):
            rep.mismatch(None, f"portfolio.jobs1: {name} differs", (clauses, kw))


def check_adaptive_procs(rep, rng, clauses, nvars, truth):
    r = solve_adaptive(to_cnf(clauses, nvars), engine="python", jobs=2,
                       always_preprocess=rng.random() < 0.5, probe=rng.choice((0, 1)))
    rep.count("adaptive.parallel.python")
    judge_answer(rep, "adaptive.parallel.python", clauses, nvars, truth, r.sat, r.model)


def check_portfolio_procs(rep, eng, rng, clauses, nvars, truth):
    want_proof = rng.random() < 0.5
    workers = 0 if want_proof else rng.choice((0, 1))
    r = eng.portfolio(clauses, nvars, jobs=2, want_proof=want_proof, engine="python",
                      preprocess_workers=workers)
    path = "portfolio.procs" + (".proof" if want_proof else "")
    rep.count(path)
    judge_answer(rep, path, clauses, nvars, truth, r.sat, r.model)
    if want_proof and not r.sat:
        judge_proof(rep, path, clauses, nvars, truth, dimacs_steps(r.proof_steps or []))


def check_worker(rep, clauses, nvars, truth, kw):
    """The preprocessing worker, on the engine the driver never hands it.

    The driver takes threads whenever native is built, so `_worker` with
    engine="native" and preprocessing on is reachable only directly.
    """
    f = to_cnf(clauses, nvars)
    plain = [list(c) for c in f.clauses]
    for engine in ("python", "native"):
        _, sat, model, steps, _ = _worker(
            (0, f.nvars, plain, Config(**kw).as_dict(), False, engine, True))
        rep.count(f"portfolio.worker_preprocess.{engine}")
        judge_answer(rep, f"portfolio.worker_preprocess.{engine}", clauses, nvars,
                     truth, sat, model)
        if steps is not None:
            rep.mismatch(None, "preprocessing worker returned a proof", clauses)


def check_incremental(rep, rng, clauses, nvars, kw):
    """Solve, add clauses, solve again. No proof: added clauses are not lemmas."""
    py = Solver(nvars, config=Config(**kw))
    na = native.require().Solver(nvars, **native_kwargs(Config(**kw)))
    current = [list(c) for c in clauses]
    for c in current:
        lits = [from_dimacs(l) for l in c]
        py.add_clause(lits)
        na.add_clause(lits)
    for _ in range(rng.randint(2, 4)):
        a, b = py.solve(), na.solve()
        truth = oracle.satisfiable(current)
        rep.count("incremental.solves")
        rep.steps += 1
        judge_answer(rep, "incremental.python", current, py.nvars, truth, a,
                     list(py.model) if a else None)
        judge_answer(rep, "incremental.native", current, na.nvars, truth, b,
                     list(na.model) if b else None)
        if a is False and b is False and py.model != list(na.model):
            rep.count("incremental.stale_model")
            rep.mismatch("engines-4", "incremental: model after a failed re-solve",
                         (current, py.model, list(na.model)))
        elif a != b or list(py.model) != list(na.model):
            rep.mismatch(None, "incremental: engines differ", (current, kw))
        for name in ("conflicts", "decisions", "propagations", "restarts"):
            if getattr(py.stats, name) != getattr(na, name):
                rep.mismatch(None, f"incremental: {name} differs", (current, kw))
        extra = rand_k(rng, max(py.nvars, 1), 0.3, (1, 2, 3))
        if not nvars:
            break
        for c in extra:
            current.append(c)
            lits = [from_dimacs(l) for l in c]
            if py.add_clause(lits) != na.add_clause(lits):
                rep.mismatch(None, "incremental: add_clause differs", (current, kw))


def check_enumeration(rep, clauses, nvars, kw):
    if nvars > 9:
        return
    brute = set()
    for m in range(1 << nvars):
        a = [bool(m >> i & 1) for i in range(nvars)]
        if satisfies(clauses, a):
            brute.add(tuple(a))
    py = Solver(nvars, config=Config(**kw))
    for c in clauses:
        py.add_clause([from_dimacs(l) for l in c])
    found = [tuple(m) for m in py.enumerate_models()]
    rep.count("enumeration.runs")
    rep.count("enumeration.models", len(found))
    rep.steps += 1 + len(found)
    if set(found) != brute or len(found) != len(brute):
        rep.mismatch(None, "enumerate_models: wrong model set", (clauses, kw))
    na = native.require().Solver(nvars, **native_kwargs(Config(**kw)))
    for c in clauses:
        na.add_clause([from_dimacs(l) for l in c])
    seq = []
    while na.solve():
        m = list(na.model)
        seq.append(tuple(m))
        if not na.add_clause([(v << 1) | (1 if m[v] else 0) for v in range(nvars)]):
            break
        if not nvars:
            break
    if seq != found:
        rep.mismatch(None, "enumeration: engines find models in a different order",
                     (clauses, kw))


def check_assumptions(rep, rng, clauses, nvars, truth, kw):
    """Python only: the native binding takes no assumptions."""
    if nvars < 1:
        return
    vs = rng.sample(range(1, nvars + 1), min(nvars, rng.randint(1, 4)))
    assumptions = [v if rng.random() < 0.5 else -v for v in vs]
    if rng.random() < 0.2:
        assumptions.append(rng.choice(assumptions))  # repeated
    if rng.random() < 0.1:
        assumptions.append(-rng.choice(assumptions))  # contradictory
    p = MemoryProof()
    s = Solver(nvars, proof=p, config=Config(**kw))
    for c in clauses:
        s.add_clause([from_dimacs(l) for l in c])
    got = s.solve([from_dimacs(l) for l in assumptions])
    expect = oracle.satisfiable([*clauses, *([l] for l in assumptions)])
    rep.count("assumptions.runs")
    rep.steps += 1
    if bool(got) != expect:
        rep.mismatch(None, "assumptions: wrong verdict", (clauses, assumptions, kw))
    if got:
        rep.count("assumptions.sat")
        if not satisfies(clauses + [[l] for l in assumptions], s.model):
            rep.mismatch(None, "assumptions: model ignores them", (clauses, assumptions, kw))
    else:
        rep.count("assumptions.unsat")
        core = s.core_dimacs()
        if truth:
            rep.steps += 1
            if not set(core) <= set(assumptions) or oracle.satisfiable(
                    [*clauses, *([l] for l in core)]):
                rep.mismatch(None, "assumptions: core wrong", (clauses, assumptions, core, kw))
            if any(k == "a" and not c for k, c in p.steps):
                rep.mismatch(None, "assumptions: empty clause logged on a SAT formula",
                             (clauses, assumptions, kw))
    judge_proof(rep, "assumptions", clauses, nvars, truth, dimacs_steps(p.steps),
                complete=False)
    after = s.solve()
    if bool(after) != truth:
        rep.mismatch(None, "assumptions: wrong verdict after they are retracted",
                     (clauses, assumptions, kw))


def write_cnf(clauses, nvars, path):
    with open(path, "w", encoding="ascii") as fh:
        fh.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            fh.write(" ".join(map(str, c)) + " 0\n")


def cli(args, engine=None):
    env = dict(os.environ)
    env.pop("CDCLKIT_ENGINE", None)
    if engine:
        env["CDCLKIT_ENGINE"] = engine
    return subprocess.run([sys.executable, "-m", "cdclkit", *args], capture_output=True,
                          text=True, env=env, cwd=ROOT, timeout=120)


def parse_model(stdout, nvars):
    model = [False] * nvars
    for line in stdout.splitlines():
        if line.startswith("v "):
            for tok in line[2:].split():
                d = int(tok)
                if d and abs(d) <= nvars:
                    model[abs(d) - 1] = d > 0
    return model


CLI_FLAGS = (
    (), ("--check-model",), ("--self-check",),
    ("--preprocess",), ("--preprocess", "--check-model"), ("--preprocess", "--self-check"),
    ("--adaptive",), ("--adaptive", "--self-check"), ("--adaptive", "--check-model"),
    ("--adaptive", "--preprocess"), ("--adaptive", "--preprocess", "--check-model"),
    ("--adaptive", "--preprocess", "--self-check"),
    ("-j", "2"), ("-j", "2", "--self-check"), ("-j", "2", "--preprocess"),
    ("--adaptive", "-j", "2"), ("--adaptive", "-j", "2", "--check-model"),
)


def check_cli(rep, rng, clauses, nvars, truth, tmp, turn):
    path = os.path.join(tmp, "f.cnf")
    write_cnf(clauses, nvars, path)
    # round robin, so a default run reaches every combination on both verdicts
    for flags in (CLI_FLAGS[(turn * 4 + k) % len(CLI_FLAGS)] for k in range(4)):
        engine = rng.choice((None, "python", "native"))
        out = cli(["solve", path, *flags], engine)
        name = "cli " + " ".join(flags)
        rep.count("cli.runs")
        rep.count("cli.flags." + (" ".join(flags) or "plain"))
        rep.steps += 1
        wants = 10 if truth else 20
        if ("--adaptive" in flags or "-j" in flags) and "c engine: " not in out.stdout:
            rep.mismatch(None, f"{name}: no `c engine:` line", clauses)
        if engine and ("--adaptive" in flags or "-j" in flags):
            if f"c engine: {engine}" not in out.stdout:
                rep.mismatch(None, f"{name}: asked for {engine}", clauses)
        adaptive_prep = "--adaptive" in flags and "--preprocess" in flags
        if out.returncode != wants:
            if adaptive_prep and truth and out.returncode == 1 and "--check-model" in flags:
                rep.mismatch("engines-5", f"{name}: MODEL CHECK FAILED on the "
                                          f"unreconstructed model", clauses)
            elif "PanicException" in out.stderr and "--preprocess" in flags and "-j" in flags:
                rep.mismatch("engines-8", f"{name}: the native preprocessor panics on "
                                          f"the empty clause --preprocess produced", clauses)
            else:
                rep.mismatch(None, f"{name}: exit {out.returncode}, wanted {wants}",
                             (clauses, engine, out.stdout[-300:], out.stderr[-300:]))
            continue
        if truth:
            model = parse_model(out.stdout, nvars)
            if not satisfies(clauses, model):
                rep.mismatch("engines-5" if adaptive_prep else None,
                             f"{name}: printed a model that falsifies the input",
                             (clauses, engine, model))
    if rng.random() < 0.3:
        # a proof file written by each path, replayed by the oracle
        for flags in (("--adaptive",), ("-j", "2"), ()):
            proof = os.path.join(tmp, "f.drat")
            out = cli(["solve", path, "--proof", proof, *flags])
            rep.count("cli.proof_files")
            if truth or out.returncode != 20:
                continue
            with open(proof, encoding="ascii") as fh:
                steps = dimacs_steps(dratify.proof.parse_proof(fh.read()))
            judge_proof(rep, "cli.proof_file", clauses, nvars, truth, steps)


def check_cli_budget(rep, tmp):
    """AGENTS.md: exit 0 only for a budget that ran out. A budget of 0 must."""
    clauses, nvars = php(3), 12
    path = os.path.join(tmp, "budget.cnf")
    write_cnf(clauses, nvars, path)
    for flags in ((), ("--adaptive",), ("-j", "2"), ("--adaptive", "-j", "2")):
        out = cli(["solve", path, "--conflicts", "0", *flags])
        rep.count("cli.budget_runs")
        rep.steps += 1
        if out.returncode != 0:
            rep.mismatch("engines-6" if flags else None,
                         f"cli --conflicts 0 {' '.join(flags)}: exit {out.returncode}, "
                         f"wanted 0 (unknown)", clauses)


def check_edges(rep):
    """One-off shapes the random generators do not produce."""
    formula = to_cnf(php(2), 6)

    def raises(what, fn):
        try:
            fn()
            return None
        except KeyboardInterrupt:
            raise
        except BaseException as e:  # noqa: BLE001 - a Rust panic is a BaseException
            return type(e).__name__

    rep.count("edge.portfolio_defaults")
    got = raises("default", lambda: solve_portfolio(formula.copy()))
    if got:
        rep.mismatch("engines-7", f"solve_portfolio(f) raises {got}", ())
    # configs=[] recurses through a process-spawning fallback, ~50 ms a level:
    # a low limit shows the same thing without paying for a thousand levels
    limit = sys.getrecursionlimit()
    sys.setrecursionlimit(len(inspect.stack()) + 40)
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            got = raises("empty", lambda: solve_portfolio(formula.copy(), jobs=2, configs=[]))
    finally:
        sys.setrecursionlimit(limit)
    if got:
        rep.mismatch("engines-7", f"solve_portfolio(f, jobs=2, configs=[]) raises {got}", ())
    # the empty clause, through every preprocessing door
    for engine in ("python", "native"):
        f = to_cnf([[1, 2], []], 2)
        rep.count("edge.empty_clause_preprocess")
        got = raises("always", lambda: solve_adaptive(f, engine=engine, always_preprocess=True))
        if got:
            rep.mismatch("engines-8", f"always_preprocess on the empty clause, {engine}: "
                                      f"raises {got}", ())
    rep.count("edge.empty_clause_preprocess")
    got = raises("threads", lambda: solve_portfolio(to_cnf([[1, 2], []], 2), jobs=2))
    if got:
        rep.mismatch("engines-8", f"solve_portfolio(jobs=2) on the empty clause: raises {got}", ())
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "empty.cnf")
        with open(path, "w", encoding="ascii") as fh:
            fh.write("p cnf 2 2\n1 2 0\n0\n")
        for flags in (("-j", "2"), ("--preprocess",)):
            out = cli(["solve", path, *flags])
            rep.count("edge.empty_clause_preprocess")
            if out.returncode != 20:
                rep.mismatch("engines-8", f"cli {' '.join(flags)} on the empty clause: exit "
                                          f"{out.returncode}, wanted 20",
                             out.stderr[-200:])
    # --preprocess refutes this by itself, then -j hands the result to a worker
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "contradiction.cnf")
        write_cnf([[1], [-1]], 1, path)
        for engine in ("native", "python"):
            out = cli(["solve", path, "--preprocess", "-j", "2"], engine)
            rep.count("cli.preprocess_parallel_unsat")
            if out.returncode != 20:
                rep.mismatch("engines-8", f"cli --preprocess -j 2 on (1)(-1), {engine}: "
                                          f"exit {out.returncode}, wanted 20",
                             out.stderr[-200:])
        for name in ("quantum",):
            out = cli(["solve", path, "--adaptive"], name)
            rep.count("edge.engine_names")
            if out.returncode != 1:
                rep.mismatch(None, f"cli CDCLKIT_ENGINE={name}: exit {out.returncode}", ())
    rep.count("edge.engine_names")
    a = raises("adaptive", lambda: solve_adaptive(formula.copy(), engine="quantum"))
    b = raises("portfolio", lambda: solve_portfolio(formula.copy(), jobs=1, engine="quantum"))
    if a != b:
        rep.mismatch("engines-9", f"engine='quantum': solve_adaptive {a}, solve_portfolio {b}", ())
    # configuration both engines should take or refuse alike
    for kw in (dict(restart="bogus"), dict(ccmin="bogus"), dict(rnd_seed=2 ** 32 + 1),
               dict(rnd_seed=-1), dict(glue_keep=-1)):
        f = to_cnf(php(2), 6)
        rep.count("edge.config_acceptance")
        a = raises("py", lambda: solve_adaptive(f.copy(), engine="python", config=Config(**kw)))
        b = raises("na", lambda: solve_adaptive(f.copy(), engine="native", config=Config(**kw)))
        if a != b:
            rep.mismatch("engines-9", f"Config({kw}): python {a}, native {b}", ())
    # a deadline of 0: same early stop on both engines
    for mode in ({"never_preprocess": True}, {"always_preprocess": True}):
        out = []
        for engine in ("python", "native"):
            r = solve_adaptive(to_cnf(php(2), 6), engine=engine, seconds=0.0, **mode)
            out.append((r.sat, r.conflicts))
        rep.count("edge.zero_deadline")
        if out[0] != out[1]:
            rep.mismatch(None, f"seconds=0 {mode}: {out}", ())


def check_medium(rep, eng, rng, count):
    """Past the exhaustive oracle: dpll decides, oracle.rup judges each step."""
    for _ in range(count):
        n = rng.randint(30, 45)
        clauses = rand_k(rng, n, rng.choice((4.3, 4.5, 5.0)))
        kw = sample_config(rng)
        truth = dpll.satisfiable(clauses)
        py = eng.python_solver(clauses, n, kw)
        nat = eng.native_solver(clauses, n, kw)
        note_config(rep, kw, py)
        rep.count("medium.instances")
        rep.count("medium.sat" if truth else "medium.unsat")
        rep.count("medium.conflicts", py.stats["conflicts"])
        compare_counters(rep, "medium", clauses, py, nat, kw)
        compare_streams(rep, "medium", clauses, py, nat, kw)
        judge_answer(rep, "medium.python", clauses, n, truth, py.sat, py.model)
        judge_answer(rep, "medium.native", clauses, n, truth, nat.sat, nat.model)
        current = [list(c) for c in clauses]
        for k, lits in py.steps:
            rep.steps += 1
            if k == "d":
                current, present = oracle.remove_one(current, lits)
                if not present:
                    rep.count("medium.del_absent")
            else:
                if not oracle.rup(current, lits):
                    rep.mismatch(None, "medium: a lemma is not RUP", (clauses, kw, lits))
                    break
                current.append(list(lits))
        rep.count("medium.proof_steps", len(py.steps))
        if not truth and not oracle.propagate(current)[0]:
            rep.mismatch(None, "medium: proof does not refute", (clauses, kw))


def rand3(n, ratio, seed):
    rng = random.Random(seed)
    return rand_k(rng, n, ratio)


def check_big(rep, eng):
    """No oracle verdict here: the conflict volume no 16-variable formula has.

    n=205, ratio 4.35, seed 6 is the suite's instance that crosses the default
    reduction, rephasing and blocking thresholds. It is parity plus dratify,
    and `solve_adaptive` past its real 1000-conflict probe.
    """
    clauses = rand3(205, 4.35, 6)
    py = eng.python_solver(clauses, 205, {})
    nat = eng.native_solver(clauses, 205, {})
    rep.count("big.instances")
    rep.count("big.conflicts", py.stats["conflicts"])
    rep.count("big.blocked_restarts", py.stats["blocked_restarts"])
    rep.count("big.walks", py.stats["walks"])
    rep.count("big.reductions", py.stats["reductions"])
    compare_counters(rep, "big", clauses, py, nat, {})
    compare_streams(rep, "big", clauses, py, nat, {})
    cnf = to_cnf(clauses, 205)
    if py.sat is False:
        chk = dratify.check_proof(cnf, internal_steps(nat.steps), engine="native")
        rep.count("big.selfcheck")
        if not chk.ok:
            rep.mismatch(None, "big: the proof is rejected", ())
    for mode, name in (({}, "default"),):
        a = eng.adaptive(clauses, 205, "python", {}, mode)
        b = eng.adaptive(clauses, 205, "native", {}, mode)
        rep.count("big.adaptive_preprocessed", a.stats["preprocessed"] and b.stats["preprocessed"])
        if a.sat != b.sat:
            rep.mismatch(None, "big adaptive: verdict differs", ())
        for field in ("conflicts", "clauses_after"):
            if a.stats[field] != b.stats[field]:
                rep.mismatch("engines-2", f"big adaptive: {field} differs",
                             (a.stats[field], b.stats[field]))
        for e, r in (("python", a), ("native", b)):
            chk = dratify.check_proof(to_cnf(clauses, 205), internal_steps(r.steps),
                                      engine="native")
            rep.count("big.selfcheck")
            if r.sat is False and not chk.ok:
                rep.mismatch(None, f"big adaptive {e}: the proof is rejected", ())


# --------------------------------------------------------------------------
# the run
# --------------------------------------------------------------------------

REQUIRED = [
    "instances.sat", "instances.unsat", "answers.solver.python", "answers.solver.native",
    "answers.solve()", "adaptive.never", "adaptive.always", "adaptive.default",
    "adaptive.probe0", "adaptive.probe1", "adaptive.probe3",
    "adaptive.preprocessing_ran", "adaptive.refused_parallel_proof",
    "adaptive.parallel.native", "adaptive.parallel.python", "raw.runs", "raw.empty_clause",
    "solver.undeclared_vars", "cli.preprocess_parallel_unsat", "edge.engine_names",
    "portfolio.threads", "portfolio.threads.proof", "portfolio.jobs1.python",
    "portfolio.jobs1.native", "portfolio.procs", "portfolio.procs.proof",
    "portfolio.worker_preprocess.python", "portfolio.worker_preprocess.native",
    "portfolio.winner_vs_sequential", "budget.calls", "budget.exhausted", "budget.zero",
    "incremental.solves", "enumeration.runs", "assumptions.sat", "assumptions.unsat",
    "steps.add", "steps.del", "replay.specified.ok", "replay.operational.ok",
    "replay.length-one.ok", "replay.on_sat_formula", "replay.on_unsat_formula",
    "steps.del_unit_applied.specified", "steps.del_ignored.operational",
    "selfcheck.python", "selfcheck.native", "cli.runs", "cli.proof_files",
    "cli.budget_runs",
    "effect.conflicts", "effect.restarts", "effect.reductions", "effect.deleted",
    "effect.learned", "effect.minimized_lits", "effect.walks", "effect.simplifications",
    "effect.random_branching", "medium.instances", "big.blocked_restarts", "big.walks",
    "big.reductions", "big.adaptive_preprocessed", "edge.portfolio_defaults",
    "edge.empty_clause_preprocess", "edge.config_acceptance", "edge.zero_deadline",
] + [f"knob.{k}" for k in KNOBS] + [
    "cli.flags." + (" ".join(flags) or "plain") for flags in CLI_FLAGS]


def run(seed, instances, big=True, eng=None, rep=None, cli_every=25, procs_every=30,
        medium=15):
    eng = eng or Real()
    rep = rep or Report()
    rng = random.Random(seed)
    with tempfile.TemporaryDirectory() as tmp:
        for i in range(instances):
            family, clauses, nvars = instance(rng)
            truth = oracle.satisfiable(clauses)
            rep.count("instances")
            rep.count(f"instances.{'sat' if truth else 'unsat'}")
            rep.count(f"family.{family}")
            rep.steps += 1
            for kw in ({}, sample_config(rng)):
                check_direct(rep, eng, clauses, nvars, truth, kw)
            kw = sample_config(rng)
            check_raw(rep, eng, rng, clauses, nvars, kw)
            check_budget(rep, eng, rng, clauses, nvars, truth, kw)
            check_adaptive(rep, eng, rng, clauses, nvars, truth, kw)
            check_portfolio_one(rep, eng, clauses, nvars, truth, kw)
            check_portfolio_threads(rep, eng, rng, clauses, nvars, truth)
            check_worker(rep, clauses, nvars, truth, kw)
            check_incremental(rep, rng, clauses, nvars, kw)
            check_enumeration(rep, clauses, nvars, kw)
            check_assumptions(rep, rng, clauses, nvars, truth, kw)
            if procs_every and i % procs_every == 0:
                # both shapes, so a default run reaches both
                for _ in range(2):
                    check_portfolio_procs(rep, eng, rng, clauses, nvars, truth)
                check_adaptive_procs(rep, rng, clauses, nvars, truth)
            if cli_every and i % cli_every == 0:
                check_cli(rep, rng, clauses, nvars, truth, tmp, i // cli_every)
        if cli_every:
            check_cli_budget(rep, tmp)
    check_edges(rep)
    if medium:
        check_medium(rep, eng, rng, medium)
    if big:
        check_big(rep, eng)
    return rep


def summarise(rep, out=sys.stdout):
    known = collections.Counter()
    unexplained = []
    for (label, what), n in sorted(rep.mismatches.items(), key=lambda kv: str(kv[0])):
        if label:
            known[label] += n
        else:
            unexplained.append((what, n))
    for label in sorted(known):
        print(f"known {label} [{FINDINGS[label][0]}]: {known[label]} mismatches", file=out)
    for what, n in unexplained:
        print(f"UNEXPLAINED ({n}): {what}", file=out)
        print(f"    e.g. {rep.examples[(None, what)][:400]}", file=out)
    return known, unexplained


# --------------------------------------------------------------------------
# the self-test
# --------------------------------------------------------------------------


class SaysSat(Real):
    """Every formula is satisfiable, all variables true."""

    def native_solver(self, clauses, nvars, kw, budget=None, proof=True):
        r = super().native_solver(clauses, nvars, kw, budget, proof)
        r.sat, r.model, r.steps = True, [True] * nvars, []
        return r


class SaysUnsat(Real):
    """Every formula is refuted by the empty clause, without a word of why."""

    def python_solver(self, clauses, nvars, kw, budget=None, proof=True):
        r = super().python_solver(clauses, nvars, kw, budget, proof)
        r.sat, r.model, r.steps = False, None, [("a", ())]
        return r


class OffByOne(Real):
    """A native engine that counts one conflict too many."""

    def native_solver(self, clauses, nvars, kw, budget=None, proof=True):
        r = super().native_solver(clauses, nvars, kw, budget, proof)
        r.stats["conflicts"] += 1
        return r


class ForgesLemma(Real):
    """Starts each refutation with a clause that does not follow."""

    def native_solver(self, clauses, nvars, kw, budget=None, proof=True):
        r = super().native_solver(clauses, nvars, kw, budget, proof)
        if r.sat is False and nvars >= 2:
            r.steps = [("a", (1,)), ("d", (1,)), ("a", (-1,)), *r.steps]
        return r


class FlipsModel(Real):
    """A Python pipeline whose SAT model is wrong."""

    def adaptive(self, clauses, nvars, engine, kw, mode):
        r = super().adaptive(clauses, nvars, engine, kw, mode)
        if r.sat and engine == "python":
            r.model = [not b for b in r.model]
        return r


SELF_TESTS = [
    (SaysSat, ["answered", "model", "differs"]),
    (SaysUnsat, ["answered", "dratify", "fails under", "differs"]),
    (OffByOne, ["conflicts differs"]),
    (ForgesLemma, ["fails under", "dratify"]),
    (FlipsModel, ["model"]),
]


def self_test_proofs():
    """Proofs built by hand, each wrong in one known way, to the judge directly."""
    failed = 0
    f = [[1], [-1, 2], [-2, 3], [-3]]
    cases = [
        ("valid refutation", [("a", ())], False, []),
        ("unit deleted, then needed", [("d", (1,)), ("a", ())], False, ["specified only"]),
        ("stops short of refuting", [], False, ["under operational", "dratify"]),
        ("empty clause on a SAT formula", [("a", ())], True, ["empty clause", "under operational"]),
        ("lemma that does not follow", [("a", (-1, 5))], True, ["under operational"]),
    ]
    for name, steps, sat_formula, expected in cases:
        rep = Report()
        clauses = [[1, 2], [3, 4]] if sat_formula else f
        if name == "stops short of refuting":  # propagation alone must not finish it
            clauses = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
        judge_proof(rep, "stub", clauses, 7, sat_formula, steps)
        kinds = [what for (_, what) in rep.mismatches]
        ok = all(any(e in w for w in kinds) for e in expected) and (bool(expected) == bool(kinds))
        failed += not ok
        print(f"proof judge: {name:32} {'as expected' if ok else 'WRONG'}: {kinds}")
    return failed


def self_test():
    """Each stub must be flagged, in the way that stub is wrong."""
    failed = self_test_proofs()
    baseline = run(1, 20, big=False, cli_every=0, procs_every=0, medium=0)
    base_keys = set(baseline.mismatches)
    for stub, expected in SELF_TESTS:
        rep = run(1, 20, big=False, eng=stub(), cli_every=0, procs_every=0, medium=0)
        new = [what for (_, what) in set(rep.mismatches) - base_keys]
        hits = {e: sum(e in w for w in new) for e in expected}
        ok = all(hits.values())
        failed += not ok
        print(f"{stub.__name__:13} {'flagged' if ok else 'NOT FLAGGED'}: "
              f"{len(new)} new kinds of mismatch; {hits}")
    return failed


# --------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=20261108)
    ap.add_argument("--instances", type=int, default=300)
    ap.add_argument("--no-big", action="store_true",
                    help="skip the one instance that crosses the default thresholds")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--no-write", action="store_true",
                    help="do not write campaign/results/engines.json")
    args = ap.parse_args(argv)
    if not native.available():
        print("the native engine is not built: this corner cannot run", file=sys.stderr)
        return 2
    if args.self_test:
        failed = self_test()
        print("self-test:", "FAILED" if failed else "every stub was flagged")
        return 1 if failed else 0

    t0 = time.perf_counter()
    rep = run(args.seed, args.instances, big=not args.no_big)
    runtime = time.perf_counter() - t0
    known, unexplained = summarise(rep)
    missing = [k for k in REQUIRED if not rep.counts.get(k)]
    if args.instances < 100 or args.no_big:
        missing = []  # a short run makes no claim about reach
    for k in missing:
        print(f"CATEGORY NEVER REACHED: {k}")
    print(f"{args.instances} instances, {rep.steps} checks, seed {args.seed}, "
          f"{runtime:.1f}s, cdclkit-native {native.version()}, dratify {dratify.__version__}")
    for k in sorted(rep.counts):
        print(f"  {k}: {rep.counts[k]}")
    if not args.no_write:
        result = {
            "corner": "engines",
            "seeds": [args.seed],
            "instances": args.instances,
            "steps": rep.steps,
            "per_category_counts": dict(sorted(rep.counts.items())),
            "mismatch_counts": {
                f"{label or 'UNEXPLAINED'}: {what}": n
                for (label, what), n in sorted(rep.mismatches.items(), key=str)},
            "runtime_seconds": round(runtime, 1),
            "findings": [
                {"id": k, "severity": FINDINGS[k][0], "summary": FINDINGS[k][1]}
                for k in sorted(known)],
            "not_checked": NOT_CHECKED,
            "native_build": "cdclkit_native 0.1.7 embedding this checkout's dratify/rust "
                            "(0.1.10), not the crates.io release of the same version",
        }
        os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
        with open(os.path.join(HERE, "results", "engines.json"), "w", encoding="utf-8") as fh:
            json.dump(result, fh, indent=2)
            fh.write("\n")
    if unexplained or known:
        return 1
    return 2 if missing else 0


NOT_CHECKED = [
    "The default reduction, rephasing and restart-blocking thresholds are crossed "
    "only by the one 205-variable instance, where the oracle gives no verdict: parity "
    "and dratify only. On tiny formulas they are reached by lowering the thresholds.",
    "Restart blocking (10,000 conflicts) is unreachable below that instance, so it "
    "is covered by one instance.",
    "Assumptions have no native counterpart in the binding, so they are checked on "
    "Python only, and `set_decision`, `new_var(polarity=...)` likewise.",
    "`solve_portfolio(timeout=...)` and `solve_adaptive(seconds=...)` beyond a "
    "deadline of 0: tiny formulas finish before any deadline could fire.",
    "The race itself: threads and processes answer whichever way they finish, so "
    "winner-dependent counts vary slightly between runs; every check holds per winner.",
    "`_worker` on the native engine is reached by calling it directly, because the "
    "driver always takes threads when native is built. The process path on native "
    "(no threaded portfolio in the module) is not exercised.",
    "An `--adaptive` run stopped by a deadline in the CLI: the CLI passes none.",
    "`luby_base=0` and `walk_interval=0`, which are not meaningful configurations.",
    "The crates.io dratify 0.1.10: this build embeds the checkout's dratify/rust.",
    "Counters the native binding does not expose (walks, walk_flips, simplifications, "
    "removed_clauses, removed_lits) are read on Python to prove reach, and not compared.",
    "`CDCLKIT_ENGINE=native` without the build: it is built here, so that error is not reached.",
    "drat-trim: these proofs are replayed by the oracle's flavours and dratify, not by it.",
]

if __name__ == "__main__":
    sys.exit(main())
