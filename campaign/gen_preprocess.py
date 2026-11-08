# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Soundness generator for preprocessing, judged by ``campaign.oracle``.

What is asserted, for every technique's option on and off, on both engines:

* satisfiability and unsatisfiability are both preserved by the reduced formula;
* every clause of the reduced formula is implied by the input (``preprocess.py``
  uses resolution and strengthening only, so no clause may be merely RAT);
* **every** model of the reduced formula reconstructs to a model of the input,
  not only the one a solver's default phases happen to pick;
* a frozen variable's projection is preserved, so clauses over frozen variables
  can be added to the reduced formula afterwards;
* the proof, replayed step by step against the **original** formula under the
  deletion rule dratify documents (unit deletions ignored), is RUP at every
  addition and every addition is implied by the input;
* the combined preprocessing + search proof refutes the original when the
  verdict is UNSAT, and the verdict matches the oracle end to end, through
  ``solve_adaptive``, ``solve_portfolio`` and the CLI.

Run from the repo root::

    python -m campaign.gen_preprocess                # reproduces results/preprocess.json
    python -m campaign.gen_preprocess --self-test    # wrong stubs must be flagged
    python -m campaign.gen_preprocess --shrink       # shrink one case per label

Every mismatch carries a label. One whose finding is fixed prints as REGRESSION and
fails the run, an open one is reported, and an unknown label fails. See
campaign/status.py.
"""

from __future__ import annotations

import argparse
import collections
import contextlib
import io
import json
import os
import pathlib
import random
import sys
import tempfile
import time

from campaign import oracle, status

from cdclkit import native as native_mod
from cdclkit import cli as cdclkit_cli
from cdclkit.pipeline import solve_adaptive
from cdclkit.portfolio import solve_portfolio
from cdclkit.preprocess import Preprocessor
from cdclkit.solver import Solver
from dratify.cnf import CNF
from dratify.lits import from_dimacs, to_dimacs
from dratify.proof import MemoryProof, check_proof

#: Labels for mismatches that have a finding written up. Anything else is
#: reported as UNEXPLAINED. Both make the run fail.
KNOWN = {
    "cli-model-wrong": "preprocess-1",
    "cli-exit-code-wrong": "preprocess-1",
    "crash-empty-clause": "preprocess-2",
    "crash-reduced-empty-clause": "preprocess-2",
    "parity-reduced": "preprocess-3",
    "parity-stats": "preprocess-3",
    "parity-adaptive": "preprocess-3",
}

MAX_MODELS_PER_RUN = 24

FINDINGS = [
    {"id": "preprocess-1", "severity": "Critical",
     "summary": "`cdclkit solve --preprocess --adaptive` prints the reduced formula's model "
                "without reconstructing it: `1 0` answers `s SATISFIABLE`, `v -1`, exit 10."},
    {"id": "preprocess-2", "severity": "Bug",
     "summary": "An empty clause crashes both preprocessors (ValueError, Rust panic), so "
                "`solve --preprocess -j 2` on `1 0`, `-1 0` dies with a PanicException and "
                "no verdict, and re-preprocessing any UNSAT reduction raises."},
    {"id": "preprocess-3", "severity": "Bug",
     "summary": "The engines' preprocessors disagree on stats and proofs, and through "
                "solve_adaptive on clauses_after, conflicts and model; never on the verdict "
                "or the reduced formula with BCE off."},
    {"id": "preprocess-4", "severity": "Note",
     "summary": "Preprocessing proofs delete a unit before using it, so they check only where "
                "unit deletions are ignored; `specified` DRAT rejects them, as it does [[1],[-1]]."},
]

NOT_CHECKED = [
    "drat-trim: not installed here, so 'operational' is the oracle's approximation of it",
    "formulas past 16 mentioned variables, the oracle's limit",
    "the BVE guard len(pos)*len(negs) > 400 and the default subsumption budget of 2,000,000 "
    "are never reached; subsumption_limit is exercised only at 0, 1 and 5",
    "native BCE, elim_growth and subsumption_limit: native has no BCE and exposes neither option",
    "more than 24 models per run: reduced formulas with more are sampled, not enumerated",
    "which portfolio thread wins is not controlled, so a reconstruction from a preprocessing "
    "worker is possible on these runs but not counted",
    "search options (restart, ccmin, phase, --conflicts) crossed with preprocessing: default "
    "Config only",
    "reference solvers: every verdict is judged by the oracle, none by minisat/cadical/kissat",
]


# --------------------------------------------------------------------------
# formulas, in DIMACS
# --------------------------------------------------------------------------


def _lit(rng, v):
    return v if rng.random() < 0.5 else -v


def _random_clause(rng, n, k):
    return [_lit(rng, v) for v in rng.sample(range(1, n + 1), min(k, n))]


def fam_random(rng):
    """Mixed clause lengths at a ratio spread across the threshold."""
    n = rng.randint(2, 12)
    m = rng.randint(1, int(rng.choice((2.0, 4.5, 6.0)) * n) + 1)
    return n, [_random_clause(rng, n, rng.choice((1, 2, 2, 3, 3, 3, 4))) for _ in range(m)]


def fam_no_units(rng):
    """No planted units, so BVE and BCE see the formula before propagation empties it."""
    n = rng.randint(3, 12)
    m = rng.randint(n, 5 * n)
    return n, [_random_clause(rng, n, rng.choice((2, 3, 3, 4))) for _ in range(m)]


def fam_planted(rng):
    """Random clauses plus a shape aimed at each technique."""
    n = rng.randint(4, 12)
    cs = [_random_clause(rng, n, rng.choice((2, 3, 3))) for _ in range(rng.randint(1, 3 * n))]
    for _ in range(rng.randint(1, 6)):
        kind = rng.choice(("subsume", "strengthen", "block", "pure", "unit", "dup", "gate", "gate"))
        if kind == "subsume" and cs:
            base = rng.choice(cs)
            extra = rng.randint(1, n)
            if extra not in base and -extra not in base:
                cs.append(base + [extra])
        elif kind == "strengthen" and cs:
            base = list(rng.choice(cs))
            base[rng.randrange(len(base))] *= -1
            extra = rng.randint(1, n)
            cs.append(base + ([extra] if extra not in base and -extra not in base else []))
        elif kind == "block":
            # (l x ...) with every clause containing -l also containing -x
            l, x = rng.sample(range(1, n + 1), 2)
            l, x = _lit(rng, l), _lit(rng, x)
            cs = [c + [-x] if -l in c and x not in c and -x not in c else c for c in cs]
            cs = [c for c in cs if not (-l in c and x in c)]
            cs.append([l, x])
        elif kind == "pure":
            v = rng.randint(1, n)
            cs = [[l for l in c if l != -v] or [v] for c in cs]
            cs.append([v] + _random_clause(rng, n, 1))
        elif kind == "unit":
            cs.append([_lit(rng, rng.randint(1, n))])
        elif kind == "dup" and cs:
            cs.append(list(rng.choice(cs)))
        elif kind == "gate" and n >= 3:
            o, a, b = rng.sample(range(1, n + 1), 3)
            a, b = _lit(rng, a), _lit(rng, b)
            if rng.random() < 0.5:  # o <-> a & b
                cs += [[-o, a], [-o, b], [o, -a, -b]]
            else:  # o <-> a ^ b
                cs += [[-o, a, b], [-o, -a, -b], [o, -a, b], [o, a, -b]]
    return n, cs


def fam_unsat_core(rng):
    """Small unsatisfiable shapes in fresh variables, padded with satisfiable noise."""
    n = rng.randint(3, 12)
    vs = rng.sample(range(1, n + 1), n)
    a, b = _lit(rng, vs[0]), _lit(rng, vs[1])
    c = _lit(rng, vs[2])
    shape = rng.choice(("square", "cube", "units", "chain"))
    if shape == "square":
        cs = [[a, b], [a, -b], [-a, b], [-a, -b]]
    elif shape == "cube":
        cs = [[s1 * a, s2 * b, s3 * c] for s1 in (1, -1) for s2 in (1, -1) for s3 in (1, -1)]
    elif shape == "units":
        cs = [[a], [-a]]
    else:
        cs = [[a], [-a, b], [-b, c], [-c, -a]]
    cs += [_random_clause(rng, n, rng.choice((2, 3))) for _ in range(rng.randint(0, 2 * n))]
    rng.shuffle(cs)
    return n, cs


def fam_hard(rng):
    """Up to the oracle's limit, near the threshold, so a probe of a few conflicts runs out."""
    n = rng.randint(10, 16)
    m = int(n * rng.uniform(4.0, 5.5))
    return n, [_random_clause(rng, n, 3) for _ in range(m)]


def fam_sparse(rng):
    """Variable numbers far past 64, where the 64-bit subsumption signatures collide."""
    n, cs = fam_no_units(rng)
    top = rng.choice((70, 130, 300))
    names = rng.sample(range(1, top + 1), n)
    # a stride of 64 maps to one signature bit, the worst case for the filter
    if rng.random() < 0.5:
        names = [1 + (i * 64) for i in range(n)]
    renamed = [[names[abs(l) - 1] * (1 if l > 0 else -1) for l in c] for c in cs]
    return max(names), renamed


def fam_edge(rng):
    """Degenerate inputs: no clauses, unused variables, a literal repeated, a tautology."""
    n = rng.randint(1, 5)
    choice = rng.choice(("none", "repeat", "taut", "unused", "allunit"))
    if choice == "none":
        return n, []
    if choice == "repeat":
        return n, [[_lit(rng, rng.randint(1, n))] * 2 for _ in range(rng.randint(1, 4))]
    if choice == "taut":
        v = rng.randint(1, n)
        return n, [[v, -v], *[_random_clause(rng, n, 2) for _ in range(rng.randint(0, 3))]]
    if choice == "unused":
        return n + 3, [_random_clause(rng, n, rng.randint(1, 3)) for _ in range(rng.randint(1, 4))]
    return n, [[_lit(rng, v)] for v in range(1, n + 1)]


def fam_empty_clause(rng):
    """The empty clause, which CNF.add keeps on purpose, among ordinary clauses."""
    n, cs = fam_edge(rng)
    cs = cs + [[]]
    rng.shuffle(cs)
    return n, cs


FAMILIES = (
    ("random", fam_random, 26),
    ("no_units", fam_no_units, 30),
    ("planted", fam_planted, 30),
    ("unsat_core", fam_unsat_core, 10),
    ("hard", fam_hard, 6),
    ("sparse", fam_sparse, 3),
    ("edge", fam_edge, 3),
    ("empty_clause", fam_empty_clause, 1),
)


def to_cnf(n, cs):
    f = CNF(n)
    for c in cs:
        f.add([from_dimacs(d) for d in c])
    f.nvars = n
    return f


def internal_to_dimacs(clauses):
    return [[to_dimacs(l) for l in c] for c in clauses]


def satisfies(model, cs):
    """Own evaluation of DIMACS clauses under a list of bools, tautologies included."""
    return all(any(model[abs(l) - 1] == (l > 0) for l in c) for c in cs)


def oracle_sat(cs):
    return oracle.satisfiable([c for c in cs])


# --------------------------------------------------------------------------
# the harness
# --------------------------------------------------------------------------


class Report:
    def __init__(self):
        self.counts = collections.Counter()
        self.steps = 0
        self.mismatches = collections.Counter()
        self.examples = {}

    def bump(self, key, by=1):
        self.counts[key] += by

    def judge(self):
        self.steps += 1

    def flag(self, label, n, cs, cfg, detail=""):
        self.mismatches[label] += 1
        self.examples.setdefault(label, (n, [list(c) for c in cs], dict(cfg), str(detail)))


class TaggedPreprocessor(Preprocessor):
    """The real preprocessor, recording which pass pushed each stack entry.

    Used for the coverage counters only; no pass is changed.
    """

    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.tags = []

    def _tag(self, kind):
        self.tags += [kind] * (len(self.eliminated) - len(self.tags))

    def _pure_literals(self):
        super()._pure_literals()
        self._tag("pure")

    def block_eliminate(self):
        super().block_eliminate()
        self._tag("bce")

    def eliminate_vars(self):
        out = super().eliminate_vars()
        self._tag("bve")
        return out


def count_flips(pre, model, rep):
    """How many stack entries actually changed the value. Coverage only: the
    verdict comes from evaluating the input formula on reconstruct's answer."""
    if not hasattr(pre, "tags"):
        return
    full = list(model) + [False] * (pre.orig_nvars - len(model))
    for v, val in pre.value.items():
        full[v] = val
    sat = lambda c: any(full[l >> 1] != bool(l & 1) for l in c)
    for (v, clauses), tag in zip(reversed(pre.eliminated), reversed(pre.tags)):
        bad = [c for c in clauses if not sat(c)]
        if bad:
            full[v] = (v << 1) in bad[0]
            rep.bump(f"reconstruct_flip_{tag}")


def sample_models(rng, n, red, limit=MAX_MODELS_PER_RUN):
    """Models of `red`, with the variables it does not mention set adversarially.

    All-false, all-true and random fillings of the free variables, because a
    solver's default phases would only ever try one.
    """
    if any(len(c) == 0 for c in red):
        return []
    mentioned = sorted({abs(l) for c in red for l in c})
    free = [v for v in range(1, n + 1) if v not in mentioned]
    out = []
    space = 1 << len(mentioned)
    order = range(space) if space <= 256 else rng.sample(range(space), 256)
    fillings = [lambda v: False, lambda v: True, None]
    for bits in order:
        base = [False] * n
        for i, v in enumerate(mentioned):
            base[v - 1] = bool(bits >> i & 1)
        if not satisfies(base, red):
            continue
        for fill in fillings:
            m = list(base)
            for v in free:
                m[v - 1] = rng.random() < 0.5 if fill is None else fill(v)
            out.append(m)
            if not free:
                break
        if len(out) >= limit:
            break
    return out


def replay_flavour(cs, steps, flavour):
    """The first unacceptable addition under `flavour`, or None."""
    judged, _ = oracle.replay(cs, steps, flavour=flavour)
    for s in judged:
        if not s.acceptable:
            return s
    return None


def judge_proof_steps(rep, n, cs, steps, cfg, implied_only=True):
    """Replay against the original under dratify's documented rule."""
    if not steps:
        return
    judged, _ = oracle.replay(cs, steps, flavour="length-one")
    rep.judge()
    rep.steps += len(judged) - 1
    for s in judged:
        if s.kind == "a":
            rep.bump("proof_additions")
            if not s.rup:
                # every addition here is documented as RUP
                rep.flag("proof-step-not-rup", n, cs, cfg, s)
                return
            if implied_only and not oracle.implies(cs, s.clause):
                rep.flag("proof-step-not-implied-by-input", n, cs, cfg, s)
                return
        else:
            rep.bump("proof_deletions")
            if not s.present:
                rep.bump("proof_deletions_absent")
            if s.applied:
                rep.bump("proof_deletions_applied")
            elif len(set(s.clause)) <= 1:
                rep.bump("proof_unit_deletions_ignored")
    # the two other readings of deletion: a difference is a note, not a failure
    if replay_flavour(cs, steps, "operational") is not None:
        rep.flag("proof-fails-operational", n, cs, cfg, replay_flavour(cs, steps, "operational"))
    if replay_flavour(cs, steps, "specified") is not None:
        rep.bump("proof_fails_under_specified_flavour")
    else:
        rep.bump("proof_passes_under_specified_flavour")


def judge_preprocessed(rep, rng, n, cs, red, fsat, unsat_flag, reconstruct, cfg, frozen, is_sat_flag=None):
    """The checks common to both engines, on a finished preprocessing run."""
    # satisfiability both ways
    rep.judge()
    rsat = oracle_sat(red)
    if rsat != fsat:
        rep.flag("sat-not-preserved" if fsat else "unsat-not-preserved", n, cs, cfg,
                 f"reduced={red}")
        return
    if unsat_flag and fsat:
        rep.flag("unsat-flag-on-satisfiable", n, cs, cfg)
        return
    if unsat_flag:
        rep.bump("unsat_found_by_preprocessing")
    elif not fsat:
        rep.bump("unsat_left_for_the_solver")
    else:
        rep.bump("sat_runs")

    # every reduced clause follows from the input
    for c in red:
        rep.judge()
        if c and not oracle.implies(cs, c):
            rep.flag("reduced-clause-not-implied", n, cs, cfg, c)
            return

    # every model of the reduced formula reconstructs
    if fsat:
        for m in sample_models(rng, n, red):
            rep.judge()
            rep.bump("models_reconstructed")
            try:
                full = list(reconstruct(m))
            except Exception as e:  # noqa: BLE001 - the harness reports it
                rep.flag("reconstruct-raised", n, cs, cfg, f"{m}: {e!r}")
                return
            if len(full) < n or not satisfies(full, cs):
                rep.flag("reconstructed-model-wrong", n, cs, cfg, f"{m} -> {full}")
                return
            if frozen:
                rep.bump("frozen_model_checks")

    # a frozen variable's projection survives
    if frozen:
        implied_lits = {l for v in frozen for l in (v + 1, -(v + 1)) if oracle.implies(cs, [l])}
        free = [v for v in frozen if v + 1 not in implied_lits and -(v + 1) not in implied_lits]
        for bits in range(1 << len(frozen)):
            a = [(v + 1) if bits >> i & 1 else -(v + 1) for i, v in enumerate(frozen)]
            rep.judge()
            rep.bump("frozen_projection_checks")
            want = oracle_sat(cs + [[l] for l in a])
            consistent = all(-l not in implied_lits for l in a)
            kept = [l for l in a if abs(l) - 1 in free]
            got = consistent and oracle_sat(red + [[l] for l in kept])
            if want != got:
                rep.flag("frozen-projection-changed", n, cs, cfg, f"{a}: F={want} reduced={got}")
                return


def _solve_red(red_cnf, proof):
    s = Solver(red_cnf.nvars, proof=proof)
    ok = s.add_cnf(red_cnf)
    sat = bool(s.solve()) if ok else False
    return sat, (list(s.model) if sat else None)


def run_python(rep, rng, n, cs, fsat, cfg, factory=TaggedPreprocessor):
    f = to_cnf(n, cs)
    kw = {k: cfg[k] for k in ("do_bve", "do_bce", "max_resolvent_len", "elim_growth",
                              "subsumption_limit") if k in cfg}
    proof = MemoryProof() if cfg.get("proof") else None
    try:
        pre = factory(f, proof=proof, **kw)
        if cfg.get("freeze"):
            pre.freeze(cfg["freeze"])
        red_cnf = pre.run(rounds=cfg.get("rounds", 3))
    except Exception as e:  # noqa: BLE001
        label = "crash-empty-clause" if any(len(c) == 0 for c in cs) else "crash"
        rep.flag(label, n, cs, cfg, repr(e))
        rep.bump("crashes_python")
        return None
    rep.bump("runs_python")
    d = pre.stats.as_dict()
    judge_options(rep, n, cs, cfg, d)
    if to_cnf(n, cs).clauses != f.clauses:
        rep.flag("input-formula-mutated", n, cs, cfg)
    # what units fixed follows from the input, whatever was deleted before them
    for v, val in pre.value.items():
        rep.judge()
        if fsat and not oracle.implies(cs, [(v + 1) if val else -(v + 1)]):
            rep.flag("fixed-value-not-implied", n, cs, cfg, (v, val))
    for k in ("units", "subsumed", "strengthened", "eliminated_vars", "resolvents", "blocked",
              "pure", "tautologies"):
        rep.bump(f"py_{k}", d[k])
    red = internal_to_dimacs(red_cnf.clauses)

    def rec(m):
        count_flips(pre, m, rep)
        return pre.reconstruct(m)

    # the frozen variables must not be on the stack
    if cfg.get("freeze"):
        if set(cfg["freeze"]) & {v for v, _ in pre.eliminated}:
            rep.flag("frozen-variable-eliminated", n, cs, cfg)
    judge_preprocessed(rep, rng, n, cs, red, fsat, pre.unsat, rec, cfg, cfg.get("freeze"))

    if proof is not None:
        prep_steps = [(k, [to_dimacs(l) for l in c]) for k, c in proof.steps]
        judge_proof_steps(rep, n, cs, prep_steps, cfg)
        # the same run with no proof must do the same thing
        plain = factory(f, proof=None, **kw)
        if cfg.get("freeze"):
            plain.freeze(cfg["freeze"])
        plain_red = plain.run(rounds=cfg.get("rounds", 3))
        rep.judge()
        if plain_red.clauses != red_cnf.clauses:
            rep.flag("proof-changes-result", n, cs, cfg)
        finish_proof(rep, n, cs, f, fsat, red_cnf, proof, cfg, steps_are_internal=True)
    else:
        sat, model = _solve_red(red_cnf, None)
        rep.judge()
        if sat != fsat:
            rep.flag("verdict-wrong-after-preprocessing", n, cs, cfg)
        elif sat:
            try:
                full = pre.reconstruct(model)
            except Exception as e:  # noqa: BLE001 - the harness reports it
                rep.flag("reconstruct-raised", n, cs, cfg, f"{model}: {e!r}")
            else:
                if not satisfies(full, cs):
                    rep.flag("reconstructed-model-wrong", n, cs, cfg, f"{model} -> {full}")
    return pre


def judge_options(rep, n, cs, cfg, stats):
    """An option that is off stays off; a cap of zero admits no resolvent."""
    rep.judge()
    if cfg.get("do_bce") is False and stats["blocked"]:
        rep.flag("do_bce-off-ignored", n, cs, cfg, stats)
    if cfg.get("do_bve") is False and stats["resolvents"]:
        rep.flag("do_bve-off-ignored", n, cs, cfg, stats)
    if cfg.get("max_resolvent_len") == 0 and stats["resolvents"]:
        rep.flag("max_resolvent_len-ignored", n, cs, cfg, stats)


def run_composed(rep, rng, n, cs, fsat, factory):
    """Preprocessing a reduced formula, and running twice: stacks must compose."""
    f = to_cnf(n, cs)
    try:
        first = factory(f)
        red1 = first.run()
        second = factory(red1)
        red2 = second.run()
        twice = factory(f)
        twice.run(1)
        red3 = twice.run(2)
    except Exception as e:  # noqa: BLE001 - the harness reports it
        if any(len(c) == 0 for c in cs):
            return  # labelled where the input itself is first run
        # an UNSAT reduction returns the empty clause, which then cannot be
        # preprocessed again
        label = "crash-reduced-empty-clause" if first.unsat else "crash"
        rep.flag(label, n, cs, {"composed": True}, repr(e))
        return
    rep.bump("composed_runs")
    judge_preprocessed(rep, rng, n, cs, internal_to_dimacs(red2.clauses), fsat, second.unsat,
                       lambda m: first.reconstruct(second.reconstruct(m)), {"composed": True}, None)
    judge_preprocessed(rep, rng, n, cs, internal_to_dimacs(red3.clauses), fsat, twice.unsat,
                       twice.reconstruct, {"run_twice": True}, None)


def finish_proof(rep, n, cs, f, fsat, red_cnf, proof, cfg, steps_are_internal):
    """Run the search on the reduced formula into the same proof, then judge."""
    sat, _ = _solve_red(red_cnf, proof)
    rep.judge()
    if sat != fsat:
        rep.flag("verdict-wrong-after-preprocessing", n, cs, cfg)
        return
    judge_combined(rep, n, cs, f, sat, proof, cfg)


def judge_combined(rep, n, cs, f, sat, proof, cfg):
    steps = [(k, [to_dimacs(l) for l in c]) for k, c in proof.steps]
    if sat:
        return
    rep.bump("combined_refutations")
    judged, final = oracle.replay(cs, steps, flavour="length-one")
    rep.judge()
    bad = [s for s in judged if not s.acceptable]
    if bad:
        rep.flag("combined-proof-step-bad", n, cs, cfg, bad[0])
        return
    if not oracle.propagate(final)[0]:
        rep.flag("combined-proof-not-a-refutation", n, cs, cfg, final)
        return
    if not any(s.kind == "a" and not s.clause for s in judged) and not any(not c for c in cs):
        rep.flag("combined-proof-has-no-empty-clause", n, cs, cfg)
        return
    for engine in ("python", "native") if native_mod.available() else ("python",):
        res = check_proof(f, proof, engine=engine)
        rep.judge()
        if res.ok == oracle_sat(cs):
            rep.flag("dratify-verdict-wrong-on-combined-proof", n, cs, cfg,
                     f"{engine}: {res.report()}")
        rep.bump(f"combined_checked_{engine}")


def run_native(rep, rng, n, cs, fsat, cfg):
    nat = native_mod.require()
    f = to_cnf(n, cs)
    kw = {}
    if "do_bve" in cfg:
        kw["do_bve"] = cfg["do_bve"]
    if "max_resolvent_len" in cfg:
        kw["max_resolvent_len"] = cfg["max_resolvent_len"]
    if cfg.get("proof"):
        kw["with_proof"] = True
    try:
        p = nat.Preprocessor(n, **kw)
        for c in f.clauses:
            p.add_clause(list(c))
        for v in cfg.get("freeze") or ():
            p.freeze(v)
        p.run(cfg.get("rounds", 3))
    except BaseException as e:  # a Rust panic arrives as a BaseException
        if isinstance(e, (KeyboardInterrupt, SystemExit)):
            raise
        label = "crash-empty-clause" if any(len(c) == 0 for c in cs) else "crash"
        rep.flag(label, n, cs, cfg, f"native: {e!r}")
        rep.bump("crashes_native")
        return None
    rep.bump("runs_native")
    rep.bump("native_eliminated_vars", p.eliminated_vars)
    rep.bump("native_subsumed", p.subsumed)
    rep.bump("native_strengthened", p.strengthened)
    rep.bump("native_pure", p.pure)
    rep.bump("native_units", p.units)
    rep.bump("native_resolvents", p.resolvents)
    judge_options(rep, n, cs, cfg, {"blocked": 0, "resolvents": p.resolvents})
    red = [[to_dimacs(l) for l in c] for c in p.reduced()]
    judge_preprocessed(rep, rng, n, cs, red, fsat, p.unsat, p.reconstruct, cfg, cfg.get("freeze"))
    if cfg.get("proof"):
        steps = [(k, list(c)) for k, c in p.proof_steps()]
        judge_proof_steps(rep, n, cs, steps, cfg)
        proof = MemoryProof()
        for k, c in steps:
            (proof.delete if k == "d" else proof.add)([from_dimacs(d) for d in c])
        red_cnf = to_cnf(n, red)
        finish_proof(rep, n, cs, f, fsat, red_cnf, proof, cfg, steps_are_internal=True)
    return p


def run_parity(rep, n, cs, cfg):
    """Python with BCE off against native, which has no BCE, on what both expose."""
    if not native_mod.available():
        return
    nat = native_mod.require()
    f = to_cnf(n, cs)
    try:
        py = Preprocessor(f, do_bce=False, do_bve=cfg["do_bve"])
        py_red = py.run(cfg.get("rounds", 3))
        p = nat.Preprocessor(n, do_bve=cfg["do_bve"])
        for c in f.clauses:
            p.add_clause(list(c))
        p.run(cfg.get("rounds", 3))
    except BaseException as e:  # noqa: BLE001 - empty-clause crashes are counted elsewhere
        if isinstance(e, (KeyboardInterrupt, SystemExit)):
            raise
        return
    rep.judge()
    rep.bump("parity_runs")
    canon = lambda clauses: sorted(sorted(c) for c in clauses)
    a, b = canon(py_red.clauses), canon(p.reduced())
    if a != b:
        rep.bump("parity_reduced_differs")
        rep.flag("parity-reduced", n, cs, dict(cfg, compare="reduced"), f"python={a} native={b}")
    d = py.stats.as_dict()
    for field in ("units", "subsumed", "strengthened", "eliminated_vars", "resolvents", "pure"):
        if d[field] != getattr(p, field):
            rep.bump("parity_stats_differs")
            rep.flag("parity-stats", n, cs, dict(cfg, compare=field),
                     f"{field}: python={d[field]} native={getattr(p, field)}")
            break
    if py.unsat != p.unsat:
        rep.flag("parity-unsat-flag", n, cs, cfg, f"python={py.unsat} native={p.unsat}")


def run_adaptive(rep, n, cs, fsat, cfg):
    """solve_adaptive on both engines, forced and through the probe."""
    f = to_cnf(n, cs)
    results = {}
    for engine in ("python", "native") if native_mod.available() else ("python",):
        proof = MemoryProof() if cfg.get("proof") else None
        kw = dict(cfg["mode"])
        try:
            r = solve_adaptive(f, engine=engine, proof=proof, **kw)
        except BaseException as e:
            if isinstance(e, (KeyboardInterrupt, SystemExit)):
                raise
            label = "crash-empty-clause" if any(len(c) == 0 for c in cs) else "crash"
            rep.flag(label, n, cs, dict(cfg, engine=engine), f"adaptive {engine}: {e!r}")
            continue
        results[engine] = r
        rep.judge()
        rep.bump(f"adaptive_{engine}")
        if r.preprocessed:
            rep.bump("adaptive_preprocessed")
            if r.probe_conflicts:
                rep.bump("adaptive_probe_exhausted_then_preprocessed")
                if proof is not None:
                    rep.bump("adaptive_probe_then_preprocess_with_proof")
                    if not fsat:
                        rep.bump("adaptive_probe_then_preprocess_refuted")
                    if engine == "python":
                        rep.bump("adaptive_probe_lemmas_in_python_proof")
        if bool(r.sat) != fsat:
            rep.flag("adaptive-verdict-wrong", n, cs, dict(cfg, engine=engine), r.sat)
            continue
        if r.sat:
            if not satisfies(r.model, cs):
                rep.flag("adaptive-model-wrong", n, cs, dict(cfg, engine=engine), r.model)
        elif proof is not None:
            judge_combined(rep, n, cs, f, False, proof, dict(cfg, engine=engine))
    if len(results) == 2:
        py, na = results["python"], results["native"]
        rep.bump("parity_adaptive_runs")
        for field in ("sat", "preprocessed", "clauses_before", "clauses_after", "conflicts",
                      "model"):
            if getattr(py, field) != getattr(na, field):
                rep.bump(f"parity_adaptive_{field}_differs")
                rep.flag("parity-adaptive", n, cs, dict(cfg, compare=field),
                         f"{field}: python={getattr(py, field)} native={getattr(na, field)}")
                break


def run_cli(rep, n, cs, fsat, cfg, tmp):
    """The two CLI paths into preprocessing, in-process."""
    path = pathlib.Path(tmp) / "f.cnf"
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in cs)
    path.write_text(f"p cnf {n} {len(cs)}\n{body}")
    out = io.StringIO()
    checks = ["--check-model", "--self-check"] if cfg.get("checks", True) else []
    proof_file = pathlib.Path(tmp) / "f.drat"
    proof_file.unlink(missing_ok=True)
    extra = ["--proof", str(proof_file)] if cfg.get("proof_file") else []
    argv = ["solve", str(path), *checks, *extra, *cfg["argv"]]
    try:
        with contextlib.redirect_stdout(out):
            code = cdclkit_cli.main(argv)
    except BaseException as e:
        if isinstance(e, (KeyboardInterrupt, SystemExit)):
            raise
        label = "crash-empty-clause" if any(len(c) == 0 for c in cs) else "crash"
        if label == "crash" and "--preprocess" in argv and "-j" in argv:
            label = "crash-reduced-empty-clause"
        rep.flag(label, n, cs, cfg, f"cli {argv[2:]}: {e!r}")
        return
    rep.judge()
    rep.bump("cli_solve_runs")
    want = 10 if fsat else 20
    if code != want and any(len(c) == 0 for c in cs):
        # main() turns the Python preprocessor's ValueError into exit 1
        rep.flag("crash-empty-clause", n, cs, cfg, f"exit {code}, want {want}")
        return
    if code != want:
        rep.flag("cli-exit-code-wrong", n, cs, cfg,
                 f"exit {code}, want {want}: {out.getvalue()[-400:]}")
        return
    if cfg.get("proof_file") and not fsat:
        steps = parse_drat_text(proof_file.read_text())
        rep.bump("cli_proof_files_replayed")
        judged, final = oracle.replay(cs, steps, flavour="length-one")
        rep.judge()
        bad = [s for s in judged if not s.acceptable]
        if bad or not oracle.propagate(final)[0]:
            rep.flag("cli-proof-file-bad", n, cs, cfg, bad[:1])
    if fsat:
        vals = [int(t) for line in out.getvalue().splitlines() if line.startswith("v ")
                for t in line[2:].split()]
        model = [False] * n
        for t in vals:
            if t:
                model[abs(t) - 1] = t > 0
        if not satisfies(model, cs):
            rep.flag("cli-model-wrong", n, cs, cfg, vals)


def parse_drat_text(text):
    steps = []
    for line in text.splitlines():
        tokens = line.split()
        if not tokens:
            continue
        kind = "d" if tokens[0] == "d" else "a"
        lits = [int(t) for t in tokens[1 if kind == "d" else 0:]]
        assert lits and lits[-1] == 0, line
        steps.append((kind, lits[:-1]))
    return steps


def run_cli_prep(rep, n, cs, fsat, cfg, tmp):
    from dratify.cnf import parse_dimacs

    path = pathlib.Path(tmp) / "f.cnf"
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in cs)
    path.write_text(f"p cnf {n} {len(cs)}\n{body}")
    outp = pathlib.Path(tmp) / "red.cnf"
    outp.unlink(missing_ok=True)
    argv = ["prep", str(path), "--out", str(outp), *cfg["argv"]]
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            code = cdclkit_cli.main(argv)
    except BaseException as e:
        if isinstance(e, (KeyboardInterrupt, SystemExit)):
            raise
        label = "crash-empty-clause" if any(len(c) == 0 for c in cs) else "crash"
        rep.flag(label, n, cs, dict(cfg, prep=True), f"cli prep {argv[2:]}: {e!r}")
        return
    rep.judge()
    rep.bump("cli_prep_runs")
    if code != 0 or not outp.exists():
        label = "crash-empty-clause" if any(len(c) == 0 for c in cs) else "cli-prep-failed"
        rep.flag(label, n, cs, dict(cfg, prep=True), f"exit {code}")
        return
    red = internal_to_dimacs(parse_dimacs(outp.read_text()).clauses)
    if oracle_sat(red) != fsat:
        rep.flag("cli-prep-sat-changed", n, cs, dict(cfg, prep=True), red)


def run_portfolio(rep, n, cs, fsat, cfg):
    f = to_cnf(n, cs)
    try:
        pr = solve_portfolio(f, jobs=cfg["jobs"], engine=cfg["engine"],
                             preprocess_workers=cfg["preprocess_workers"])
    except BaseException as e:
        if isinstance(e, (KeyboardInterrupt, SystemExit)):
            raise
        label = "crash-empty-clause" if any(len(c) == 0 for c in cs) else "crash"
        rep.flag(label, n, cs, cfg, f"portfolio: {e!r}")
        return
    rep.judge()
    rep.bump("portfolio_runs")
    if not pr.finished or bool(pr.sat) != fsat:
        rep.flag("portfolio-verdict-wrong", n, cs, cfg, pr.sat)
    elif pr.sat and not satisfies(pr.model, cs):
        rep.flag("portfolio-model-wrong", n, cs, cfg, pr.model)


# --------------------------------------------------------------------------
# the campaign
# --------------------------------------------------------------------------

#: each technique's option, on and off, crossed
BASE_GRID = [
    {"do_bve": b, "do_bce": c} for b in (True, False) for c in (True, False)
]


def random_cfg(rng, n):
    cfg = {
        "do_bve": rng.random() < 0.7,
        "do_bce": rng.random() < 0.7,
        "max_resolvent_len": rng.choice((20, 20, 3, 2, 1, 0)),
        "elim_growth": rng.choice((0, 0, 1, 4, 16, -1)),
        "subsumption_limit": rng.choice((2_000_000, 2_000_000, 0, 1, 5)),
        "rounds": rng.choice((0, 1, 2, 3, 3, 6)),
    }
    return cfg


def one_instance(rep, rng, family, n, cs, tmp, index, factory=TaggedPreprocessor):
    fsat = oracle_sat(cs)
    rep.bump("formulas_sat" if fsat else "formulas_unsat")
    rep.bump(f"family_{family}")

    # the grid, proof on (every proof is replayed) and off
    for base in BASE_GRID:
        run_python(rep, rng, n, cs, fsat, dict(base, proof=True), factory)
        rep.bump(f"grid_bve{int(base['do_bve'])}_bce{int(base['do_bce'])}")
    run_python(rep, rng, n, cs, fsat, {"proof": False}, factory)

    # a random point in the rest of the option space
    cfg = random_cfg(rng, n)
    cfg["proof"] = rng.random() < 0.5
    if rng.random() < 0.5 and n >= 1:
        cfg["freeze"] = rng.sample(range(n), min(n, rng.randint(1, 3)))
    run_python(rep, rng, n, cs, fsat, cfg, factory)
    rep.bump("random_config_runs")
    run_composed(rep, rng, n, cs, fsat, factory)

    if factory is not TaggedPreprocessor or not native_mod.available():
        return

    # native: its options on and off
    for bve in (True, False):
        run_native(rep, rng, n, cs, fsat, {"do_bve": bve, "proof": True})
    ncfg = {"do_bve": rng.random() < 0.7,
            "max_resolvent_len": rng.choice((20, 20, 3, 2, 1, 0)),
            "rounds": rng.choice((0, 1, 2, 3, 3, 6)),
            "proof": rng.random() < 0.5}
    if rng.random() < 0.5:
        ncfg["freeze"] = rng.sample(range(n), min(n, rng.randint(1, 3)))
    run_native(rep, rng, n, cs, fsat, ncfg)

    run_parity(rep, n, cs, {"do_bve": True})
    run_parity(rep, n, cs, {"do_bve": False})

    # pipeline: the probe matters because the Python path logs its lemmas ahead
    # of preprocessing, and a tiny budget is what makes the probe run out here
    mode = rng.choice(({"always_preprocess": True}, {"always_preprocess": True},
                       {"probe": 1}, {"probe": 2}, {"probe": 4}, {"never_preprocess": True}, {}))
    run_adaptive(rep, n, cs, fsat, {"mode": mode, "proof": True})
    if index % 4 == 0:
        run_adaptive(rep, n, cs, fsat, {"mode": {"probe": 1}, "proof": True})

    if index % 10 == 0:
        # without --check-model nothing inside the CLI looks at the model, so
        # what it prints is judged here; with it, the exit code is judged too
        argv = rng.choice(CLI_ROUTES)
        run_cli(rep, n, cs, fsat, {"argv": argv, "checks": True}, tmp)
        run_cli(rep, n, cs, fsat, {"argv": argv, "checks": False}, tmp)
        rep.bump("cli_route_" + "_".join(a.strip("-") for a in argv))
        if "-j" not in argv:
            run_cli(rep, n, cs, fsat, {"argv": argv, "checks": False, "proof_file": True}, tmp)
        run_cli_prep(rep, n, cs, fsat,
                     {"argv": rng.choice(([], ["--no-bve"], ["--no-bce"], ["--no-bve", "--no-bce"]))},
                     tmp)
    if index % 25 == 0:
        run_adaptive(rep, n, cs, fsat, {"mode": {"always_preprocess": True, "jobs": 2}})
        rep.bump("adaptive_parallel_after_preprocessing")
    if index % 40 == 0:
        run_portfolio(rep, n, cs, fsat, {"jobs": 3, "engine": "native",
                                         "preprocess_workers": rng.randint(1, 2)})
    if index % 200 == 0:
        run_portfolio(rep, n, cs, fsat, {"jobs": 2, "engine": "python", "preprocess_workers": 1})


CLI_ROUTES = (
    ["--preprocess"],
    ["--preprocess", "--prep-rounds", "0"],
    ["--preprocess", "--prep-rounds", "1"],
    ["--adaptive"],
    ["--preprocess", "--adaptive"],
    ["--preprocess", "-j", "2"],
    ["-j", "2"],
)


def pick_family(rng):
    total = sum(w for _, _, w in FAMILIES)
    x = rng.randrange(total)
    for name, fn, w in FAMILIES:
        if x < w:
            return name, fn
        x -= w
    raise AssertionError


#: every category this generator claims to reach; zero fails the run
REQUIRED = """
py_units py_subsumed py_strengthened py_eliminated_vars py_resolvents py_blocked py_pure
py_tautologies grid_bve1_bce1 grid_bve1_bce0 grid_bve0_bce1 grid_bve0_bce0 random_config_runs
formulas_sat formulas_unsat sat_runs unsat_found_by_preprocessing unsat_left_for_the_solver
reconstruct_flip_pure reconstruct_flip_bce reconstruct_flip_bve models_reconstructed
frozen_model_checks frozen_projection_checks proof_additions proof_deletions
proof_deletions_applied proof_unit_deletions_ignored combined_refutations
combined_checked_python composed_runs proof_fails_under_specified_flavour
proof_passes_under_specified_flavour
""".split()

REQUIRED_NATIVE = """
runs_native native_eliminated_vars native_subsumed native_strengthened native_pure native_units
native_resolvents combined_checked_native parity_runs parity_adaptive_runs adaptive_python
adaptive_native adaptive_preprocessed adaptive_probe_exhausted_then_preprocessed
adaptive_probe_then_preprocess_with_proof adaptive_probe_then_preprocess_refuted
adaptive_probe_lemmas_in_python_proof adaptive_parallel_after_preprocessing
cli_proof_files_replayed cli_solve_runs cli_prep_runs portfolio_runs
""".split()


def campaign(seed, instances, factory=TaggedPreprocessor, required=True):
    rep = Report()
    with tempfile.TemporaryDirectory() as tmp:
        for i in range(instances):
            rng = random.Random(f"preprocess:{seed}:{i}")
            family, fn = pick_family(rng)
            n, cs = fn(rng)
            one_instance(rep, rng, family, n, cs, tmp, i, factory)
    missing = []
    if required:
        need = REQUIRED + (REQUIRED_NATIVE if native_mod.available() else [])
        missing = [k for k in need if rep.counts[k] == 0]
    return rep, missing


# --------------------------------------------------------------------------
# shrinking
# --------------------------------------------------------------------------


def still_fails(n, cs, cfg, label):
    rep = Report()
    with tempfile.TemporaryDirectory() as tmp:
        try:
            rng = random.Random(0)
            fsat = oracle_sat(cs)
            if "mode" in cfg:
                run_adaptive(rep, n, cs, fsat, cfg)
            elif "compare" in cfg:
                run_parity(rep, n, cs, cfg)
            elif "prep" in cfg:
                run_cli_prep(rep, n, cs, fsat, cfg, tmp)
            elif "argv" in cfg:
                run_cli(rep, n, cs, fsat, cfg, tmp)
            elif "jobs" in cfg:
                run_portfolio(rep, n, cs, fsat, cfg)
            elif "do_bce" in cfg or "elim_growth" in cfg:
                run_python(rep, rng, n, cs, fsat, cfg)
            else:
                run_python(rep, rng, n, cs, fsat, cfg)
                run_native(rep, rng, n, cs, fsat, cfg)
        except Exception:  # noqa: BLE001 - a shrink candidate that breaks the harness
            return False
    return rep.mismatches[label] > 0


def shrink(n, cs, cfg, label):
    cs = [list(c) for c in cs]
    # a clause shrunk to nothing is a different bug: keep the case it started as
    floor = 0 if any(not c for c in cs) else 1
    changed = True
    while changed:
        changed = False
        for i in range(len(cs) - 1, -1, -1):
            cand = cs[:i] + cs[i + 1:]
            if still_fails(n, cand, cfg, label):
                cs, changed = cand, True
        for i in range(len(cs)):
            for j in range(len(cs[i]) - 1, -1, -1):
                if len(cs[i]) <= floor:
                    break
                cand = [list(c) for c in cs]
                del cand[i][j]
                if still_fails(n, cand, cfg, label):
                    cs, changed = cand, True
                    break
    used = sorted({abs(l) for c in cs for l in c})
    remap = {v: i + 1 for i, v in enumerate(used)}
    renamed = [[(remap[abs(l)] if l > 0 else -remap[abs(l)]) for l in c] for c in cs]
    if used and still_fails(len(used), renamed, cfg, label):
        return len(used), renamed
    return n, cs


# --------------------------------------------------------------------------
# self-test: the harness must flag preprocessors that are wrong
# --------------------------------------------------------------------------


class DropsEverything(Preprocessor):
    """Returns the empty formula: loses unsatisfiability, and its models are wrong."""

    def run(self, rounds=3):
        return CNF(self.orig_nvars)

    def reconstruct(self, model):
        return list(model)[: self.orig_nvars] + [False] * (self.orig_nvars - len(model))


class ForgetsReconstruction(Preprocessor):
    """Correct reduction, but returns the reduced model unchanged."""

    def reconstruct(self, model):
        return list(model)


class ReconstructWithoutValues(Preprocessor):
    """Walks the stack but forgets the assignments that units fixed."""

    def reconstruct(self, model):
        saved, self.value = self.value, {}
        try:
            return super().reconstruct(model)
        finally:
            self.value = saved


class LosesSatisfiability(Preprocessor):
    """Adds a clause that does not follow, logged as if it did."""

    def run(self, rounds=3):
        self._add_clause((1,))  # the unit ~x0
        self._add_clause((0,))  # and x0
        return super().run(rounds)


class ForgesUnit(Preprocessor):
    """Adds an unjustified unit to the proof and to the formula."""

    def run(self, rounds=3):
        self._add_clause((0,))
        return super().run(rounds)


class IgnoresFreeze(Preprocessor):
    """Eliminates frozen variables anyway."""

    def freeze(self, variables):
        pass

    def reconstruct(self, model):
        return super().reconstruct(model)


class EliminatesWithoutStack(Preprocessor):
    """BCE and BVE as written, but nothing on the stack."""

    def run(self, rounds=3):
        out = super().run(rounds)
        self.eliminated = []
        return out


STUBS = (
    ("drops every clause", DropsEverything, "unsat-not-preserved"),
    ("reconstruct returns its input", ForgetsReconstruction, "reconstructed-model-wrong"),
    ("reconstruct forgets unit values", ReconstructWithoutValues, "reconstructed-model-wrong"),
    ("adds a contradiction", LosesSatisfiability, "sat-not-preserved"),
    ("forges a unit", ForgesUnit, "proof-step-not-rup"),
    ("empties the elimination stack", EliminatesWithoutStack, "reconstructed-model-wrong"),
    ("ignores freeze", IgnoresFreeze, "frozen-projection-changed"),
)


def self_test(seed, instances):
    failed = 0
    for name, cls, label in STUBS:
        rep, _ = campaign(seed, instances, factory=cls, required=False)
        hit = rep.mismatches[label]
        print(f"  stub '{name}': {hit} x {label}  (all labels: {dict(rep.mismatches)})")
        if not hit:
            print(f"    NOT FLAGGED: expected {label}")
            failed += 1
    # the coverage rule itself: a campaign with no instances has to report zero
    # counters as missing, or a generator that reaches nothing could pass
    _, missing = campaign(seed, 0)
    print(f"  zero instances: {len(missing)} categories reported missing")
    if not missing:
        failed += 1
    # the true preprocessor is not flagged for any of the labels above
    rep, _ = campaign(seed, instances)
    wrong = {k: v for k, v in rep.mismatches.items() if k in {s[2] for s in STUBS}}
    print(f"  real preprocessor on those labels: {wrong or 'none'}")
    if wrong:
        failed += 1
    return failed


# --------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seed", type=int, default=20261108)
    ap.add_argument("--instances", type=int, default=600)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--shrink", action="store_true", help="shrink one example per label")
    ap.add_argument("--json", help="write the results here")
    args = ap.parse_args(argv)

    if args.self_test:
        failed = self_test(args.seed, min(args.instances, 120))
        print("self-test FAILED" if failed else "self-test passed")
        return 1 if failed else 0

    t0 = time.perf_counter()
    rep, missing = campaign(args.seed, args.instances)
    runtime = time.perf_counter() - t0

    print(f"seed={args.seed} instances={args.instances} steps={rep.steps} runtime={runtime:.1f}s")
    for k in sorted(rep.counts):
        print(f"  {k}: {rep.counts[k]}")
    failing = 0
    for label, count in sorted(rep.mismatches.items()):
        n, cs, cfg, detail = rep.examples[label]
        finding = KNOWN.get(label)
        if finding is None:
            tag = "UNEXPLAINED"
        elif status.state(finding) == "fixed":
            tag = f"REGRESSION {finding}"
        else:
            tag = f"open {finding}"
        failing += count if tag != f"open {finding}" else 0
        print(f"MISMATCH [{tag}] {label}: {count}")
        if args.shrink:
            n, cs = shrink(n, cs, cfg, label)
        print(f"  n={n} clauses={cs}\n  cfg={cfg}\n  {detail[:300]}")
    if missing:
        print(f"CATEGORY AT ZERO: {missing}")
    if args.json:
        pathlib.Path(args.json).write_text(json.dumps(
            {"corner": "preprocess", "seeds": [args.seed], "instances": args.instances,
             "steps": rep.steps,
             "per_category_counts": dict(sorted(rep.counts.items())),
             "mismatches": dict(sorted(rep.mismatches.items())),
             "regressions_or_unexplained": failing,
             "runtime_seconds": round(runtime, 1),
             "findings": [{**f, "status": status.state(f["id"])} for f in FINDINGS],
             "not_checked": NOT_CHECKED}, indent=2) + "\n")
    return 1 if failing or missing else 0


if __name__ == "__main__":
    sys.exit(main())
