# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Choosing when to preprocess, instead of always or never.

Preprocessing is worth 1.3-1.5x on structured instances and a dead loss on
instances that solve in milliseconds -- `bench/compare.py` measures both. The
crafted families in the benchmark set finish in under a millisecond, so any
preprocessing at all is a hundredfold overhead; the factoring and colouring
instances take seconds, and preprocessing pays for itself several times over.

Deciding by looking at the formula does not work well. Clause count is a poor
predictor: `queens(40)` has 18 611 clauses and solves in zero conflicts, while
`factor(16b)` has 8 051 and needs sixteen thousand. Size tells you how big the
formula is, not how hard it is.

So this asks the solver instead. Run with a small conflict budget; if the
instance falls over quickly, nothing was spent. If the budget is exhausted, the
instance is hard enough that preprocessing will repay its cost, so preprocess
and solve properly. The wasted work is bounded by the budget and the learnt
clauses from the probe are discarded -- a real cost, but a fixed and small one
against an unbounded win.

The policy is deliberately simple and its parameter is exposed, because the
right budget depends on the ratio between preprocessing cost and solve cost on
the machine in front of you.
"""

from __future__ import annotations

import time
from typing import Sequence

from dratify.cnf import CNF
from .solver import Config, Solver

__all__ = ["solve_adaptive", "PipelineResult"]

#: Conflicts to spend probing before deciding to preprocess.  At ~100k
#: conflicts/second on the native engine this is a ~10 ms probe, which is
#: cheaper than the fastest preprocessing run measured (~1 ms native, ~3 ms
#: Python) on anything but the smallest instances, and negligible against the
#: seconds-long solves where preprocessing matters.
DEFAULT_PROBE = 1000


class PipelineResult:
    __slots__ = ("sat", "model", "conflicts", "seconds", "preprocessed",
                 "probe_conflicts", "prep_seconds", "clauses_before",
                 "clauses_after")

    def __init__(self) -> None:
        self.sat: bool | None = None
        self.model: list[bool] | None = None
        self.conflicts = 0
        self.seconds = 0.0
        self.preprocessed = False
        self.probe_conflicts = 0
        self.prep_seconds = 0.0
        self.clauses_before = 0
        self.clauses_after = 0

    def report(self) -> str:
        if not self.preprocessed:
            return (f"c solved during the {self.probe_conflicts}-conflict probe; "
                    f"preprocessing skipped")
        return (f"c probe exhausted at {self.probe_conflicts} conflicts -> "
                f"preprocessed {self.clauses_before} -> {self.clauses_after} "
                f"clauses in {self.prep_seconds*1000:.0f} ms")


def _native_available() -> bool:
    from . import native

    return native.available()


def _solve(f: CNF, cfg: Config, budget: int | None, engine: str,
           seconds: float | None = None):
    """Returns (status, model, conflicts).  status None means budget exhausted."""
    if engine == "native":
        from . import native

        n = native.require()
        s = n.Solver(
            f.nvars, restart=cfg.restart, ccmin=cfg.ccmin,
            phase_saving=cfg.phase_saving, init_phase=cfg.init_phase,
            target_phase=cfg.target_phase, target_reset=cfg.target_reset,
            walk_flips=cfg.walk_flips, walk_interval=cfg.walk_interval,
            walk_patience=cfg.walk_patience,
            walk_min_conflicts=cfg.walk_min_conflicts,
            var_decay=cfg.var_decay, var_decay_max=cfg.var_decay_max,
            cla_decay=cfg.cla_decay, luby_base=float(cfg.luby_base),
            first_reduce=cfg.first_reduce, reduce_inc=cfg.reduce_inc,
            glue_keep=cfg.glue_keep, block_restart=cfg.block_restart,
            rnd_freq=cfg.rnd_freq, rnd_seed=cfg.rnd_seed,
        )
        for c in f.clauses:
            if not s.add_clause(list(c)):
                return False, None, s.conflicts
        res = s.solve(budget, seconds)
        if res is None:
            return None, None, s.conflicts
        return res, (list(s.model) if res else None), s.conflicts

    s = Solver(f.nvars, config=cfg)
    if not s.add_cnf(f):
        return False, None, s.stats.conflicts
    res = s.solve(max_conflicts=budget, deadline=(
        None if seconds is None else time.perf_counter() + seconds))
    if res is None:
        return None, None, s.stats.conflicts
    return res, (list(s.model) if res else None), s.stats.conflicts


def _preprocess(f: CNF, engine: str):
    """Returns (reduced_formula, unsat, reconstruct_fn, seconds)."""
    t0 = time.perf_counter()
    if engine == "native" and _native_available():
        from . import native

        n = native.require()
        p = n.Preprocessor(f.nvars)
        for c in f.clauses:
            p.add_clause(list(c))
        p.run(3)
        red = CNF(f.nvars)
        for c in p.reduced():
            red.add(c)
        red.nvars = f.nvars
        return red, p.unsat, p.reconstruct, time.perf_counter() - t0

    from .preprocess import Preprocessor

    p = Preprocessor(f)
    red = p.run()
    return red, p.unsat, p.reconstruct, time.perf_counter() - t0


def solve_adaptive(
    f: CNF,
    engine: str = "native",
    probe: int = DEFAULT_PROBE,
    config: Config | None = None,
    always_preprocess: bool = False,
    never_preprocess: bool = False,
    jobs: int = 1,
    seconds: float | None = None,
) -> PipelineResult:
    """Solve `f`, preprocessing only when a short probe says it is worth it.

    `engine` selects "native" (falling back to Python when the module is
    absent) or "python". `always_preprocess` / `never_preprocess` force the
    decision, which is what the benchmark harness uses to measure the policy
    against its own extremes.

    `jobs > 1` runs the *post-probe* solve as a parallel portfolio. The probe
    itself stays sequential and in-process on purpose: spawning five workers
    costs ~60 ms, which is more than an easy instance takes to solve outright,
    so paying it before knowing the instance is hard would throw away exactly
    what the probe is for.
    """
    cfg = config or Config()
    if engine == "native" and not _native_available():
        engine = "python"

    r = PipelineResult()
    r.clauses_before = f.nclauses
    t_start = time.perf_counter()

    if not never_preprocess and not always_preprocess:
        status, model, conflicts = _solve(f, cfg, probe, engine)
        r.probe_conflicts = conflicts
        if status is not None:
            r.sat, r.model, r.conflicts = status, model, conflicts
            r.seconds = time.perf_counter() - t_start
            r.clauses_after = f.nclauses
            return r

    if never_preprocess:
        status, model, conflicts = _solve(f, cfg, None, engine, seconds)
        r.sat, r.model, r.conflicts = status, model, conflicts
        r.seconds = time.perf_counter() - t_start
        r.clauses_after = f.nclauses
        return r

    red, unsat, reconstruct, prep_s = _preprocess(f, engine)
    r.preprocessed = True
    r.prep_seconds = prep_s
    r.clauses_after = red.nclauses

    if unsat:
        r.sat = False
        r.seconds = time.perf_counter() - t_start
        return r

    if jobs > 1:
        from .portfolio import solve_portfolio

        # preprocess_workers=0 because this formula is *already* preprocessed;
        # asking for preprocessing workers here would both redo the work and
        # force the process-based path, paying ~60 ms of startup for nothing
        pr = solve_portfolio(red, jobs=jobs, engine=engine, preprocess_workers=0)
        status = pr.sat
        model = pr.model
        conflicts = pr.stats.get("conflicts", 0)
    else:
        status, model, conflicts = _solve(red, cfg, None, engine, seconds)
    r.conflicts = conflicts + r.probe_conflicts
    r.sat = status
    if status:
        r.model = list(reconstruct(model))
    r.seconds = time.perf_counter() - t_start
    return r
