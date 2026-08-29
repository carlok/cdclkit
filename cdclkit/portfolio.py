# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""A parallel portfolio: run several differently-configured solvers, take the
first answer.

Why a portfolio rather than a parallel search
---------------------------------------------
Splitting a SAT search across cores is genuinely hard -- the search tree is
irregular, and dividing it well requires knowing which subtree is expensive,
which is the thing you are trying to find out. A *portfolio* sidesteps that: run
the same formula under different heuristic configurations, and stop when any of
them finishes. No coordination, no shared state, no load balancing.

What it can and cannot buy you, stated up front:

* **Satisfiable instances: real gains.** CDCL runtimes on satisfiable instances
  are heavy-tailed -- the same solver with a different seed can be an order of
  magnitude faster or slower, because it either wanders into the right region
  early or does not. Running k configurations takes the *minimum* of k draws
  from that distribution, and the minimum of a heavy-tailed sample is much
  better than its mean.
* **Unsatisfiable instances: close to nothing.** A refutation has to exhaust the
  search space no matter which heuristic walks it. Diversity changes the
  constant, not the requirement. Expect a speedup near 1.0, and be suspicious
  of any claim otherwise that does not come with a measurement.

This module deliberately does **no clause sharing**. That keeps each worker's
DRAT proof self-contained and independently verifiable: the winner's proof is a
refutation of the original formula, full stop. Sharing clauses between workers
would invalidate that -- an imported clause is not RUP in the importing worker's
proof stream -- and buying throughput with an unverifiable answer is a bad trade
for this project. See `PLAN.md` for how sharing would have to be handled if it
is ever added.

Threads versus processes
------------------------
CPython's GIL is enabled on this interpreter, so threads would serialise on the
solver's pure-Python inner loop and buy nothing. Processes it is, with the
`spawn` start method (the default on macOS). Spawn re-imports the module in each
worker, which is why the worker entry point is a module-level function and the
formula crosses as plain tuples rather than as a `CNF` object.

Asymmetric cores
----------------
On Apple Silicon the core count is not the parallelism you get: an M3 Pro has 5
performance and 6 efficiency cores, and the E-cores run this workload at a
fraction of P-core throughput. A worker that lands on an E-core takes much
longer, which does not hurt a first-to-finish portfolio (the P-core workers win
the race) but does mean **worker count is not speedup**. The default is the
performance-core count; `jobs` overrides it, and `bench/compare.py` measures both
rather than trusting either.
"""

from __future__ import annotations

import multiprocessing
import os
import queue as _queue
import subprocess
import sys
import time
import warnings
from typing import Sequence

from dratify.cnf import CNF
from .solver import Config, Solver

__all__ = [
    "solve_portfolio",
    "PortfolioResult",
    "default_configs",
    "performance_cores",
    "usable_start_method",
]


# --------------------------------------------------------------------------
# machine topology
# --------------------------------------------------------------------------


def performance_cores() -> int:
    """Number of performance cores, falling back to the logical CPU count.

    On Apple Silicon, `hw.perflevel0.physicalcpu` is the P-core count; on other
    platforms the sysctl is absent and we use `os.cpu_count()`.
    """
    try:
        out = subprocess.run(
            ["sysctl", "-n", "hw.perflevel0.physicalcpu"],
            capture_output=True, text=True, timeout=5,
        )
        n = int(out.stdout.strip())
        if n > 0:
            return n
    except Exception:
        pass
    return os.cpu_count() or 1


#: Marks a process as a portfolio worker.  Set in the environment the children
#: inherit, so it is visible even before their `__main__` is re-imported.
_WORKER_ENV = "CDCLKIT_PORTFOLIO_WORKER"


def in_worker() -> bool:
    """True when this process is already a portfolio worker.

    Guards against recursive process explosion.  `multiprocessing` with the
    `spawn` method re-imports the parent's `__main__` in every child, so a
    caller who forgets the `if __name__ == "__main__":` guard has their whole
    script re-executed per child -- and if that script calls
    `solve_portfolio`, each child starts its own portfolio, and so on. The
    standard library's answer is "always write the guard", which is correct and
    also not something a library should rely on: the failure mode is a fork
    bomb, not an error message.

    So children are marked, and a marked process runs sequentially.
    """
    return os.environ.get(_WORKER_ENV) == "1"


def usable_start_method() -> str | None:
    """Pick a start method that will actually work in this process.

    `spawn` (the macOS default) re-imports the parent's `__main__` in every
    child. From a script that is fine. From a REPL, a `python -c`, or a
    heredoc, `__main__` has no importable file and **every child dies on
    startup** -- and a `Pool` cheerfully respawns them, so the run hangs
    forever instead of failing. That is worth detecting rather than
    documenting.

    Returns the method to use, or None when no multiprocessing method is
    viable and the caller should run sequentially.
    """
    available = multiprocessing.get_all_start_methods()
    main = sys.modules.get("__main__")
    main_file = getattr(main, "__file__", None)
    main_importable = bool(main_file) and os.path.exists(main_file)

    if main_importable and "spawn" in available:
        return "spawn"
    # No importable __main__: spawn cannot work, but fork does not re-import
    # anything, so it still can.
    if "fork" in available:
        return "fork"
    if "forkserver" in available and main_importable:
        return "forkserver"
    return None


# --------------------------------------------------------------------------
# configuration diversity
# --------------------------------------------------------------------------


def default_configs(n: int) -> list[Config]:
    """`n` meaningfully different solver configurations.

    Diversity along the axes that actually change the search trajectory:
    restart policy (when to abandon a region), phase (which half of the space
    to try first), clause minimisation (how strong learnt clauses are), and
    randomisation (tie-breaking). Seeds differ throughout, so even two workers
    with the same policy explore differently.

    The order matters: index 0 is the plain default, so a 1-worker portfolio
    reproduces sequential behaviour exactly, and each added worker brings the
    next most different configuration rather than a near-duplicate.
    """
    recipes = [
        dict(),
        # Glucose EMA restarts with saved phases -- the default until the
        # measurement in CHECKPOINT_LOG moved it to Luby plus target phases.
        # It stays as a diversity axis rather than disappearing: it is still
        # the better configuration on some instances, and index 1 used to read
        # `restart="luby"`, which the flip silently turned into a duplicate of
        # index 0. A portfolio worker running the same search as another
        # worker is a wasted core.
        dict(restart="glucose", target_phase=False),
        # Local search with the gate lifted. Ungated walking is 34x on large
        # random satisfiable instances and a loss elsewhere, so it is wrong as
        # a default and right as one worker out of several: the cost is one
        # core, and the other workers are untouched.
        dict(walk_min_conflicts=0, walk_flips=50_000),
        dict(phase_saving=False, init_phase=True),
        dict(restart="luby", luby_base=1000, ccmin="basic"),
        dict(rnd_freq=0.02, var_decay=0.75),
        dict(restart="none", var_decay=0.9),
        dict(phase_saving=False, rnd_freq=0.05),
        dict(restart="luby", luby_base=32, glue_keep=3),
        dict(var_decay=0.95, first_reduce=8000),
        dict(ccmin="none", restart="luby", luby_base=256),
        dict(rnd_freq=0.1, init_phase=True, var_decay=0.7),
    ]
    out = []
    for i in range(n):
        kw = dict(recipes[i % len(recipes)])
        # a distinct seed per worker, so duplicated recipes still diverge
        kw["rnd_seed"] = 91648253 + 7919 * i
        out.append(Config(**kw))
    return out


# --------------------------------------------------------------------------
# worker
# --------------------------------------------------------------------------


def _worker_native(index, nvars, clauses, cfg_kwargs, want_proof):
    """Run one configuration on the native engine.  Returns None if unavailable.

    Each worker imports the native module independently -- under `spawn` the
    child is a fresh interpreter, so there is nothing to inherit. A worker that
    cannot import it falls back to Python rather than failing the whole
    portfolio, which keeps the dependency-free path working even here.
    """
    try:
        import cdclkit_native
    except ImportError:
        return None

    from dratify.lits import from_dimacs

    cfg = Config(**cfg_kwargs)
    t0 = time.perf_counter()
    s = cdclkit_native.Solver(
        nvars,
        restart=cfg.restart, ccmin=cfg.ccmin,
        phase_saving=cfg.phase_saving, init_phase=cfg.init_phase,
        target_phase=cfg.target_phase, target_reset=cfg.target_reset,
        walk_flips=cfg.walk_flips, walk_interval=cfg.walk_interval,
        walk_patience=cfg.walk_patience,
        walk_min_conflicts=cfg.walk_min_conflicts,
        var_decay=cfg.var_decay, var_decay_max=cfg.var_decay_max,
        cla_decay=cfg.cla_decay, luby_base=float(cfg.luby_base),
        first_reduce=cfg.first_reduce, reduce_inc=cfg.reduce_inc,
        glue_keep=cfg.glue_keep, block_restart=cfg.block_restart,
    )
    if want_proof:
        s.enable_proof()  # must precede the first clause
    ok = True
    for c in clauses:
        if not s.add_clause(c):
            ok = False
            break
    res = s.solve() if ok else False
    dt = time.perf_counter() - t0

    stats = {
        "conflicts": s.conflicts,
        "decisions": s.decisions,
        "propagations": s.propagations,
        "restarts": s.restarts,
        "seconds": dt,
        "engine": "native",
    }
    model = list(s.model) if res else None
    steps = None
    if want_proof and not res:
        # normalise to the same internal-literal form MemoryProof uses, so a
        # caller cannot tell which engine produced the proof
        steps = [(k, tuple(from_dimacs(d) for d in lits))
                 for k, lits in s.proof_steps()]
    return (index, bool(res), model, steps, stats)


def _worker(payload):
    """Run one configuration.  Must be module-level: `spawn` pickles by name."""
    (index, nvars, clauses, cfg_kwargs, want_proof, engine, preprocess) = payload

    if preprocess:
        # This worker preprocesses first.  Measurement says the two strategies
        # win on disjoint instance classes -- a portfolio wins on satisfiable
        # and heavy-tailed instances (rand3(250): 0.08 s against 0.99 s),
        # preprocessing wins on structured unsatisfiable ones (factor, php,
        # colouring).  Since workers race in parallel, preprocessing does not
        # have to be chosen *instead of* diversity: it can be one of the
        # diverse strategies, and whichever suits the instance wins.
        from dratify.cnf import CNF

        f = CNF(nvars)
        for c in clauses:
            f.add(c)
        f.nvars = nvars
        try:
            reduced, unsat, reconstruct, _ = _preprocess_for_worker(f, engine)
        except Exception:
            reduced, unsat, reconstruct = None, False, None
        if unsat:
            return (index, False, None, None,
                    {"conflicts": 0, "decisions": 0, "propagations": 0,
                     "restarts": 0, "seconds": 0.0,
                     "engine": engine, "preprocessed": True})
        if reduced is not None:
            inner = (index, nvars, [list(c) for c in reduced.clauses],
                     cfg_kwargs, False, engine, False)
            idx, sat, model, _steps, stats = _worker(inner)
            stats["preprocessed"] = True
            if sat and reconstruct is not None:
                model = list(reconstruct(model))
            # proofs are not returned from a preprocessing worker: the proof
            # would be of the *reduced* formula, and the preprocessing steps
            # that justify the reduction live in this process only
            return (idx, sat, model, None, stats)

    if engine == "native":
        got = _worker_native(index, nvars, clauses, cfg_kwargs, want_proof)
        if got is not None:
            return got
        # fall through to Python when the native module is missing

    from dratify.proof import MemoryProof  # local import keeps worker startup lean

    t0 = time.perf_counter()
    proof = MemoryProof() if want_proof else None
    s = Solver(nvars, proof=proof, config=Config(**cfg_kwargs))
    ok = True
    for c in clauses:
        if not s.add_clause(c):
            ok = False
            break
    res = s.solve() if ok else False
    dt = time.perf_counter() - t0

    stats = {
        "conflicts": s.stats.conflicts,
        "decisions": s.stats.decisions,
        "propagations": s.stats.propagations,
        "restarts": s.stats.restarts,
        "seconds": dt,
        "engine": "python",
    }
    model = list(s.model) if res else None
    steps = proof.steps if (proof is not None and not res) else None
    return (index, bool(res), model, steps, stats)


def _preprocess_for_worker(f, engine):
    """Preprocess inside a worker, preferring the native preprocessor."""
    from .pipeline import _preprocess

    return _preprocess(f, engine)


def _worker_proc(payload, out_queue):
    """Process entry point: run `_worker` and post the answer."""
    try:
        out_queue.put(_worker(payload))
    except BaseException as e:  # never leave the parent waiting on a silent death
        out_queue.put(("error", payload[0], f"{type(e).__name__}: {e}"))


# --------------------------------------------------------------------------
# result
# --------------------------------------------------------------------------


class PortfolioResult:
    """Outcome of a portfolio run."""

    __slots__ = ("sat", "model", "proof_steps", "winner", "winner_config",
                 "stats", "elapsed", "jobs", "finished", "engine")

    def __init__(self) -> None:
        self.sat: bool | None = None
        self.model: list[bool] | None = None
        self.proof_steps = None
        self.winner: int = -1
        self.winner_config: Config | None = None
        self.stats: dict = {}
        self.elapsed: float = 0.0
        self.jobs: int = 0
        self.finished: bool = False
        self.engine: str = "python"

    def __bool__(self) -> bool:
        return bool(self.sat)

    def report(self) -> str:
        if not self.finished:
            return f"c portfolio: no answer within the budget ({self.jobs} workers)"
        verdict = "SATISFIABLE" if self.sat else "UNSATISFIABLE"
        cfg = self.winner_config
        desc = (f"restart={cfg.restart} ccmin={cfg.ccmin} "
                f"phase_saving={cfg.phase_saving} seed={cfg.rnd_seed}"
                if cfg else "?")
        return (
            f"c portfolio: {self.jobs} workers on the {self.engine} engine, "
            f"{self.elapsed:.3f}s\n"
            f"c winner   : worker {self.winner} ({desc})\n"
            f"c           {self.stats.get('conflicts', 0)} conflicts, "
            f"{self.stats.get('propagations', 0)} propagations\n"
            f"c verdict  : {verdict}"
        )


# --------------------------------------------------------------------------
# native threaded path
# --------------------------------------------------------------------------


def _config_tuples(configs):
    """Flatten Configs into the shape the native binding accepts.

    Dicts rather than tuples. pyo3 stops extracting tuples past 12 elements,
    and a positional tuple mis-binds silently when a field is inserted in the
    middle -- `phase_saving` and `target_phase` are both booleans and adjacent,
    so a swap would run happily and just search differently.
    """
    return [
        dict(restart=c.restart, ccmin=c.ccmin, phase_saving=c.phase_saving,
             init_phase=c.init_phase, target_phase=c.target_phase,
             target_reset=c.target_reset, walk_flips=c.walk_flips,
             walk_interval=c.walk_interval, walk_patience=c.walk_patience,
             walk_min_conflicts=c.walk_min_conflicts,
             var_decay=c.var_decay, var_decay_max=c.var_decay_max,
             cla_decay=c.cla_decay, luby_base=float(c.luby_base),
             first_reduce=c.first_reduce, reduce_inc=c.reduce_inc,
             glue_keep=c.glue_keep, block_restart=c.block_restart)
        for c in configs
    ]


def _native_threaded(formula, cfgs, result, preprocess_workers=0,
                     want_proof=False):
    """Try the native threaded portfolio.  Returns True when it answered.

    Threads instead of processes removes ~60 ms of startup per solve, which on
    short instances was the entire runtime. The native side releases the GIL,
    so the threads genuinely run in parallel.

    Proofs work here too: each thread carries its own DRAT buffer and the
    winner's is returned. Because threads share no clauses, that buffer is
    already a complete standalone refutation -- there is nothing to merge. It is
    the payoff of the no-sharing decision, and it means the fastest
    configuration is also a certifying one.
    """
    try:
        import cdclkit_native
    except ImportError:
        return False
    if not hasattr(cdclkit_native, "solve_portfolio"):
        return False

    clauses = [list(c) for c in formula.clauses]

    # Some threads solve a preprocessed copy instead.  Preprocessing is worth
    # 1.3-1.5x on structured instances and a loss on easy ones, and the formula
    # does not say which it is -- so run it as one of the parallel strategies
    # rather than as a decision. When it helps, that thread wins; when it does
    # not, it cost nothing on the critical path.
    alt = None
    reconstruct = None
    if preprocess_workers > 0:
        from .pipeline import _preprocess

        try:
            red, unsat, reconstruct, _ = _preprocess(formula, "native")
            if unsat:
                result.sat = False
                result.model = None
                result.winner, result.winner_config = 0, cfgs[0]
                result.stats = {"conflicts": 0, "engine": "native-threads"}
                result.engine = "native-threads"
                result.finished = True
                return True
            alt = [list(c) for c in red.clauses]
        except Exception:
            alt, reconstruct = None, None

    out = cdclkit_native.solve_portfolio(
        formula.nvars, clauses, _config_tuples(cfgs),
        alt, preprocess_workers if alt is not None else 0, want_proof)
    if out is None:
        return False
    (winner, clause_set, sat, model, conflicts, decisions, propagations,
     restarts, proof) = out
    if sat and clause_set == 1 and reconstruct is not None:
        model = list(reconstruct(list(model)))
    from dratify.lits import from_dimacs

    result.sat = sat
    result.model = list(model) if sat else None
    result.proof_steps = (
        [("d" if is_del else "a", tuple(from_dimacs(d) for d in lits))
         for is_del, lits in proof]
        if proof else None
    )
    result.winner = winner
    result.winner_config = cfgs[winner]
    result.stats = {
        "conflicts": conflicts, "decisions": decisions,
        "propagations": propagations, "restarts": restarts,
        "engine": "native-threads",
    }
    result.engine = "native-threads"
    result.finished = True
    return True


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------


def solve_portfolio(
    formula: CNF,
    jobs: int | None = None,
    configs: Sequence[Config] | None = None,
    want_proof: bool = False,
    timeout: float | None = None,
    engine: str = "native",
    preprocess_workers: int | None = None,
) -> PortfolioResult:
    """Solve `formula` with `jobs` differently-configured workers in parallel.

    Returns as soon as any worker produces a definitive answer; the rest are
    terminated. Every worker solves the same formula, so whichever answers
    first is authoritative.

    `jobs=1` runs in-process with no multiprocessing at all, which keeps the
    single-worker path byte-for-byte identical to a plain `Solver` run --
    useful as a control, and it means the default configuration of any caller
    that does not ask for parallelism is unchanged.

    `engine` selects the per-worker solver. "native" uses the Rust engine when
    the module imports in the worker and falls back to Python otherwise, so the
    default is safe on a machine with no Rust toolchain. Pass "python" to force
    the reference engine -- worth doing when comparing against
    `bench/baseline.json`, since the two engines are bit-exact but only the
    Python one is what the baseline was recorded from.
    """
    if engine not in ("native", "python"):
        raise ValueError(f"unknown engine {engine!r} (expected native or python)")
    if preprocess_workers is None:
        # Roughly two fifths of the workers preprocess.  Measured on the
        # benchmark set at jobs=5 (total seconds over 17 instances):
        #   0 preprocessing workers  1.243
        #   1                        1.002
        #   2                        0.927
        #   3                        0.914
        # Past 2 the gain is marginal and it is bought with diversity, which
        # this benchmark set under-represents -- only 3 of its 17 instances are
        # satisfiable, and diversity is what wins those.
        preprocess_workers = max(1, jobs * 2 // 5) if jobs > 1 else 0
    if want_proof:
        # A preprocessing worker solves the *reduced* formula, so its proof
        # would refute that rather than the original, and the steps justifying
        # the reduction live in this process. Proof runs therefore use plain
        # configurations only, and every thread's buffer refutes the formula
        # the caller actually passed in.
        preprocess_workers = 0
    if jobs is None:
        jobs = performance_cores()
    jobs = max(1, int(jobs))
    cfgs = list(configs) if configs is not None else default_configs(jobs)
    jobs = min(jobs, len(cfgs))

    result = PortfolioResult()
    result.jobs = jobs
    clauses = [list(c) for c in formula.clauses]
    t0 = time.perf_counter()

    if in_worker():
        # Already inside a portfolio worker: never fan out again.
        jobs = 1
        cfgs = cfgs[:1]
        result.jobs = 1

    # Threads first: same design, a thousandth of the startup cost.  Skipped
    # for proof runs and for the preprocessing-worker strategy, both of which
    # need the per-process path.
    if jobs > 1 and engine == "native" and not in_worker():
        if _native_threaded(formula, cfgs, result, preprocess_workers, want_proof):
            result.elapsed = time.perf_counter() - t0
            return result

    if jobs == 1:
        idx, sat, model, steps, stats = _worker(
            (0, formula.nvars, clauses, cfgs[0].as_dict(), want_proof, engine,
             False))
        result.sat, result.model, result.proof_steps = sat, model, steps
        result.winner, result.winner_config, result.stats = idx, cfgs[0], stats
        result.engine = stats.get("engine", engine)
        result.elapsed = time.perf_counter() - t0
        result.finished = True
        return result

    method = usable_start_method()
    if method is None:
        warnings.warn(
            "no usable multiprocessing start method; running the portfolio "
            "sequentially with the first configuration",
            RuntimeWarning, stacklevel=2,
        )
        return solve_portfolio(formula, jobs=1, configs=cfgs[:1],
                               want_proof=want_proof, timeout=timeout,
                               engine=engine, preprocess_workers=0)

    ctx = multiprocessing.get_context(method)
    # The last `preprocess_workers` slots preprocess first; the rest race with
    # plain configuration diversity.
    payloads = [
        (i, formula.nvars, clauses, cfgs[i].as_dict(), want_proof, engine,
         i >= jobs - preprocess_workers)
        for i in range(jobs)
    ]

    # Explicit processes rather than a Pool: a Pool silently respawns workers
    # that die at startup, which turns a configuration error into an infinite
    # hang.  With plain processes, "everyone died" is observable.
    out: multiprocessing.Queue = ctx.Queue()
    procs = [ctx.Process(target=_worker_proc, args=(p, out), daemon=True)
             for p in payloads]
    # Mark the environment the children inherit, then restore ours.  This has
    # to happen around `start()` rather than inside the worker: under `spawn`
    # the child re-imports `__main__` *before* the worker function runs, and
    # that re-import is exactly what has to be stopped from fanning out again.
    previous = os.environ.get(_WORKER_ENV)
    os.environ[_WORKER_ENV] = "1"
    try:
        for p in procs:
            p.start()
    finally:
        if previous is None:
            os.environ.pop(_WORKER_ENV, None)
        else:
            os.environ[_WORKER_ENV] = previous

    deadline = (time.monotonic() + timeout) if timeout else None
    winner = None
    errors: list[str] = []
    try:
        while True:
            if deadline is not None and time.monotonic() > deadline:
                break
            try:
                item = out.get(timeout=0.05)
            except _queue.Empty:
                if not any(p.is_alive() for p in procs):
                    try:
                        item = out.get_nowait()
                    except _queue.Empty:
                        break
                else:
                    continue
            if item and item[0] == "error":
                errors.append(f"worker {item[1]}: {item[2]}")
                continue
            winner = item
            break
    finally:
        for p in procs:
            if p.is_alive():
                p.terminate()
        for p in procs:
            p.join(timeout=5)
        out.close()
        out.join_thread()

    result.elapsed = time.perf_counter() - t0
    if winner is None:
        if errors:
            raise RuntimeError(
                "every portfolio worker failed:\n  " + "\n  ".join(errors))
        if deadline is None:
            # Workers died without reporting -- almost always a start-method
            # problem the detector missed.  Degrade rather than return nothing.
            warnings.warn(
                "portfolio workers exited without an answer; falling back to "
                "a sequential solve", RuntimeWarning, stacklevel=2,
            )
            return solve_portfolio(formula, jobs=1, configs=cfgs[:1],
                                   want_proof=want_proof, timeout=timeout,
                                   engine=engine, preprocess_workers=0)
        return result  # genuine timeout

    idx, sat, model, steps, stats = winner
    result.sat, result.model, result.proof_steps = sat, model, steps
    result.winner, result.winner_config, result.stats = idx, cfgs[idx], stats
    result.engine = stats.get("engine", engine)
    result.finished = True
    return result
