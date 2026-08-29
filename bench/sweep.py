# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Sweep existing solver knobs over a corpus, split by satisfiability.

Written for one question: the gap against kissat was *entirely* on satisfiable
random 3-SAT -- uf250 at 3.25x behind while uuf250 was 0.84x ahead -- which
looks like a default chosen for the wrong half of the corpus rather than a
missing mechanism. (An earlier version of this docstring quoted 2.12 for uf250.
That came from a 14-instance corpus and was wrong; the corpus is 344 now.)

So this changes nothing in the solver. It asks what the knobs that already
exist are worth, before any new search code gets written. That question paid:
the answer was Luby restarts plus target phases, both already present.

Reporting rules, which are the point of having a script rather than a shell
loop:

* the **geometric mean of per-instance ratios against the baseline config**,
  never a wall-time sum -- a sum reports whichever instance was slowest;
* **uf and uuf separately**, because a knob that helps satisfiable instances
  and hurts unsatisfiable ones has bought nothing, and the aggregate hides it;
* the **worst instance** for each config, since the deficit being closed is a
  heavy tail rather than a uniform slowdown.

    python3 bench/sweep.py --limit 25
    python3 bench/sweep.py --limit 25 --configs default,luby,slow-decay
"""

from __future__ import annotations

import argparse
import math
import pathlib
import sys
import time
from collections import defaultdict

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))

from dratify.cnf import parse_dimacs_file
from cdclkit.pipeline import solve_adaptive
from cdclkit.solver import Config

from fetch_satlib import corpus_dir, group_of, holdout_families

CORPUS = corpus_dir()

#: name -> Config kwargs.  "default" must stay first and unmodified: every
#: other row is reported as a ratio against it.
CONFIGS: dict[str, dict] = {
    "default": {},
    # restart schedule -- the most likely single lever. Glucose EMA restarts
    # aggressively, which is right for refutation and can stop a satisfiable
    # search just as it is descending towards a solution.
    "luby": {"restart": "luby"},
    "luby-slow": {"restart": "luby", "luby_base": 512},
    # Restart interval. kissat's --sat is `--target=2 --restartint=50`; target
    # phases are already unconditional here, so the interval is the difference
    # left to explain the 1.28x it wins the satisfiable half by.
    "lb16": {"luby_base": 16},
    "lb32": {"luby_base": 32},
    "lb50": {"luby_base": 50},
    "lb64": {"luby_base": 64},
    "lb200": {"luby_base": 200},
    # Target reset. Ours never resets, so it is CaDiCaL's "best" rather than
    # its "target": after the search moves region, the assignment being
    # branched from is a memory of somewhere it can no longer reach.
    "reset8": {"target_reset": 8},
    "reset32": {"target_reset": 32},
    "lb50-reset8": {"luby_base": 50, "target_reset": 8},
    "lb32-reset8": {"luby_base": 32, "target_reset": 8},
    # probSAT rephasing. The walk can only ever help satisfiable instances --
    # on an unsatisfiable one it is pure overhead, so the uf/uuf split is the
    # whole measurement here, not a detail.
    "walk5k": {"walk_flips": 5_000},
    "walk20k": {"walk_flips": 20_000},
    "walk50k": {"walk_flips": 50_000},
    "walk20k-i1": {"walk_flips": 20_000, "walk_interval": 1},
    "walk20k-i16": {"walk_flips": 20_000, "walk_interval": 16},
    "no-restart": {"restart": "none"},
    "no-block": {"block_restart": False},
    # phase: the other half of the satisfiable story
    "target": {"target_phase": True},
    "target-luby": {"target_phase": True, "restart": "luby"},
    "phase-true": {"init_phase": True},
    "no-phase-saving": {"phase_saving": False},
    # activity decay: slower decay keeps the search in a region longer
    "slow-decay": {"var_decay": 0.75},
    "fast-decay": {"var_decay": 0.99},
    # clause database: keeping more clauses helps refutation, costs propagation
    "keep-more": {"first_reduce": 4000, "glue_keep": 5},
    "keep-less": {"first_reduce": 1000, "glue_keep": 2},
}


def load(families: list[str], limit: int) -> list[tuple[str, str, pathlib.Path]]:
    # Holdout families are refused, not warned about.
    #
    # This tool exists to choose configurations, and choosing a configuration
    # against a family means that family can no longer measure whether the
    # choice generalises. Making that a rule enforced by the tool rather than
    # by discipline is the whole point: the failure it guards against -- the
    # local-search walk, 37x faster on the corpus it was tuned on and 5.2x
    # slower on one it had never seen -- was caught by luck, once.
    refused = sorted(set(families) & holdout_families())
    if refused:
        raise SystemExit(
            f"bench/sweep.py refuses holdout families: {', '.join(refused)}.\n"
            f"They exist to measure whether a tuned configuration generalises, "
            f"which they cannot do once it has been tuned against them.\n"
            f"Report on them with bench/compare.py instead."
        )
    out = []
    for fam in families:
        d = CORPUS / fam
        if not d.is_dir():
            continue
        kind = "UNSAT" if fam.startswith("uuf") else "SAT"
        for f in sorted(d.glob("*.cnf"))[:limit]:
            out.append((fam, kind, f))
    return out


def run_one(path: pathlib.Path, cfg: Config, engine: str, budget: int | None):
    """Solve one instance, refusing to report a timing that spans a suspension.

    A laptop is one idle timeout away from a meaningless benchmark: if the host
    sleeps mid-instance the wall clock keeps running while the process is
    frozen, and the result looks exactly like a hard instance. That happened
    here -- a run was killed as "stuck" after an elapsed time that was mostly
    hibernation, and a conclusion was drawn from it the data did not support.

    `time.time()` advances across a suspension and `time.perf_counter()` does
    not, so their disagreement is the signal. Prevention (`caffeinate -i`) is
    better; this is the check that prevention worked.
    """
    f = parse_dimacs_file(str(path))
    t0, w0 = time.perf_counter(), time.time()
    r = solve_adaptive(f, engine=engine, config=cfg)
    secs = time.perf_counter() - t0
    slept = (time.time() - w0) - secs
    if slept > 2.0:
        raise RuntimeError(
            f"host suspended for ~{slept:.0f}s while solving {path.name}: that "
            f"timing is void and so is every ratio computed from it. Re-run "
            f"under `caffeinate -i` (macOS) or `systemd-inhibit` (Linux)."
        )
    return secs, r.sat, r.conflicts


def geo(xs: list[float]) -> float:
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float("nan")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--limit", type=int, default=25,
                    help="instances per family (default 25)")
    ap.add_argument("--families", default="uf250,uuf250",
                    help="tune-group families only; holdout families are refused")
    ap.add_argument("--configs", default="",
                    help="comma-separated subset of the table (default: all)")
    ap.add_argument("--engine", default="native", choices=["native", "python"])
    args = ap.parse_args()

    names = ([c.strip() for c in args.configs.split(",") if c.strip()]
             or list(CONFIGS))
    if "default" not in names:
        names.insert(0, "default")
    unknown = [n for n in names if n not in CONFIGS]
    if unknown:
        print(f"unknown config(s): {unknown}", file=sys.stderr)
        return 2

    work = load(args.families.split(","), args.limit)
    if not work:
        print(f"no instances under {CORPUS}; run bench/fetch_satlib.py first",
              file=sys.stderr)
        return 2
    print(f"c {len(work)} instances, {len(names)} configs, engine={args.engine}")

    # config -> instance -> seconds
    times: dict[str, dict[str, float]] = defaultdict(dict)
    conflicts: dict[str, dict[str, int]] = defaultdict(dict)
    for name in names:
        cfg = Config(**CONFIGS[name])
        t0 = time.perf_counter()
        for fam, kind, path in work:
            secs, sat, confl = run_one(path, cfg, args.engine, None)
            got = "SAT" if sat else "UNSAT"
            if got != kind:
                print(f"c !! {name} {path.name}: expected {kind}, got {got}")
                return 1
            times[name][path.name] = secs
            conflicts[name][path.name] = confl
        print(f"c   {name:<16} done in {time.perf_counter()-t0:6.1f}s")

    base = times["default"]
    print()
    print(f"{'config':<16} {'uf (SAT)':>10} {'uuf (UNSAT)':>12} {'all':>8} "
          f"{'worst':>8}  conflicts vs default")
    print("-" * 78)
    for name in names:
        per_fam: dict[str, list[float]] = defaultdict(list)
        allr, worst = [], (0.0, "")
        cratio = []
        for fam, kind, path in work:
            b = base.get(path.name, 0.0)
            if b <= 1e-6:
                continue
            r = times[name][path.name] / b
            per_fam["uf" if kind == "SAT" else "uuf"].append(r)
            allr.append(r)
            if r > worst[0]:
                worst = (r, path.name)
            cb = conflicts["default"].get(path.name, 0)
            if cb:
                cratio.append(conflicts[name][path.name] / cb)
        mark = "" if name != "default" else "   (baseline)"
        print(f"{name:<16} {geo(per_fam['uf']):10.3f} {geo(per_fam['uuf']):12.3f} "
              f"{geo(allr):8.3f} {worst[0]:8.2f}  {geo(cratio):.3f}{mark}")
    print("-" * 78)
    print("c <1.000 is faster than the default. uf and uuf are reported apart")
    print("c because a knob that trades one for the other has bought nothing.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
