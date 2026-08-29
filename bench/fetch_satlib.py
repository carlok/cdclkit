# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Fetch a curated subset of SATLIB into `bench/instances/satlib/`.

Run:  python3 bench/fetch_satlib.py [--force] [--list]

Why this exists
---------------
Every instance in `bench/run_bench.py` is one I generated. That is a real
weakness, not a formality: a single heavy-tailed instance of my own making
(`rand3(250)` seed 11) produced three separate phantom results before I noticed
— a 3x preprocessing "win", a 2.33x vivification "win", and an inflated
beats-CaDiCaL aggregate. Instances someone else designed cannot flatter my
design decisions the same way.

SATLIB is the standard public collection (Hoos and Stützle), hosted at UBC.

What is taken, and why it is bounded
------------------------------------
Unsatisfiable instances at the satisfiability threshold are where the runtime
goes, so the selection is deliberately uneven:

    uf100 / uuf100      50 each   fast, and enough of them to say something
    uf250 / uuf250      10 each   genuinely hard random 3-SAT
    flat200             20        graph colouring, structured
    logistics           all       planning, industrial-shaped and Tseitin-heavy
    BMS_k3_n100         20        backbone-minimal, an awkward family

Total download is ~6 MB.

Ground truth for free
---------------------
The family name encodes the answer: `uf*` is satisfiable, `uuf*` is
unsatisfiable, by construction of the benchmark set. That is a **third**
independent oracle, alongside the brute-force checker (which stops working past
~12 variables) and agreement between the five installed solvers. If cdclkit says
UNSAT on a `uf` instance, that is a bug no amount of solver agreement would
excuse. `expected_verdict()` exposes it and `bench/compare.py` checks it.

Safety
------
Archives are extracted with `filter="data"`, which rejects absolute paths,
parent-directory escapes, symlinks and device files. Extracting a downloaded
tarball without that is a path-traversal waiting to happen.
"""

from __future__ import annotations

import argparse
import io
import os
import pathlib
import sys
import tarfile
import urllib.request
from typing import NamedTuple

BASE = "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT"


def corpus_dir() -> pathlib.Path:
    """Where instances live.

    `CDCLKIT_BENCH_DIR` relocates the corpus -- to an external disk, or to
    somewhere a much larger benchmark set would fit. SATLIB is a few megabytes
    so this is not needed today; it exists so that adding a competition corpus
    later does not mean editing the harness.
    """
    env = os.environ.get("CDCLKIT_BENCH_DIR")
    if env:
        return pathlib.Path(env).expanduser()
    return pathlib.Path(__file__).with_name("instances") / "satlib"


DEST = corpus_dir()

class Family(NamedTuple):
    """One benchmark family.

    `group` is the important field. **tune** families may be used to choose
    configurations; **holdout** families may not, and `bench/sweep.py` refuses
    to load them so that the rule is enforced by the tool rather than by
    memory.

    The reason is that every performance number in this project was, until now,
    measured on uniform random 3-SAT at n=250 -- with a configuration tuned on
    that same corpus. That is training on the test set, and it is the first
    thing anyone familiar with the field would say. The holdout families are
    deliberately *structurally* different (planning, circuit fault analysis,
    parity learning, all-interval series) rather than a second sample of the
    same distribution, because the failure this is meant to catch is exactly
    the one the local-search walk exhibited: 37x faster on random satisfiable
    instances and 5.2x slower on a family it had never been measured against.
    """

    url: str
    keep: int
    verdict: str | None
    group: str = "tune"


#: family -> Family
#:
#: The n=250 families take all 100 instances the tarballs contain, and the
#: reason is a measurement failure rather than a wish for more data. At 10
#: each, only 14 instances in the whole corpus ran long enough for a timing
#: comparison to mean anything, and a *single* one of them -- uf250-0100 --
#: moved the standing against kissat from 1st (0.905) to 2nd (1.105). A
#: benchmark whose ranking hinges on one instance is measuring that instance.
#:
#: The n=100 families stay at 50: they solve in milliseconds, so they are
#: verdict-agreement evidence rather than timing evidence, and more of them
#: would only lengthen the run.
FAMILIES: dict[str, Family] = {
    # -- tune: configurations may be chosen against these ------------------
    "uf100": Family("RND3SAT/uf100-430.tar.gz", 50, "SAT"),
    "uuf100": Family("RND3SAT/uuf100-430.tar.gz", 50, "UNSAT"),
    "uf250": Family("RND3SAT/uf250-1065.tar.gz", 100, "SAT"),
    "uuf250": Family("RND3SAT/uuf250-1065.tar.gz", 100, "UNSAT"),
    "flat200": Family("GCP/flat200-479.tar.gz", 20, "SAT"),
    "logistics": Family("PLANNING/logistics.tar.gz", 10, "SAT"),
    "bms100": Family("BMS/BMS_k3_n100_m429.tar.gz", 20, "SAT"),

    # -- holdout: never tuned on, only reported on -------------------------
    #
    # Verdicts here were *measured*, not recalled: the first holdout run had
    # them all as None, and a family is given a verdict only where every
    # instance in it was solved and every solver agreed. Mixed families keep
    # None, which costs only the ground-truth check -- cross-solver agreement
    # still applies, and asserting a verdict I had not verified would be worse
    # than asserting none.
    #
    # `dubois` is the cautionary one and stays None. It is constructed to be
    # unsatisfiable, yet dubois100 came back satisfiable -- because that file
    # declares 800 clauses and parses to 396 (see CNF.header_mismatch). The
    # benchmark now drops malformed instances instead of comparing solvers on a
    # formula none of them was asked about.
    "blocksworld": Family("PLANNING/blocksworld.tar.gz", 7, "SAT", "holdout"),
    "ais": Family("AIS/ais.tar.gz", 4, "SAT", "holdout"),
    "hanoi": Family("DIMACS/HANOI/hanoi.tar.gz", 5, "SAT", "holdout"),
    "aim": Family("DIMACS/AIM/aim.tar.gz", 40, None, "holdout"),      # mixed
    "jnh": Family("DIMACS/JNH/jnh.tar.gz", 30, None, "holdout"),      # mixed
    "ssa": Family("DIMACS/SSA/ssa.tar.gz", 8, None, "holdout"),       # mixed
    "bf": Family("DIMACS/BF/bf.tar.gz", 4, "UNSAT", "holdout"),
    # 10, not 20: sorted order takes the par16 instances, which both solvers
    # finish, and leaves the par32 ones, which neither does. Ten instances that
    # both solvers time out on cost 20 minutes of every repeated run and
    # contribute a ratio of exactly 1.0 -- they measure the timeout, not the
    # solvers. Parity stays in the corpus because it is a known CDCL weakness
    # worth keeping honest about; it just does not need the intractable half.
    "parity": Family("DIMACS/PARITY/parity.tar.gz", 10, "SAT", "holdout"),
    "dubois": Family("DIMACS/DUBOIS/dubois.tar.gz", 13, None, "holdout"),
    "pret": Family("DIMACS/PRET/pret.tar.gz", 8, "UNSAT", "holdout"),
    "sw100": Family("SW-GCP/sw100-8-lp0-c5.tar.gz", 20, "SAT", "holdout"),
}


def group_of(name: str) -> str:
    """"tune" or "holdout" for a family directory name."""
    f = FAMILIES.get(name)
    return f.group if f else "tune"


def holdout_families() -> set[str]:
    return {k for k, v in FAMILIES.items() if v.group == "holdout"}


def expected_verdict(path: str | os.PathLike) -> str | None:
    """"SAT" / "UNSAT" / None, from the SATLIB family the file belongs to.

    Ground truth that costs nothing: the benchmark set is *constructed* so that
    `uf*` instances are satisfiable and `uuf*` are not.
    """
    name = pathlib.Path(path).parent.name
    fam = FAMILIES.get(name)
    if fam is not None:
        return fam.verdict
    # fall back to the filename convention for loose files
    base = pathlib.Path(path).name
    if base.startswith("uuf"):
        return "UNSAT"
    if base.startswith("uf"):
        return "SAT"
    return None


def fetch_one(family: str, url_path: str, keep: int, force: bool) -> int:
    out_dir = DEST / family
    if out_dir.exists() and not force:
        have = len(list(out_dir.glob("*.cnf")))
        # `have >= keep`, not `have > 0`. Treating any cached file as a
        # complete cache means raising a family's count in FAMILIES silently
        # does nothing, and you go on benchmarking the old corpus while
        # believing you enlarged it.
        if have >= keep:
            print(f"  {family:<12} cached ({have} instances)")
            return have
        if have:
            print(f"  {family:<12} have {have}, want {keep} -- topping up")

    url = f"{BASE}/{url_path}"
    print(f"  {family:<12} downloading {url_path} ...", end="", flush=True)
    try:
        with urllib.request.urlopen(url, timeout=120) as resp:
            blob = resp.read()
    except Exception as e:
        print(f" FAILED ({type(e).__name__}: {e})")
        return 0
    print(f" {len(blob)/1048576:.1f} MB", end="", flush=True)

    out_dir.mkdir(parents=True, exist_ok=True)
    written = 0
    with tarfile.open(fileobj=io.BytesIO(blob), mode="r:gz") as tar:
        members = sorted(
            (m for m in tar.getmembers() if m.isfile() and m.name.endswith(".cnf")),
            key=lambda m: m.name,
        )
        for m in members[:keep]:
            # filter="data" rejects absolute paths, ".." escapes, symlinks and
            # device nodes -- extracting a downloaded archive without it is a
            # path traversal waiting to happen
            src = tar.extractfile(m)
            if src is None:
                continue
            (out_dir / pathlib.Path(m.name).name).write_bytes(src.read())
            written += 1
    print(f" -> {written} instances")
    return written


def instances() -> list[pathlib.Path]:
    """Every cached instance, sorted, for a stable benchmark order."""
    if not DEST.exists():
        return []
    return sorted(DEST.glob("*/*.cnf"))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--force", action="store_true", help="re-download even if cached")
    ap.add_argument("--list", action="store_true", help="list what is cached and exit")
    args = ap.parse_args()

    if args.list:
        found = instances()
        if not found:
            print("c nothing cached; run without --list to fetch")
            return 1
        by_family: dict[str, int] = {}
        for p in found:
            by_family[p.parent.name] = by_family.get(p.parent.name, 0) + 1
        for fam, n in sorted(by_family.items()):
            f = FAMILIES.get(fam)
            v = f.verdict if f else None
            print(f"  {fam:<14} {n:>4} instances  {group_of(fam):<8} "
                  f"expected {v or '-'}")
        print(f"  {'TOTAL':<12} {len(found):>4}")
        return 0

    print(f"c fetching SATLIB subset into {DEST}")
    total = 0
    for family, f in FAMILIES.items():
        total += fetch_one(family, f.url, f.keep, args.force)
    print(f"c {total} instances available")
    if total == 0:
        print("c nothing fetched -- is the network reachable?")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
