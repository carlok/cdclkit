# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Compare cdclkit against external SAT solvers on this machine.

Run:  python3 bench/compare.py [--quick] [--timeout 60] [--solvers cadical,minisat]

Two jobs, and the second one matters more than the first.

**Performance.** A speed claim is only meaningful against a reference measured
on the same hardware, in the same session, on the same instances. Numbers
copied from a paper were produced on someone else's machine with someone else's
compiler; they cannot tell you what your port bought you. This harness runs
cdclkit and every external solver it can find back to back and reports the ratio.

**Correctness at scale.** `cdclkit/brute.py` is exhaustive, so it caps out around
12 variables. A mature external solver is an oracle that keeps working at 200
variables and beyond, which is exactly the range where a subtle watched-literal
or backjumping bug hides. Any verdict disagreement is a bug in somebody's
solver, and the harness exits non-zero when it sees one.

There is a third thing it does, almost for free: when an external solver can
emit a DRAT proof, cdclkit's checker verifies *that* proof. A checker that
accepts CaDiCaL's refutations is a checker being tested against an
implementation that shares none of its assumptions.

Installing a reference solver (any one of these is enough)::

    brew install cadical      # or: minisat, kissat, cryptominisat, z3

The harness discovers whatever is on PATH and skips the rest, so it is useful
with one solver installed and more useful with four.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from dratify.cnf import CNF, parse_dimacs, parse_dimacs_file
from dratify.proof import check_proof, parse_proof
from cdclkit.solver import Solver

from run_bench import families  # the same instance families the solo bench uses
from fetch_satlib import group_of

SAT, UNSAT, UNKNOWN, ERROR = "SAT", "UNSAT", "UNKNOWN", "ERROR"


# --------------------------------------------------------------------------
# external solver adapters
# --------------------------------------------------------------------------


class External:
    """How to invoke one external solver and read its answer.

    Most modern solvers follow the SAT competition contract -- exit 10 for
    satisfiable, 20 for unsatisfiable, `s`/`v` lines on stdout -- which is why
    a single adapter covers CaDiCaL, kissat, CryptoMiniSat and PicoSAT.
    MiniSat and Glucose write the model to a second file instead, so they get
    their own reader.
    """

    def __init__(self, name: str, argv_fn, reader: str = "competition",
                 proof_fn=None) -> None:
        self.name = name
        self.argv_fn = argv_fn
        self.reader = reader
        self.proof_fn = proof_fn

    @property
    def path(self) -> str | None:
        return shutil.which(self.name)

    def available(self) -> bool:
        return self.path is not None

    def version(self) -> str:
        for flag in ("--version", "-version", "--help"):
            try:
                out = subprocess.run([self.name, flag], capture_output=True,
                                     text=True, timeout=10)
                line = (out.stdout or out.stderr).strip().splitlines()
                if line:
                    return line[0][:60]
            except Exception:
                continue
        return "unknown"

    # -- running --------------------------------------------------------

    def run(self, cnf_path: str, timeout: float, proof_path: str | None = None):
        """Returns (verdict, seconds, model_or_None)."""
        with tempfile.TemporaryDirectory() as tmp:
            out_path = os.path.join(tmp, "model.out")
            argv = self.argv_fn(cnf_path, out_path, proof_path)
            t0 = time.perf_counter()
            try:
                proc = subprocess.run(argv, capture_output=True, text=True,
                                      timeout=timeout)
            except subprocess.TimeoutExpired:
                return UNKNOWN, timeout, None
            except FileNotFoundError:
                return ERROR, 0.0, None
            dt = time.perf_counter() - t0

            if self.reader == "outfile":
                return self._read_outfile(proc, out_path, dt)
            return self._read_competition(proc, dt)

    @staticmethod
    def _read_competition(proc, dt):
        verdict = UNKNOWN
        if proc.returncode == 10:
            verdict = SAT
        elif proc.returncode == 20:
            verdict = UNSAT
        else:
            for line in proc.stdout.splitlines():
                if line.startswith("s "):
                    if "UNSAT" in line:
                        verdict = UNSAT
                    elif "SAT" in line:
                        verdict = SAT
        model = None
        if verdict == SAT:
            lits = []
            for line in proc.stdout.splitlines():
                if line.startswith("v "):
                    lits.extend(int(x) for x in line[2:].split())
            model = _lits_to_model(lits) if lits else None
        return verdict, dt, model

    @staticmethod
    def _read_outfile(proc, out_path, dt):
        if not os.path.exists(out_path):
            return External._read_competition(proc, dt)
        with open(out_path, "r", errors="replace") as fh:
            text = fh.read()
        head = text.split(None, 1)[0].upper() if text.strip() else ""
        if head.startswith("UNSAT"):
            return UNSAT, dt, None
        if head.startswith("SAT"):
            rest = text.split(None, 1)[1] if len(text.split(None, 1)) > 1 else ""
            lits = [int(x) for x in rest.split() if x.lstrip("-").isdigit()]
            return SAT, dt, _lits_to_model(lits)
        if head.startswith("INDET"):
            return UNKNOWN, dt, None
        return External._read_competition(proc, dt)


def _lits_to_model(lits) -> list[bool]:
    n = max((abs(l) for l in lits if l != 0), default=0)
    model = [False] * n
    for l in lits:
        if l:
            model[abs(l) - 1] = l > 0
    return model


ADAPTERS = [
    # CaDiCaL and kissat write *binary* DRAT to a file by default; cdclkit's
    # checker reads the text dialect, so ask for text explicitly.  This is the
    # same incompatibility PLAN.md flags for the native port: a binary proof
    # nothing in the repo can read is a proof that does not get checked.
    External("cadical",
             lambda cnf, out, proof: (["cadical", "-q", "--no-binary", cnf]
                                      + ([proof] if proof else [])),
             "competition",
             proof_fn=lambda p: p),
    External("kissat",
             lambda cnf, out, proof: (["kissat", "-q", "--no-binary", cnf]
                                      + ([proof] if proof else [])),
             "competition",
             proof_fn=lambda p: p),
    External("minisat",
             lambda cnf, out, proof: ["minisat", "-verb=0", cnf, out],
             "outfile"),
    External("glucose",
             lambda cnf, out, proof: ["glucose", "-verb=0", cnf, out],
             "outfile"),
    External("cryptominisat5",
             lambda cnf, out, proof: ["cryptominisat5", "--verb=0", cnf],
             "competition"),
    External("picosat",
             lambda cnf, out, proof: ["picosat", cnf],
             "competition"),
    External("z3",
             lambda cnf, out, proof: ["z3", "-dimacs", cnf],
             "competition"),
]


def discover() -> list[External]:
    return [a for a in ADAPTERS if a.available()]



# --------------------------------------------------------------------------
# suspension detection
# --------------------------------------------------------------------------


class SuspensionDetector:
    """Notices when the machine slept in the middle of a measurement.

    A benchmark on a laptop is one idle timeout away from garbage. If the host
    suspends mid-instance, the wall clock keeps advancing while the process is
    frozen, and the run reports a solve time that is mostly sleep. Nothing in
    the numbers looks wrong afterwards -- it just looks like that instance was
    hard.

    This happened here: a sweep was killed as "stuck" after an elapsed time
    that turned out to be mostly hibernation, and a conclusion about the
    default configuration was drawn from it that the data did not support.

    Detection is a clock comparison. `time.time()` advances across a
    suspension; `time.perf_counter()` is monotonic and on most platforms does
    not. When they disagree by more than a threshold, the interval contained
    time the process was not running, and any timing from it is void.

    Prevention is better and cheaper -- run under `caffeinate -i` on macOS or
    `systemd-inhibit` on Linux -- but prevention that is not checked is a
    wish. This is the check.
    """

    #: seconds of divergence before an interval is considered suspended
    TOLERANCE = 2.0

    def __init__(self) -> None:
        self.reset()
        self.events: list[tuple[str, float]] = []

    def reset(self) -> None:
        self._mono = time.perf_counter()
        self._wall = time.time()

    def check(self, label: str) -> float:
        """Seconds lost to suspension since the last reset (0.0 if none)."""
        mono = time.perf_counter() - self._mono
        wall = time.time() - self._wall
        self.reset()
        gap = wall - mono
        if gap > self.TOLERANCE:
            self.events.append((label, gap))
            print(f"c !! host suspended for ~{gap:.0f}s during {label}: "
                  f"that timing is void")
            return gap
        return 0.0

    def report(self) -> None:
        if not self.events:
            return
        total = sum(g for _, g in self.events)
        print(f"c !! WARNING: the host slept {len(self.events)} time(s) during "
              f"this run, {total:.0f}s total.")
        print("c !! Timings from the affected instances are meaningless. "
              "Re-run under `caffeinate -i` (macOS) or `systemd-inhibit` "
              "(Linux) before quoting any number from it.")
        for lab, g in self.events:
            print(f"c !!   {lab}: ~{g:.0f}s")


# --------------------------------------------------------------------------
# our side
# --------------------------------------------------------------------------


def run_cdclkit(f: CNF, timeout: float, want_proof: bool = False,
              engine: str = "python", jobs: int | None = None,
              config: "Config | None" = None):
    """Returns (verdict, seconds, model_or_None, conflicts).

    `config` lets a candidate configuration be measured against the external
    solvers *without* changing the shipped default. Flipping a default to find
    out whether it is better is how a benchmark ends up validating the change
    it was supposed to test.
    """
    from dratify.proof import MemoryProof

    if engine == "adaptive":
        from cdclkit.pipeline import solve_adaptive

        # The same wall clock the external solvers get. Without it the harness
        # bounded the competitors and not itself: a SATLIB par32 instance --
        # exponential for CDCL without XOR reasoning, and one kissat also fails
        # to solve -- ran here for 77 minutes while kissat was killed at 120s.
        r = solve_adaptive(f, engine="native" if _has_native() else "python",
                           config=config, seconds=timeout)
        # `r.sat` is bool | None, and None means the budget ran out. Writing
        # `SAT if r.sat else UNSAT` would record giving up as a refutation --
        # the same falsy-None mistake that once let cdclkit.pyeq report an
        # exhausted budget as a proof.
        if r.sat is None:
            return UNKNOWN, r.seconds, None, r.conflicts
        return (SAT if r.sat else UNSAT), r.seconds, r.model, r.conflicts

    if engine == "native":
        from cdclkit import native as _nat

        n = _nat.require()
        s = n.Solver(f.nvars)
        ok = True
        for c in f.clauses:
            if not s.add_clause(list(c)):
                ok = False
                break
        t0 = time.perf_counter()
        res = s.solve() if ok else False
        dt = time.perf_counter() - t0
        return (SAT if res else UNSAT), dt, (list(s.model) if res else None), s.conflicts

    if engine == "portfolio":
        from cdclkit.portfolio import solve_portfolio

        r = solve_portfolio(f, jobs=jobs, want_proof=want_proof, timeout=timeout,
                            engine="native" if _has_native() else "python")
        if not r.finished:
            return UNKNOWN, timeout, None, 0
        return (SAT if r.sat else UNSAT), r.elapsed, r.model, r.stats.get("conflicts", 0)

    proof = MemoryProof() if want_proof else None
    s = Solver(f.nvars, proof=proof)
    ok = s.add_cnf(f)
    t0 = time.perf_counter()
    res = s.solve() if ok else False
    dt = time.perf_counter() - t0
    if res:
        return SAT, dt, list(s.model), s.stats.conflicts
    return UNSAT, dt, None, s.stats.conflicts


# --------------------------------------------------------------------------
# per-sprint history
# --------------------------------------------------------------------------

HISTORY = pathlib.Path(__file__).with_name("history.jsonl")


def _has_native() -> bool:
    from cdclkit import native

    return native.available()


def git_commit() -> str:
    try:
        out = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                             capture_output=True, text=True, timeout=5,
                             cwd=pathlib.Path(__file__).parent.parent)
        return out.stdout.strip() or "unknown"
    except Exception:
        return "unknown"


def record_run(label: str, engine: str, jobs, rows, totals, geo=None) -> None:
    """Append one checkpoint to bench/history.jsonl.

    One line per sprint, so progress across the port is visible as a table
    rather than as a memory of what last week's numbers were.
    """
    entry = {
        "label": label,
        "engine": engine,
        "jobs": jobs,
        "commit": git_commit(),
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "totals": {k: round(v, 4) for k, v in totals.items()},
        "geomean_vs_cadical": (round(geo.get("cadical"), 4)
                               if geo and geo.get("cadical") else None),
        "geomeans": {k: round(v, 4) for k, v in (geo or {}).items()},
        "instances": {
            f"{lab}/{who}": {"verdict": v, "seconds": round(t, 4), "conflicts": c}
            for (lab, who, v, t, _ratio, c) in rows
        },
    }
    with HISTORY.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(entry, sort_keys=True) + "\n")
    print(f"c recorded checkpoint {label!r} to {HISTORY.name}")


def print_history() -> int:
    if not HISTORY.exists():
        print("c no checkpoints recorded yet (use --record LABEL)")
        return 1
    entries = [json.loads(l) for l in HISTORY.read_text().splitlines() if l.strip()]
    competitors = sorted({k for e in entries for k in e.get("geomeans", {})})
    header = (f"{'label':<17}{'engine':<11}{'cdclkit s':>9}"
              + "".join(f"{c[:9]:>10}" for c in competitors))
    print(header)
    print("-" * len(header))
    for e in entries:
        # Checkpoints recorded before the project was renamed store our times
        # under "sable". Reading only the new key made every historical row
        # print 0.00 -- a `.get(..., 0.0)` default silently turning "recorded
        # under the old name" into "took no time at all".
        totals = e["totals"]
        ours = totals.get("cdclkit", totals.get("sable"))
        if ours is None:
            ours = float("nan")
        cells = ""
        for c in competitors:
            g = e.get("geomeans", {}).get(c)
            cells += f"{(f'{g:.2f}x' if g else '-'):>10}"
        shown = "-" if ours != ours else f"{ours:.2f}"
        print(f"{e['label']:<17}{e['engine']:<11}{shown:>9}{cells}")
    print()
    print("c geometric mean of per-instance ratios; >1 means the competitor is")
    print("c faster.  Instances the competitor finishes in <50 ms are excluded:")
    print("c below that the measurement is process startup, not solving.")
    return 0


# --------------------------------------------------------------------------
# comparison
# --------------------------------------------------------------------------


def compare_instance(label, f: CNF, externals, timeout, tmpdir, check_proofs,
                     engine="python", jobs=None, config=None, repeat=1):
    """Run everyone on one instance.  Returns (rows, disagreements, notes).

    `repeat > 1` times each solver several times and keeps the **median**.

    This is not belt-and-braces. kissat's own speed varied 35% between two runs
    of the same binary on this machine, and every ratio in this project has
    been a single sample -- so no reported difference has ever had an error bar,
    and small ones were unreadable.

    Repeats are **interleaved**: every solver runs once on this instance before
    any of them runs a second time. Looping the whole corpus instead would let
    the machine warm up between the two solvers being compared, which puts the
    drift entirely on one side of the ratio.

    The median, not the mean: one thermal outlier should move nothing.
    """
    cnf_path = os.path.join(tmpdir, f"{abs(hash(label))}.cnf")
    f.save(cnf_path)

    rows, notes = [], []
    samples: dict[str, list[float]] = {}

    our_times, verdict, model, conflicts = [], None, None, None
    for _ in range(repeat):
        verdict, dt, model, conflicts = run_cdclkit(f, timeout, engine=engine,
                                                  jobs=jobs, config=config)
        our_times.append(dt)
        if verdict == SAT and not f.is_satisfied_by(model):
            notes.append(f"{label}: cdclkit returned an invalid model")
    samples["cdclkit"] = our_times
    dt = statistics.median(our_times)
    rows.append((label, "cdclkit", verdict, dt, 1.0, conflicts))
    base_time = dt

    disagreements = []
    for ex in externals:
        proof_path = None
        if check_proofs and ex.proof_fn is not None:
            proof_path = os.path.join(tmpdir, f"{ex.name}_{abs(hash(label))}.drat")
        ex_times = []
        for _ in range(repeat):
            v, t, m = ex.run(cnf_path, timeout, proof_path)
            ex_times.append(t)
        samples[ex.name] = ex_times
        t = statistics.median(ex_times)
        ratio = (t / base_time) if base_time > 0 else float("nan")
        rows.append((label, ex.name, v, t, ratio, None))

        if v in (SAT, UNSAT) and verdict in (SAT, UNSAT) and v != verdict:
            disagreements.append(f"{label}: cdclkit says {verdict}, {ex.name} says {v}")
        if v == SAT and m is not None:
            padded = m + [False] * max(0, f.nvars - len(m))
            if not f.is_satisfied_by(padded):
                notes.append(f"{label}: {ex.name} returned a model that does not satisfy the formula")
        if v == UNSAT and proof_path and os.path.exists(proof_path):
            try:
                with open(proof_path, "r", errors="replace") as fh:
                    steps = parse_proof(fh.read())
                res = check_proof(f, steps)
                notes.append(
                    f"{label}: {ex.name}'s {len(steps)}-step proof "
                    f"{'VERIFIED' if res.ok else 'REJECTED (' + res.reason + ')'} "
                    "by cdclkit's checker"
                )
            except Exception as e:  # binary DRAT, or a dialect we cannot read
                notes.append(f"{label}: could not read {ex.name}'s proof ({type(e).__name__})")
    return rows, disagreements, notes, samples


def load_directory(path: str, limit: int = 0):
    """Load `.cnf` files from a directory tree, with SATLIB ground truth.

    Returns `(instances, expected)` where `expected` maps a label to "SAT" or
    "UNSAT" when the benchmark family declares it. SATLIB encodes the answer in
    the family name -- `uf*` is satisfiable by construction, `uuf*` is not --
    which is a third oracle alongside brute force (useless past ~12 variables)
    and agreement between the installed solvers. A verdict that contradicts it
    is a bug no amount of solver agreement would excuse.
    """
    root = pathlib.Path(path)
    files = sorted(root.rglob("*.cnf"))
    if limit:
        files = files[:limit]
    try:
        sys.path.insert(0, str(pathlib.Path(__file__).parent))
        from fetch_satlib import expected_verdict
    except ImportError:
        def expected_verdict(_p):
            return None

    out, expected = [], {}
    for f in files:
        label = f"{f.parent.name}/{f.stem}"
        out.append((label, parse_dimacs_file(str(f))))
        v = expected_verdict(f)
        if v:
            expected[label] = v
    return out, expected


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--solvers", default="", help="comma-separated subset to use")
    ap.add_argument("--check-proofs", action="store_true",
                    help="ask solvers for DRAT proofs and verify them with cdclkit")
    ap.add_argument("--engine", default="python",
                    choices=["python", "portfolio", "native", "adaptive"],
                    help="which cdclkit engine to measure")
    ap.add_argument("--jobs", type=int, default=None,
                    help="workers for --engine portfolio (default: performance cores)")
    ap.add_argument("--record", metavar="LABEL",
                    help="append this run to bench/history.jsonl under LABEL")
    ap.add_argument("--history", action="store_true",
                    help="print all recorded checkpoints and exit")
    ap.add_argument("--instances", metavar="DIR",
                    help="benchmark a directory of .cnf files (e.g. the SATLIB "
                         "corpus from bench/fetch_satlib.py) instead of the "
                         "generated families")
    ap.add_argument("--repeat", type=int, default=1, metavar="N",
                    help="run each solver N times per instance and keep the "
                         "median. A performance claim needs at least 3: the "
                         "competitor's own speed varied 35%% between two runs "
                         "of the same binary here, and a single sample cannot "
                         "show that.")
    ap.add_argument("--group", default="all", choices=["all", "tune", "holdout"],
                    help="restrict to tune families (may be used for choosing "
                         "configurations) or holdout families (may not, and so "
                         "are the only ones that can say whether a tuned "
                         "configuration generalises)")
    ap.add_argument("--config", default="",
                    help="candidate Config overrides as k=v pairs, e.g. "
                         "'target_phase=1,restart=luby'. Measures a candidate "
                         "against the external solvers without changing the "
                         "shipped default -- flipping a default to find out "
                         "whether it is better is how a benchmark ends up "
                         "validating the change it was meant to test.")
    ap.add_argument("--limit", type=int, default=0,
                    help="with --instances, use at most this many files")
    args = ap.parse_args()

    if args.history:
        return print_history()

    externals = discover()
    if args.solvers:
        wanted = set(args.solvers.split(","))
        externals = [e for e in externals if e.name in wanted]

    print("c reference solvers on this machine:")
    if not externals:
        print("c   none found on PATH.")
        print("c")
        print("c   Install one and re-run -- any of these is enough:")
        print("c     brew install cadical      # emits DRAT, so --check-proofs works")
        print("c     brew install minisat      # small and classic")
        print("c     brew install kissat cryptominisat z3")
        print("c")
        print("c   Without a reference, a speed number is unanchored and a verdict")
        print("c   is unchecked above the ~12 variables brute force can reach.")
        return 2
    for e in externals:
        print(f"c   {e.name:<16} {e.path}")
        print(f"c   {'':<16} {e.version()}")

    if args.instances:
        insts, expected = load_directory(args.instances, args.limit)
        if not insts:
            print(f"c no .cnf files under {args.instances}")
            print("c   run: python3 bench/fetch_satlib.py")
            return 1
        # Strict parsing, and malformed instances are dropped with a reason
        # rather than silently benchmarked. `dubois100.cnf` declares 800
        # clauses and yields 396; kissat rejects it outright, and feeding every
        # solver our re-serialised 396-clause version made them agree on a
        # verdict for a formula none of them was asked about.
        kept, dropped = [], []
        for lab, f in insts:
            if getattr(f, "header_mismatch", None):
                dropped.append((lab, f.header_mismatch))
            else:
                kept.append((lab, f))
        if dropped:
            print(f"c {len(dropped)} instance(s) dropped as malformed "
                  f"(header disagrees with contents):")
            for lab, (want, got) in dropped:
                print(f"c   {lab}: header {want} clauses, parsed {got}")
        insts = kept

        if args.group != "all":
            insts = [(lab, f) for lab, f in insts
                     if group_of(lab.split("/")[0]) == args.group]
        print(f"c {len(insts)} instances from {args.instances}"
              + (f" ({args.group} group)" if args.group != "all" else ""))
    else:
        insts, expected = families(args.quick), {}

    cand_config = None
    if args.config:
        from cdclkit.solver import Config

        kw: dict = {}
        for pair in args.config.split(","):
            k, _, v = pair.partition("=")
            k, v = k.strip(), v.strip()
            if k not in Config.__slots__:
                print(f"c unknown config option {k!r}", file=sys.stderr)
                return 1
            cur = getattr(Config(), k)
            kw[k] = (v if isinstance(cur, str)
                     else type(cur)(float(v) if isinstance(cur, float) else int(v)))
        cand_config = Config(**kw)
        print(f"c candidate config: {kw}")
    print()
    header = (f"{'instance':<16}{'solver':<16}{'verdict':>9}{'time':>10}"
              f"{'vs cdclkit':>10}{'conflicts':>11}")
    print(header)
    print("-" * len(header))

    all_disagreements, all_notes, all_rows = [], [], []
    all_samples: dict[str, list[float]] = {}
    totals: dict[str, float] = {}
    suspend = SuspensionDetector()
    with tempfile.TemporaryDirectory(prefix="cdclkit-compare-") as tmp:
        for label, f in insts:
            suspend.reset()
            rows, dis, notes, samp = compare_instance(
                label, f, externals, args.timeout, tmp, args.check_proofs,
                engine=args.engine, jobs=args.jobs, config=cand_config,
                repeat=args.repeat)
            for who, ts in samp.items():
                if min(ts) > 1e-6:
                    all_samples.setdefault(who, []).append(
                        (max(ts) / min(ts), statistics.median(ts)))
            suspend.check(label)
            for (lab, who, verdict, t, ratio, conflicts) in rows:
                totals[who] = totals.get(who, 0.0) + t
                c = "" if conflicts is None else str(conflicts)
                r = "  1.00x" if who == "cdclkit" else f"{ratio:>9.2f}x"
                print(f"{lab:<16}{who:<16}{verdict:>9}{t:>9.3f}s{r:>10}{c:>11}")
            print()
            all_disagreements += dis
            all_notes += notes
            all_rows += rows
            want = expected.get(label)
            if want:
                for (lab, who, verdict, _t, _r, _c) in rows:
                    if verdict in (SAT, UNSAT) and verdict != want:
                        all_disagreements.append(
                            f"{lab}: {who} says {verdict}, but the benchmark "
                            f"family declares {want}")

    # Per-instance ratios, aggregated geometrically.
    #
    # A wall-time *sum* is dominated by the slowest instance, and on a
    # benchmark set containing one heavy-tailed random instance that means the
    # sum reports that instance's luck rather than the solver's behaviour.
    # Three separate conclusions in this project's history were drawn from a
    # sum and later turned out to be rand3(250) seed 11 having a good or bad
    # day. The geometric mean of per-instance ratios gives every instance the
    # same weight and is the number to trust when they disagree.
    geomean: dict[str, float] = {}
    per_instance: dict[str, dict[str, float]] = {}
    unfinished: dict[str, int] = {}
    for (lab, who, _v, t, _r, _c) in all_rows:
        per_instance.setdefault(lab, {})[who] = t
        if _v == UNKNOWN:
            unfinished[lab] = unfinished.get(lab, 0) + 1
    print("-" * len(header))

    # Every external solver pays fork+exec+load before it solves anything, and
    # in-process cdclkit does not. The old fix was to drop instances the
    # competitor finished in under 50 ms -- which turned out to be unstable:
    # kissat's uf250 times straddle exactly that boundary, its own speed
    # varied 35% between two runs of the same binary on the same machine, and
    # half the family moved in or out of the sample as a result. The instances
    # that dropped out were the ones where the competitor is fastest, so the
    # exclusion silently flattered us.
    #
    # Measuring the startup cost once and subtracting it keeps every instance
    # and removes the bias at its source.
    startup = {}
    with tempfile.TemporaryDirectory(prefix="cdclkit-startup-") as sd:
        triv = os.path.join(sd, "trivial.cnf")
        with open(triv, "w") as fh:
            fh.write("p cnf 2 1\n1 2 0\n")
        for e in externals:
            ts = sorted(e.run(triv, 10)[1] for _ in range(7))
            startup[e.name] = ts[len(ts) // 2]
    if startup:
        print("c measured process startup, subtracted from every external time:")
        for k, v in sorted(startup.items()):
            print(f"c   {k:<16}{v*1000:6.1f} ms")

    for name in [e.name for e in externals]:
        import math

        # Instances where the external solver finishes faster than its own
        # process startup are measuring `fork`+`exec`, not solving: cdclkit runs
        # in-process and "wins" 50x on a formula neither solver spends real
        # time on.  Those instances are excluded from the ratio.
        base = startup.get(name, 0.0)
        MIN_WORK = 0.005          # after startup removal, only true noise goes
        ratios, skipped = [], 0
        for lab, v in per_instance.items():
            if v.get(name, 0) <= 1e-6 or v.get("cdclkit", 0) <= 1e-6:
                continue
            # If both solvers hit the same wall-clock cap, their ratio is 1.0
            # by construction and says nothing about either. Ten SATLIB `par32`
            # instances did exactly that and dragged the geometric mean toward
            # 1 while measuring nothing at all.
            if unfinished.get(lab, 0) >= 2:
                skipped += 1
                continue
            solving = v[name] - base
            if solving < MIN_WORK:
                skipped += 1
                continue
            ratios.append(v["cdclkit"] / solving)
        if ratios:
            geo = math.exp(sum(math.log(r) for r in ratios) / len(ratios))
            print(f"c vs {name}, per-instance ratio over {len(ratios)} instances "
                  f"({skipped} skipped as startup-dominated, <{MIN_WORK*1000:.0f} ms):")
            print(f"c   geometric mean {geo:.2f}x  "
                  f"(best {min(ratios):.2f}x, worst {max(ratios):.2f}x)")
            print(f"c   >1 means {name} is faster")
            geomean[name] = geo

            # How much of that number is one instance?
            #
            # Against kissat on the 164-instance corpus the aggregate was
            # 1.10 -- second place -- and dropping the single worst instance
            # made it 0.905, which is first. The mean alone could not show
            # that, so it got quoted for weeks as though it were a property of
            # the solver rather than of one satisfiable random formula.
            if len(ratios) > 2:
                trimmed = sorted(ratios)[:-1]
                g1 = math.exp(sum(math.log(r) for r in trimmed) / len(trimmed))
                flips = (geo > 1.0) != (g1 > 1.0)
                note = "  <-- THE RANKING HANGS ON ONE INSTANCE" if flips else ""
                print(f"c   drop the worst instance: {g1:.2f}x{note}")

            # Satisfiable and unsatisfiable instances exercise different halves
            # of the solver -- phase selection and restart policy for one,
            # exhaustive refutation for the other -- so a change that trades
            # one against the other nets out to nothing in the aggregate while
            # looking like progress. Split them.
            by_fam: dict[str, list[float]] = {}
            for lab, v in per_instance.items():
                if (v.get(name, 0) - base) < MIN_WORK or v.get("cdclkit", 0) <= 1e-6:
                    continue
                if unfinished.get(lab, 0) >= 2:
                    continue
                fam = lab.split("/")[0] if "/" in lab else "generated"
                by_fam.setdefault(fam, []).append(v["cdclkit"] / (v[name] - base))
            if len(by_fam) > 1:
                for fam, rs in sorted(by_fam.items(), key=lambda kv: -len(kv[1])):
                    g = math.exp(sum(math.log(r) for r in rs) / len(rs))
                    verdict = "we win " if g < 1.0 else "we lose"
                    print(f"c     {fam:<14} n={len(rs):<4} {g:6.2f}x  {verdict} "
                          f"[{group_of(fam)}]")

                # The comparison that says whether tuning generalised. A
                # configuration chosen against the tune group can only be
                # judged by the holdout group, which nothing was tuned
                # against -- if the two columns disagree sharply, the tuning
                # fitted the corpus rather than improved the solver.
                groups: dict[str, list[float]] = {}
                for fam, rs in by_fam.items():
                    groups.setdefault(group_of(fam), []).extend(rs)
                if len(groups) > 1:
                    print("c   ---- by group ----")
                    for gname, rs in sorted(groups.items()):
                        g = math.exp(sum(math.log(r) for r in rs) / len(rs))
                        print(f"c     {gname:<14} n={len(rs):<4} {g:6.2f}x")
    if args.repeat > 1 and all_samples:
        # Split by instance duration, because the two populations measure
        # different things. The solver is deterministic -- repeated runs give
        # identical conflict counts -- so all spread here is the machine. On a
        # 3 ms instance a few milliseconds of scheduler jitter reads as a 4x
        # swing and tells you nothing; on instances doing real work the noise
        # is about 1%, and that is the figure a performance claim has to clear.
        SUBSTANTIAL = 0.050
        print(f"c run-to-run spread over {args.repeat} repeats "
              f"(max/min per instance; the solver is deterministic, so this is "
              f"machine noise):")
        for who, rs in sorted(all_samples.items()):
            big = sorted(r for r, med in rs if med >= SUBSTANTIAL)
            small = sorted(r for r, med in rs if med < SUBSTANTIAL)
            big_s = (f"{statistics.median(big):5.2f}x (worst {big[-1]:4.2f}x)"
                     if big else "        n/a")
            small_s = (f"{statistics.median(small):5.2f}x" if small else "  n/a")
            print(f"c   {who:<16}>50ms: {big_s} over {len(big):>4}   "
                  f"<50ms: {small_s} over {len(small):>4}")
        print("c   Judge a claim against the >50ms column. The <50ms column is "
              "timing jitter on runs too short to measure.")
    elif args.repeat == 1:
        print("c single run per solver: no error bar. Use --repeat 3 before "
              "quoting any number.")
    suspend.report()
    print("c total wall time per solver:")
    base = totals.get("cdclkit", 0.0)
    for who, t in sorted(totals.items(), key=lambda kv: kv[1]):
        rel = f"  ({base/t:.1f}x faster than cdclkit)" if who != "cdclkit" and t > 0 else ""
        print(f"c   {who:<16}{t:>8.2f}s{rel}")

    if args.record:
        record_run(args.record, args.engine, args.jobs, all_rows, totals, geomean)

    for n in all_notes:
        print(f"c note: {n}")

    if all_disagreements:
        print()
        for d in all_disagreements:
            print(f"c DISAGREEMENT: {d}")
        print(f"c {len(all_disagreements)} verdict disagreement(s) -- one of the "
              "solvers is wrong, and it matters which")
        return 1
    if expected:
        checked = sum(1 for lab in expected if any(r[0] == lab for r in all_rows))
        print(f"c every verdict also matched the benchmark's declared answer "
              f"({checked} instances with ground truth)")
    print("c all solvers agree on every instance")
    return 0


if __name__ == "__main__":
    sys.exit(main())
