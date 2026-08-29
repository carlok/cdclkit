# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Adjudicate every (original, refactored) pair five ways. Writes results.jsonl.

Pre-registered before any result was seen:

  widths                8 and 16
  pyeq budget           200_000 conflicts, verify=True (proof emitted and replayed)
  random                200 vectors and 20 vectors, seeded
  edge                  0, +-1, +-2, +-3, MIN, MAX, MIN+1, MAX-1, powers of two
                        and their neighbours; full cartesian product capped at
                        20_000 combinations
  Hypothesis            1000 examples, seeded, database disabled
  CrossHair             `diffbehavior`, width 8 only, 10 s per pair

The headline is the marginal cell: pyeq says False and *every* baseline passes.
Everything else is reported alongside it, including the cells where pyeq is the
one that fails.

Usage:
    python3 run.py --dry-run      corpus parses, subset clean, nothing solved
    python3 run.py                the full adjudication
    python3 run.py --no-crosshair skip the slow phase
"""

from __future__ import annotations

import argparse
import ast
import concurrent.futures as cf
import importlib.util
import inspect
import json
import os
import pathlib
import subprocess
import sys
import textwrap
import time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent))

from corpus import CORPUS                                    # noqa: E402
from guard import falls_off_the_end                          # noqa: E402
from wrapping import evaluate                                # noqa: E402
import baselines as B                                        # noqa: E402

WIDTHS = (8, 16)
MAX_CONFLICTS = 200_000
CROSSHAIR_WIDTH = 8
CROSSHAIR_TIMEOUT = 10
VENV_PY = HERE / ".venv" / "bin" / "python"
VENV_CH = HERE / ".venv" / "bin" / "crosshair"


def load_pass(path: pathlib.Path) -> dict:
    spec = importlib.util.spec_from_file_location(f"ref_{path.stem}", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return {n: f for n, f in vars(mod).items()
            if inspect.isfunction(f) and n.startswith("f_")}


def _norm(fn) -> str:
    """AST dump with positions stripped, for detecting untouched functions."""
    tree = ast.parse(textwrap.dedent(inspect.getsource(fn)))
    fd = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef))
    return ast.dump(ast.Module(body=fd.body, type_ignores=[]))


def crosshair_pair(orig, ref, width: int) -> dict:
    """`crosshair diffbehavior` on the wrapped forms. Its own process."""
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        mod = pathlib.Path(td) / "pair.py"
        mod.write_text(
            "def _w(v, width):\n"
            "    half = 1 << (width - 1)\n"
            "    return ((v + half) & ((1 << width) - 1)) - half\n\n"
            + B.wrapped_source(orig, width, "lhs") + "\n\n"
            + B.wrapped_source(ref, width, "rhs") + "\n"
        )
        t0 = time.perf_counter()
        try:
            p = subprocess.run(
                [str(VENV_CH), "diffbehavior", "pair.lhs", "pair.rhs",
                 "--per_condition_timeout", str(CROSSHAIR_TIMEOUT)],
                cwd=td, capture_output=True, text=True,
                timeout=CROSSHAIR_TIMEOUT * 4,
                env={**os.environ, "PYTHONPATH": td},
            )
            out = (p.stdout + p.stderr).strip()
            # exit 0 = "no differences found", 1 = differences reported
            verdict = "differs" if p.returncode == 1 else (
                "same" if p.returncode == 0 else "error")
        except subprocess.TimeoutExpired:
            out, verdict = "", "timeout"
        return {"verdict": verdict, "seconds": time.perf_counter() - t0,
                "output": out[:400]}


def adjudicate(name, orig, ref, pass_name, do_crosshair) -> dict:
    params = list(inspect.signature(orig).parameters)
    arity = len(params)
    rec = {
        "function": name, "pass": pass_name, "arity": arity,
        "unchanged": _norm(orig) == _norm(ref),
        "guard_excluded": False, "widths": {},
    }

    off_o, off_r = falls_off_the_end(orig), falls_off_the_end(ref)
    if off_o or off_r:
        # pyeq is unsound on these until the fix lands; excluded and counted
        # rather than silently dropped
        rec["guard_excluded"] = True
        rec["guard_side"] = ("original" if off_o else "") + ("refactored" if off_r else "")
        return rec

    import cdclkit.pyeq as pyeq
    for w in WIDTHS:
        widths = {p: w for p in params}
        entry: dict = {}
        try:
            t0 = time.perf_counter()
            r = pyeq.equivalent(orig, ref, widths=widths,
                                max_conflicts=MAX_CONFLICTS)
            entry["pyeq"] = {
                "proved": r.proved, "overflow_only": r.overflow_only,
                "proof_checked": r.proof_checked, "proof_steps": r.proof_steps,
                "counterexample": r.counterexample, "outputs": list(r.outputs)
                if r.outputs else None,
                "python_outputs": list(r.python_outputs) if r.python_outputs else None,
                "conflicts": r.conflicts, "vars": r.vars, "clauses": r.clauses,
                "seconds": time.perf_counter() - t0,
            }
            # Re-simulate every refutation independently. A spurious
            # counterexample would be a compiler bug, and the headline number
            # is exactly a count of these.
            if r.proved is False and r.counterexample:
                a = evaluate(orig, r.counterexample, w)
                b = evaluate(ref, r.counterexample, w)
                entry["pyeq"]["resimulated"] = [a, b]
                entry["pyeq"]["resim_agrees"] = (
                    a != b and list(r.outputs) == [a, b])
        except Exception as e:
            entry["pyeq"] = {"error": f"{type(e).__name__}: {e}"[:300]}

        try:
            entry["random200"] = B.baseline_random(orig, ref, arity, w, 200, 20260829)
            entry["random20"] = B.baseline_random(orig, ref, arity, w, 20, 20260829)
            entry["edge"] = B.baseline_edge(orig, ref, arity, w)
            entry["hypothesis"] = B.baseline_hypothesis(orig, ref, arity, w)
        except Exception as e:
            entry["sampling_error"] = f"{type(e).__name__}: {e}"[:200]

        if do_crosshair and w == CROSSHAIR_WIDTH:
            entry["crosshair"] = crosshair_pair(orig, ref, w)
        rec["widths"][str(w)] = entry
    return rec


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--no-crosshair", action="store_true")
    ap.add_argument("--only", help="restrict to one pass, e.g. opus-1")
    args = ap.parse_args()

    originals = {f.__name__: f for f in CORPUS}
    passes = sorted(p for p in (HERE / "refactors").glob("*.py"))
    if args.only:
        passes = [p for p in passes if p.stem == args.only]
    print(f"c {len(originals)} functions x {len(passes)} passes "
          f"x {len(WIDTHS)} widths")

    if args.dry_run:
        for p in passes:
            fns = load_pass(p)
            missing = set(originals) - set(fns)
            extra = set(fns) - set(originals)
            unchanged = sum(1 for n in originals if n in fns
                            and _norm(originals[n]) == _norm(fns[n]))
            guard = sum(1 for n in fns if falls_off_the_end(fns[n]))
            print(f"  {p.stem:<12} {len(fns):>3} fns  missing={len(missing)} "
                  f"extra={len(extra)} unchanged={unchanged} "
                  f"falls_off_end={guard}")
            if missing:
                print(f"               missing: {sorted(missing)[:6]}")
        return 0

    out = HERE / "results.jsonl"
    n = 0
    with out.open("w") as fh:
        for p in passes:
            fns = load_pass(p)
            t0 = time.perf_counter()
            for name, orig in originals.items():
                if name not in fns:
                    fh.write(json.dumps({"function": name, "pass": p.stem,
                                         "missing": True}) + "\n")
                    continue
                rec = adjudicate(name, orig, fns[name], p.stem,
                                 not args.no_crosshair)
                fh.write(json.dumps(rec) + "\n")
                fh.flush()
                n += 1
            print(f"  {p.stem:<12} done in {time.perf_counter()-t0:6.1f}s")
    print(f"c {n} pairs -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
