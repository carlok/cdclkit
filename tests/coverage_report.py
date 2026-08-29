# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Statement coverage for the `cdclkit` package, using only the standard library.

Run:  python3 tests/coverage_report.py

`trace.Trace` is slow (it hooks every line), so the suite takes about 20x
longer under it than it does normally.  That is fine for a number reported
occasionally; it is not something to put in a commit hook.

The report distinguishes *executable* lines from blank lines, comments,
docstrings and `def`/`class` headers, which `trace` counts inconsistently --
the numbers below count a line as coverable only when it is the first line of a
statement inside a function or module body.
"""

from __future__ import annotations

import argparse
import ast
import os
import pathlib
import sys
import trace
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))


def statement_lines(path: pathlib.Path) -> set[int]:
    """Line numbers of executable statements, excluding docstrings."""
    tree = ast.parse(path.read_text())
    lines: set[int] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.stmt):
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) \
                    and isinstance(node.value.value, str):
                continue  # docstring
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                continue
            lines.add(node.lineno)
    return lines


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--min", type=float, default=0.0, metavar="PCT",
                    help="exit non-zero if total coverage falls below this")
    args = ap.parse_args()

    tracer = trace.Trace(count=1, trace=0, ignoredirs=[sys.prefix, sys.exec_prefix])
    loader = unittest.TestLoader()
    suite = loader.discover(str(ROOT / "tests"), top_level_dir=str(ROOT))
    runner = unittest.TextTestRunner(verbosity=0, stream=open(os.devnull, "w"))
    tracer.runfunc(runner.run, suite)

    counts = tracer.results().counts
    hit: dict[str, set[int]] = {}
    for (filename, lineno), n in counts.items():
        hit.setdefault(os.path.abspath(filename), set()).add(lineno)

    print(f"{'module':<26}{'stmts':>8}{'covered':>9}{'missed':>8}{'%':>7}")
    print("-" * 58)
    total_s = total_c = 0
    for path in sorted((ROOT / "cdclkit").glob("*.py")):
        stmts = statement_lines(path)
        covered = stmts & hit.get(str(path), set())
        total_s += len(stmts)
        total_c += len(covered)
        pct = 100.0 * len(covered) / max(len(stmts), 1)
        print(f"{path.name:<26}{len(stmts):>8}{len(covered):>9}"
              f"{len(stmts)-len(covered):>8}{pct:>6.0f}%")
    print("-" * 58)
    pct = 100.0 * total_c / max(total_s, 1)
    print(f"{'TOTAL':<26}{total_s:>8}{total_c:>9}{total_s-total_c:>8}{pct:>6.0f}%")
    print()
    print("c lits.py and cnf.py read low on purpose: the hot paths inline their")
    print("c helpers rather than calling them (solver.py writes `l ^ 1`, not")
    print("c `neg(l)`), so those lines are exercised without being executed.")
    if args.min:
        if pct < args.min:
            print(f"c FAIL: {pct:.1f}% is below the {args.min:.0f}% floor")
            return 1
        print(f"c ok: {pct:.1f}% >= {args.min:.0f}% floor")
    return 0


if __name__ == "__main__":
    sys.exit(main())
