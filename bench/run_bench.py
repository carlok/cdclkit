# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Benchmark harness: instance families x solver configurations, as a table.

Run:  python3 bench/run_bench.py [--quick] [--proofs]

Families:

``php(n)``      pigeonhole, n+1 pigeons into n holes.  Unsatisfiable, and
                *provably* exponential for resolution (Haken 1985), so it is
                the honest measure of raw conflict throughput -- no amount of
                heuristic cleverness escapes the lower bound.
``rand3(n)``    uniform random 3-SAT at ratio 4.26, the satisfiability
                threshold, where instances are hardest on average.
``queens(n)``   n-queens: heavily constrained, satisfiable, dominated by
                propagation through exactly-one encodings.
``parity(n)``   random 3-XOR systems.  Gaussian elimination solves these in
                polynomial time; resolution needs exponential size, so this is
                where a CDCL solver looks worst and knowing that matters.
``colour(k)``   k-colouring refutations of Mycielskians.

The table reports conflicts, propagations per second and wall time.  Nothing
here is a claim about competing with C solvers -- it is a regression guard and
a way to see what each heuristic actually buys.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from cdclkit.cli import gen_php, gen_parity, gen_queens, gen_random_ksat
from dratify.cnf import CNF
from cdclkit.encodings import Encoder
from dratify.lits import mk_lit, neg
from dratify.proof import MemoryProof, check_proof
from cdclkit.solver import Config, Solver


def mycielski_colouring(k: int, colours: int) -> CNF:
    n, edges = 2, [(0, 1)]
    for _ in range(k - 2):
        m = n
        new = list(edges)
        for (a, b) in edges:
            new.append((a, m + b))
            new.append((b, m + a))
        for i in range(n):
            new.append((m + i, 2 * m))
        n, edges = 2 * m + 1, new
    f = CNF()
    enc = Encoder(f)
    x = [[mk_lit(f.new_var()) for _ in range(colours)] for _ in range(n)]
    for v in range(n):
        enc.exactly_one(x[v])
    for (a, b) in edges:
        for c in range(colours):
            f.add([neg(x[a][c]), neg(x[b][c])])
    for v in range(min(n, colours)):
        for c in range(v + 1, colours):
            f.add([neg(x[v][c])])
    return f


def gen_miter(width: int, bug: bool = False) -> CNF:
    """Equivalence-check two adder implementations: a ripple-carry against a
    carry-lookahead.  UNSAT when they agree.

    This is the *structured* shape the crafted families lack.  A miter is built
    from gates, so most of its variables are Tseitin auxiliaries defined by
    two- and three-literal clauses -- which is precisely what bounded variable
    elimination was invented to remove.  Without an instance like this in the
    set, preprocessing has nothing to bite on and its value cannot be measured.
    """
    f = CNF()
    enc = Encoder(f)
    a = [mk_lit(f.new_var()) for _ in range(width)]
    b = [mk_lit(f.new_var()) for _ in range(width)]
    cin = mk_lit(f.new_var())

    # ripple-carry
    s1, c = [], cin
    for i in range(width):
        ab = enc.xor_gate(a[i], b[i])
        s1.append(enc.xor_gate(ab, c))
        c = enc.or_gate([enc.and_gate([a[i], b[i]]),
                         enc.and_gate([a[i], c]),
                         enc.and_gate([b[i], c])])
    c1 = c

    # carry-lookahead
    g = [enc.and_gate([a[i], b[i]]) for i in range(width)]
    pr = [enc.xor_gate(a[i], b[i]) for i in range(width)]
    carries = [cin]
    for i in range(width):
        terms = [g[i]]
        for j in range(i - 1, -1, -1):
            if bug and i == width // 2 and j == 1:
                continue
            terms.append(enc.and_gate([g[j]] + [pr[t] for t in range(j + 1, i + 1)]))
        terms.append(enc.and_gate([cin] + [pr[t] for t in range(0, i + 1)]))
        carries.append(enc.or_gate(terms))
    s2 = [enc.xor_gate(pr[i], carries[i]) for i in range(width)]

    diffs = [enc.xor_gate(x, y) for x, y in zip(s1, s2)] + [enc.xor_gate(c1, carries[-1])]
    f.add(diffs)
    f.comments.append(f"{width}-bit adder miter (ripple-carry vs carry-lookahead)")
    return f


def gen_bmc(width: int, steps: int, free_seed: bool = True) -> CNF:
    """Bounded model checking of an LFSR: is the all-zero state reachable from
    *any* non-zero seed within `steps`?  UNSAT, and structured the way unrolled
    hardware is -- one copy of the transition relation per time step, so the
    formula is highly repetitive and full of auxiliary variables.

    `free_seed` is what makes this an interesting instance rather than a
    calculation.  With the seed pinned to a constant the whole unrolling is
    determined and unit propagation evaluates it, so the solver never searches
    and the instance measures nothing.  Leaving the seed free (constrained only
    to be non-zero) forces reasoning over every starting state.
    """
    # The feedback MUST include the top bit.  The transition shifts and drops
    # bit width-1, so if that bit does not feed back the map is not injective,
    # states collapse, and the all-zero state really is reachable -- the
    # instance silently becomes SAT in zero conflicts and measures nothing.
    taps = tuple(sorted({0, width // 3, width // 2, width - 1}))
    f = CNF()
    enc = Encoder(f)
    st = [[mk_lit(f.new_var()) for _ in range(width)] for _ in range(steps + 1)]
    for t in range(steps):
        cur, nxt = st[t], st[t + 1]
        fb = cur[taps[0]]
        for tap in taps[1:]:
            fb = enc.xor_gate(fb, cur[tap])
        enc.equiv(nxt[0], fb)
        for i in range(1, width):
            enc.equiv(nxt[i], cur[i - 1])
    if free_seed:
        f.add(list(st[0]))  # some seed bit is set: the state is non-zero
    else:
        for i, l in enumerate(st[0]):
            f.add([l] if i == 0 else [neg(l)])
    f.add([enc.and_gate([neg(l) for l in st[t]]) for t in range(steps + 1)])
    f.comments.append(f"BMC: {width}-bit LFSR unrolled {steps} steps")
    return f


def gen_factor(bits: int, target: int) -> CNF:
    """Circuit for `a * b == target` with `a, b > 1`, as an array multiplier.

    With a prime target this is unsatisfiable, structured, and genuinely hard:
    multiplier equivalence and factoring are the standard examples of instances
    where resolution proofs blow up. It is also the shape that preprocessing is
    supposed to reward -- an array multiplier is thousands of AND/XOR gates,
    so nearly every variable is a Tseitin auxiliary defined by a handful of
    short clauses, which is exactly what bounded variable elimination consumes.

    The crafted families (pigeonhole, colouring) have no such redundancy, which
    is why they cannot measure preprocessing at all.
    """
    f = CNF()
    enc = Encoder(f)
    a = [mk_lit(f.new_var(f"a{i}")) for i in range(bits)]
    b = [mk_lit(f.new_var(f"b{i}")) for i in range(bits)]
    width = 2 * bits

    # accumulate shifted partial products with a ripple-carry adder per row
    acc = [enc.false_lit] * width
    for i in range(bits):
        row = [enc.false_lit] * width
        for j in range(bits):
            if i + j < width:
                row[i + j] = enc.and_gate([a[i], b[j]])
        carry = enc.false_lit
        new = []
        for k in range(width):
            x, y = acc[k], row[k]
            xy = enc.xor_gate(x, y)
            new.append(enc.xor_gate(xy, carry))
            carry = enc.or_gate([enc.and_gate([x, y]),
                                 enc.and_gate([x, carry]),
                                 enc.and_gate([y, carry])])
        acc = new

    for k in range(width):
        bit = (target >> k) & 1
        f.add([acc[k] if bit else neg(acc[k])])

    # both factors strictly greater than one
    f.add(a[1:])
    f.add(b[1:])
    f.comments.append(f"factor {target} into two {bits}-bit factors > 1")
    return f


def families(quick: bool):
    out = [
        ("php(6)", gen_php(7, 6)),
        ("php(7)", gen_php(8, 7)),
        ("rand3(150)", gen_random_ksat(150, 639, 3, 1)),
        ("rand3(200)", gen_random_ksat(200, 852, 3, 7)),
        ("queens(25)", gen_queens(25)),
        ("parity(40)", gen_parity(40, 2)),
        ("colour M(5),4", mycielski_colouring(5, 4)),
        ("miter(8)", gen_miter(8)),
        ("bmc(12,10)", gen_bmc(12, 10)),
        ("factor(14b)", gen_factor(14, 187881877)),
    ]
    if not quick:
        out += [
            ("php(8)", gen_php(9, 8)),
            ("rand3(250)", gen_random_ksat(250, 1065, 3, 11)),
            ("queens(40)", gen_queens(40)),
            ("colour M(6),5", mycielski_colouring(6, 5)),
            ("miter(12)", gen_miter(12)),
            ("bmc(16,24)", gen_bmc(16, 24)),
            ("factor(16b)", gen_factor(16, 3006385357)),
        ]
    return out


CONFIGS = {
    # The default is Luby restarts with target phases as of the measurement in
    # CHECKPOINT_LOG. "glucose" is kept as a named configuration rather than
    # deleted: it was the default for most of this project's life, every
    # earlier number in the record was produced by it, and a claim that the
    # new default is better is only checkable if the old one still runs.
    "default": Config(),
    "glucose": Config(restart="glucose", target_phase=False),
    "no-target": Config(target_phase=False),
    "no-restart": Config(restart="none"),
    "no-ccmin": Config(ccmin="none"),
    "no-phase": Config(phase_saving=False),
}


def run_one(f: CNF, cfg: Config, proof: bool = False):
    pr = MemoryProof() if proof else None
    s = Solver(f.nvars, proof=pr, config=cfg)
    ok = s.add_cnf(f)
    t0 = time.perf_counter()
    res = s.solve() if ok else False
    dt = time.perf_counter() - t0
    verdict = "SAT" if res else "UNSAT"
    check = ""
    if proof and not res:
        t1 = time.perf_counter()
        r = check_proof(f, pr)
        check = f"{'ok' if r.ok else 'BAD'} {len(pr.steps)} steps {time.perf_counter()-t1:.2f}s"
    return verdict, dt, s.stats, check


BASELINE = pathlib.Path(__file__).with_name("baseline.json")


def load_baseline() -> dict:
    if not BASELINE.exists():
        return {}
    return json.loads(BASELINE.read_text())


def compare(results: dict, baseline: dict, tolerance: float) -> int:
    """Report conflict-count regressions.  Returns the number of failures.

    Conflicts, not seconds: wall time depends on the machine, the Python build
    and what else is running, but conflict counts are deterministic for a fixed
    seed and configuration.  A change that makes the solver take more conflicts
    on the same instance is a real algorithmic regression; a change that makes
    it slower at the same conflict count is a performance issue the timing
    column will show.
    """
    failures = 0
    print()
    print(f"{'instance / config':<34}{'baseline':>10}{'now':>10}{'delta':>10}")
    print("-" * 64)
    for key, now in sorted(results.items()):
        was = baseline.get(key)
        if was is None:
            print(f"{key:<34}{'-':>10}{now:>10}{'new':>10}")
            continue
        delta = (now - was) / max(was, 1)
        flag = ""
        if now > was * (1 + tolerance):
            flag = "  REGRESSION"
            failures += 1
        elif now < was * (1 - tolerance):
            flag = "  improved"
        print(f"{key:<34}{was:>10}{now:>10}{delta:>+9.0%}{flag}")
    print("-" * 64)
    print(f"{failures} regression(s) beyond {tolerance:.0%} tolerance")
    return failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="skip the slow instances")
    ap.add_argument("--proofs", action="store_true", help="also emit and check proofs")
    ap.add_argument("--configs", default="default",
                    help="comma-separated config names, or 'all'")
    ap.add_argument("--save-baseline", action="store_true",
                    help="record the current conflict counts as the baseline")
    ap.add_argument("--check-baseline", action="store_true",
                    help="compare against the baseline; exit 1 on a regression")
    ap.add_argument("--tolerance", type=float, default=0.10,
                    help="fractional conflict increase tolerated (default 10%%)")
    args = ap.parse_args()

    names = list(CONFIGS) if args.configs == "all" else args.configs.split(",")
    insts = families(args.quick)

    header = f"{'instance':<16}{'vars':>7}{'clauses':>9}  {'config':<12}{'result':>7}"
    header += f"{'conflicts':>11}{'kprop/s':>10}{'time':>9}"
    if args.proofs:
        header += "  proof"
    print(header)
    print("-" * len(header))
    total = 0.0
    results: dict[str, int] = {}
    for label, f in insts:
        for name in names:
            verdict, dt, st, check = run_one(f, CONFIGS[name], args.proofs)
            total += dt
            results[f"{label} / {name}"] = st.conflicts
            kprops = st.propagations / max(dt, 1e-9) / 1000
            line = (f"{label:<16}{f.nvars:>7}{f.nclauses:>9}  {name:<12}{verdict:>7}"
                    f"{st.conflicts:>11}{kprops:>10.0f}{dt:>8.2f}s")
            if args.proofs:
                line += f"  {check}"
            print(line)
    print("-" * len(header))
    print(f"total wall time: {total:.2f}s")

    if args.save_baseline:
        BASELINE.write_text(json.dumps(results, indent=1, sort_keys=True) + "\n")
        print(f"baseline written to {BASELINE} ({len(results)} entries)")
    if args.check_baseline:
        base = load_baseline()
        if not base:
            print("no baseline recorded; run with --save-baseline first")
            return 1
        return 1 if compare(results, base, args.tolerance) else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
