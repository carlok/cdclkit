# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Command line interface: ``python -m cdclkit <command> ...``.

Follows SAT competition conventions where they exist, because that is what
scripts around a solver expect:

* solution lines ``s SATISFIABLE`` / ``s UNSATISFIABLE`` / ``s UNKNOWN``;
* the model on ``v`` lines terminated by ``0``;
* comments on ``c`` lines;
* exit status **10** for SAT, **20** for UNSAT, **0** for unknown, **1** for
  an error, and **30** when a proof check fails (a solver that emits a bad
  proof must be loudly distinguishable from one that merely times out).

Commands::

    solve FILE      solve a DIMACS CNF, optionally emitting and self-checking a proof
                    (--jobs N runs a parallel portfolio)
    check FILE PROOF  verify a DRAT proof against a formula
    prep  FILE      preprocess only, write the reduced formula
    count FILE      enumerate models (with optional projection)
    opt   FILE      minimise the number of true literals among given variables
    gen   KIND ...  generate benchmark families
    mus   FILE      extract a minimal unsatisfiable subset (why is it UNSAT?)
    stats FILE      report formula statistics
"""

from __future__ import annotations

import argparse
import sys
import time
from typing import Sequence

from dratify.cnf import CNF, parse_dimacs_file, write_dimacs
from .encodings import Encoder, optimise
from dratify.lits import from_dimacs, mk_lit, to_dimacs
from .mus import MUSExtractor
from .portfolio import performance_cores, solve_portfolio
from .preprocess import Preprocessor
from dratify.proof import MemoryProof, ProofWriter, check_proof, parse_proof
from .solver import Config, Solver

def _native_ok() -> bool:
    from . import native

    return native.available()


EXIT_SAT = 10
EXIT_UNSAT = 20
EXIT_UNKNOWN = 0
EXIT_ERROR = 1
EXIT_BAD_PROOF = 30


def _emit_model(model: Sequence[bool], out=None, per_line: int = 20) -> None:
    # resolved at call time, not at import time: a default of `sys.stdout` binds
    # the stream object once and then ignores any later redirection
    out = sys.stdout if out is None else out
    lits = [(i + 1) if b else -(i + 1) for i, b in enumerate(model)]
    for i in range(0, len(lits), per_line):
        out.write("v " + " ".join(str(x) for x in lits[i : i + per_line]) + "\n")
    out.write("v 0\n")


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------


def cmd_solve(args) -> int:
    f = parse_dimacs_file(args.file)
    print(f"c cdclkit :: {args.file}")
    print(f"c formula: {f.nvars} vars, {f.nclauses} clauses")

    proof_sink = None
    mem_proof = None
    if args.self_check:
        mem_proof = MemoryProof()
        proof_sink = mem_proof
    elif args.proof:
        proof_sink = ProofWriter(args.proof)

    original = f.copy() if (args.self_check or args.check_model) else None

    pre = None
    if args.preprocess:
        t0 = time.perf_counter()
        pre = Preprocessor(f, proof=proof_sink)
        f = pre.run(rounds=args.prep_rounds)
        print(f"c preprocessing took {time.perf_counter()-t0:.3f}s")
        for line in pre.stats.report().splitlines():
            print(line)
        print(f"c reduced: {f.nvars} vars, {f.nclauses} clauses")

    cfg = Config(
        restart=args.restart,
        var_decay=args.var_decay,
        ccmin=args.ccmin,
        phase_saving=not args.no_phase_saving,
        rnd_freq=args.rnd_freq,
        rnd_seed=args.seed,
    )
    if getattr(args, "adaptive", False):
        from .pipeline import solve_adaptive

        pr = solve_adaptive(f, engine="native" if _native_ok() else "python")
        print(pr.report())
        print(f"c {pr.conflicts} conflicts in {pr.seconds:.3f}s")
        if pr.sat:
            if args.check_model:
                base = original if original is not None else f
                if base.falsified_clauses(pr.model):
                    print("c MODEL CHECK FAILED")
                    return EXIT_ERROR
                print("c model verified against the input formula")
            print("s SATISFIABLE")
            if not args.no_model:
                _emit_model(pr.model)
            return EXIT_SAT
        print("s UNSATISFIABLE")
        return EXIT_UNSAT

    jobs = args.jobs
    if jobs is not None and jobs > 1:
        # Parallel portfolio.  Only the winning worker's proof exists, and
        # because workers share no clauses it is a complete refutation on its
        # own -- see cdclkit/portfolio.py.
        pr = solve_portfolio(f, jobs=jobs, want_proof=proof_sink is not None)
        if not pr.finished:
            print("s UNKNOWN")
            return EXIT_UNKNOWN
        print(pr.report())
        result = pr.sat
        s = Solver(0)  # placeholder so the reporting below has a stats object
        s.stats.conflicts = pr.stats.get("conflicts", 0)
        s.stats.propagations = pr.stats.get("propagations", 0)
        s.stats.decisions = pr.stats.get("decisions", 0)
        s.model = pr.model or []
        if proof_sink is not None and pr.proof_steps:
            for kind, lits in pr.proof_steps:
                (proof_sink.delete if kind == "d" else proof_sink.add)(lits)
    else:
        s = Solver(f.nvars, proof=proof_sink, config=cfg)
        ok = s.add_cnf(f)
        result = s.solve(max_conflicts=args.conflicts) if ok else False
        print(s.stats.report())

    if result is None:
        print("s UNKNOWN")
        return EXIT_UNKNOWN
    if result:
        model = s.model
        if pre is not None:
            model = pre.reconstruct(model)
        if args.check_model:
            base = original if original is not None else f
            bad = base.falsified_clauses(model)
            if bad:
                print(f"c MODEL CHECK FAILED: {len(bad)} clauses unsatisfied")
                return EXIT_ERROR
            print("c model verified against the input formula")
        print("s SATISFIABLE")
        if not args.no_model:
            _emit_model(model)
        return EXIT_SAT

    print("s UNSATISFIABLE")
    if mem_proof is not None:
        t0 = time.perf_counter()
        res = check_proof(original, mem_proof)
        print(f"c proof self-check took {time.perf_counter()-t0:.3f}s "
              f"({len(mem_proof.steps)} steps)")
        for line in res.report().splitlines():
            print(line)
        if not res.ok:
            return EXIT_BAD_PROOF
    elif isinstance(proof_sink, ProofWriter):
        proof_sink.close()
        print(f"c proof written to {args.proof} "
              f"({proof_sink.n_add} additions, {proof_sink.n_del} deletions)")
    return EXIT_UNSAT


def cmd_check(args) -> int:
    f = parse_dimacs_file(args.file)
    with open(args.proof, "r", encoding="ascii") as fh:
        steps = parse_proof(fh.read())
    print(f"c checking {len(steps)} proof steps against {args.file}")
    t0 = time.perf_counter()
    res = check_proof(f, steps, check_rat=not args.no_rat, apply_deletions=not args.keep_deleted)
    print(f"c took {time.perf_counter()-t0:.3f}s")
    print(res.report())
    return EXIT_UNSAT if res.ok else EXIT_BAD_PROOF


def cmd_prep(args) -> int:
    f = parse_dimacs_file(args.file)
    pre = Preprocessor(f, do_bve=not args.no_bve, do_bce=not args.no_bce)
    red = pre.run(rounds=args.prep_rounds)
    print(pre.summary(red))
    if args.out:
        red.save(args.out)
        print(f"c reduced formula written to {args.out}")
    else:
        write_dimacs(red, sys.stdout)
    return EXIT_UNKNOWN


def cmd_count(args) -> int:
    f = parse_dimacs_file(args.file)
    s = Solver(f.nvars)
    if not s.add_cnf(f):
        print("c 0 models")
        print("s UNSATISFIABLE")
        return EXIT_UNSAT
    proj = None
    if args.project:
        proj = [abs(int(x)) - 1 for x in args.project.split(",")]
    n = 0
    for model in s.enumerate_models(projection=proj, limit=args.limit):
        n += 1
        if args.show:
            print("v " + " ".join(str(to_dimacs(mk_lit(v, not b))) for v, b in enumerate(model)))
    print(f"c models found: {n}" + (" (limit reached)" if args.limit and n >= args.limit else ""))
    return EXIT_SAT if n else EXIT_UNSAT


def cmd_opt(args) -> int:
    f = parse_dimacs_file(args.file)
    s = Solver(f.nvars)
    if not s.add_cnf(f):
        print("s UNSATISFIABLE")
        return EXIT_UNSAT
    if args.soft:
        soft = [from_dimacs(int(x)) for x in args.soft.split(",")]
    else:
        soft = [mk_lit(v) for v in range(f.nvars)]
    res = optimise(s, soft, minimise=not args.maximise,
                   on_improve=lambda c, m: print(f"c improved to {c}"))
    if res is None:
        print("s UNSATISFIABLE")
        return EXIT_UNSAT
    count, model = res
    print(f"c optimum: {count}")
    print("s SATISFIABLE")
    _emit_model(model[: f.nvars])
    return EXIT_SAT


def cmd_mus(args) -> int:
    """Explain an UNSAT answer: which clauses are actually to blame."""
    f = parse_dimacs_file(args.file)
    ex = MUSExtractor(f)
    t0 = time.perf_counter()
    if args.method == "core":
        result = ex.core()
    elif args.method == "quickxplain":
        result = ex.quickxplain()
    else:
        result = ex.deletion()
    dt = time.perf_counter() - t0
    if not result:
        print("c the formula is satisfiable: there is nothing to explain")
        print("s SATISFIABLE")
        return EXIT_SAT
    print(f"c {args.method}: {len(result)} of {f.nclauses} clauses, "
          f"{ex.calls} solver calls, {dt:.3f}s")
    if args.verify:
        ok, msg = ex.verify(result)
        print(f"c {msg}")
        if not ok:
            return EXIT_ERROR
    for i in result:
        body = " ".join(str(to_dimacs(l)) for l in f.clauses[i])
        print(f"c   clause {i}: {body} 0")
    print("s UNSATISFIABLE")
    return EXIT_UNSAT


def cmd_stats(args) -> int:
    f = parse_dimacs_file(args.file)
    st = f.stats()
    for k, v in st.items():
        print(f"c {k:<10}: {v}")
    return EXIT_UNKNOWN


# --------------------------------------------------------------------------
# benchmark generators
# --------------------------------------------------------------------------


def gen_php(pigeons: int, holes: int) -> CNF:
    """Pigeonhole: `pigeons` items into `holes` slots, at most one per slot."""
    f = CNF()
    f.comments.append(f"pigeonhole {pigeons} pigeons into {holes} holes")
    x = [[f.new_var(f"p{i}h{j}") for j in range(holes)] for i in range(pigeons)]
    for i in range(pigeons):
        f.add([mk_lit(x[i][j]) for j in range(holes)])
    for j in range(holes):
        for i in range(pigeons):
            for k in range(i + 1, pigeons):
                f.add([mk_lit(x[i][j], True), mk_lit(x[k][j], True)])
    return f


def gen_random_ksat(n: int, m: int, k: int, seed: int) -> CNF:
    import random

    rng = random.Random(seed)
    f = CNF(n)
    f.comments.append(f"uniform random {k}-SAT n={n} m={m} seed={seed}")
    for _ in range(m):
        vs = rng.sample(range(n), k)
        f.add([mk_lit(v, rng.random() < 0.5) for v in vs])
    return f


def gen_queens(n: int) -> CNF:
    f = CNF()
    f.comments.append(f"{n}-queens")
    enc = Encoder(f)
    q = [[f.new_var(f"q{r}c{c}") for c in range(n)] for r in range(n)]
    for r in range(n):
        enc.exactly_one([mk_lit(q[r][c]) for c in range(n)])
    for c in range(n):
        enc.exactly_one([mk_lit(q[r][c]) for r in range(n)])
    for d in range(-n + 1, n):
        diag = [mk_lit(q[r][r - d]) for r in range(n) if 0 <= r - d < n]
        if len(diag) > 1:
            enc.at_most_one(diag)
        anti = [mk_lit(q[r][d - r]) for r in range(n) if 0 <= d - r < n]
        if len(anti) > 1:
            enc.at_most_one(anti)
    return f


def gen_parity(n: int, seed: int) -> CNF:
    """A random XOR (parity) system -- exponentially hard for pure resolution."""
    import random

    rng = random.Random(seed)
    f = CNF(n)
    enc = Encoder(f)
    f.comments.append(f"random parity system n={n} seed={seed}")
    for _ in range(n):
        vs = rng.sample(range(n), 3)
        enc.xor_chain([mk_lit(v) for v in vs], value=rng.random() < 0.5)
    return f


def cmd_gen(args) -> int:
    if args.kind == "php":
        f = gen_php(args.n + 1, args.n)
    elif args.kind == "random":
        f = gen_random_ksat(args.n, args.m or int(4.26 * args.n), args.k, args.seed)
    elif args.kind == "queens":
        f = gen_queens(args.n)
    elif args.kind == "parity":
        f = gen_parity(args.n, args.seed)
    else:
        print(f"unknown family {args.kind}", file=sys.stderr)
        return EXIT_ERROR
    if args.out:
        f.save(args.out)
        print(f"c wrote {args.out}: {f.nvars} vars, {f.nclauses} clauses")
    else:
        write_dimacs(f, sys.stdout)
    return EXIT_UNKNOWN


# --------------------------------------------------------------------------
# argument parsing
# --------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="cdclkit", description="CDCL SAT solving with checkable proofs"
    )
    # Reports the engine too. "Which cdclkit is this" and "was the accelerator
    # actually loaded" are the same question when a benchmark number looks
    # wrong, and the second is the one people forget to ask.
    from . import __version__, native

    p.add_argument(
        "--version", action="version",
        version=(f"cdclkit {__version__} "
                 f"(native engine: {'yes' if native.available() else 'no'})"),
    )
    sub = p.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("solve", help="solve a DIMACS CNF file")
    s.add_argument("file")
    s.add_argument("--proof", help="write a DRAT proof here (UNSAT only)")
    s.add_argument("--self-check", action="store_true",
                   help="keep the proof in memory and verify it before reporting UNSAT")
    s.add_argument("--check-model", action="store_true",
                   help="verify the model against the input before reporting SAT")
    s.add_argument("--preprocess", action="store_true")
    s.add_argument("--adaptive", action="store_true",
                   help="probe briefly, then preprocess only if the instance "
                        "turns out to be hard enough to repay it")
    s.add_argument("--prep-rounds", type=int, default=3)
    s.add_argument("--conflicts", type=int, default=None, help="conflict budget")
    s.add_argument("--restart", default="glucose", choices=["glucose", "luby", "none"])
    s.add_argument("--var-decay", type=float, default=0.8)
    s.add_argument("--ccmin", default="deep", choices=["deep", "basic", "none"])
    s.add_argument("--no-phase-saving", action="store_true")
    s.add_argument("--rnd-freq", type=float, default=0.0)
    s.add_argument("--seed", type=int, default=91648253)
    s.add_argument("--no-model", action="store_true", help="suppress the v lines")
    s.add_argument("--jobs", "-j", type=int, default=None,
                   metavar="N",
                   help=f"run a parallel portfolio of N differently-configured "
                        f"solvers and take the first answer (this machine has "
                        f"{performance_cores()} performance cores; more workers "
                        f"than that is usually slower)")
    s.set_defaults(func=cmd_solve)

    c = sub.add_parser("check", help="verify a DRAT proof")
    c.add_argument("file")
    c.add_argument("proof")
    c.add_argument("--no-rat", action="store_true", help="RUP only")
    c.add_argument("--keep-deleted", action="store_true", help="ignore deletion lines")
    c.set_defaults(func=cmd_check)

    pr = sub.add_parser("prep", help="preprocess a formula")
    pr.add_argument("file")
    pr.add_argument("--out")
    pr.add_argument("--prep-rounds", type=int, default=3)
    pr.add_argument("--no-bve", action="store_true")
    pr.add_argument("--no-bce", action="store_true")
    pr.set_defaults(func=cmd_prep)

    ct = sub.add_parser("count", help="enumerate models")
    ct.add_argument("file")
    ct.add_argument("--limit", type=int, default=0)
    ct.add_argument("--project", help="comma-separated 1-based variables")
    ct.add_argument("--show", action="store_true")
    ct.set_defaults(func=cmd_count)

    op = sub.add_parser("opt", help="minimise true literals among a soft set")
    op.add_argument("file")
    op.add_argument("--soft", help="comma-separated DIMACS literals")
    op.add_argument("--maximise", action="store_true")
    op.set_defaults(func=cmd_opt)

    mu = sub.add_parser("mus", help="extract a minimal unsatisfiable subset")
    mu.add_argument("file")
    mu.add_argument("--method", default="deletion",
                    choices=["deletion", "quickxplain", "core"])
    mu.add_argument("--verify", action="store_true",
                    help="check that the result is unsatisfiable and minimal")
    mu.set_defaults(func=cmd_mus)

    st = sub.add_parser("stats", help="formula statistics")
    st.add_argument("file")
    st.set_defaults(func=cmd_stats)

    g = sub.add_parser("gen", help="generate benchmark instances")
    g.add_argument("kind", choices=["php", "random", "queens", "parity"])
    g.add_argument("-n", type=int, default=8)
    g.add_argument("-m", type=int, default=0)
    g.add_argument("-k", type=int, default=3)
    g.add_argument("--seed", type=int, default=1)
    g.add_argument("--out")
    g.set_defaults(func=cmd_gen)

    return p


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return args.func(args)
    except FileNotFoundError as e:
        print(f"c error: {e}", file=sys.stderr)
        return EXIT_ERROR
    except IsADirectoryError as e:
        print(f"c error: {e}", file=sys.stderr)
        return EXIT_ERROR
    except PermissionError as e:
        print(f"c error: {e}", file=sys.stderr)
        return EXIT_ERROR
    except ValueError as e:
        # Malformed DIMACS. The parser raises with a line number and the
        # offending token, which is the useful half of a traceback; the other
        # half is our call stack, which tells the user nothing about their
        # file and reads like a crash.
        print(f"c error: {e}", file=sys.stderr)
        return EXIT_ERROR
    except UnicodeDecodeError as e:
        print(f"c error: not a text file ({e})", file=sys.stderr)
        return EXIT_ERROR
    except BrokenPipeError:  # pragma: no cover - `cdclkit ... | head`
        # Python prints its own noisy warning at shutdown unless stdout is
        # closed first, and `| head` is a normal thing to do to a solver that
        # prints a model with 100k literals in it.
        try:
            sys.stdout.close()
        except Exception:
            pass
        return EXIT_ERROR
    except KeyboardInterrupt:  # pragma: no cover - interactive
        print("c interrupted", file=sys.stderr)
        return EXIT_UNKNOWN


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
