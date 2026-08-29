# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Second condition: what ordinary Python-semantics testing finds, plus CrossHair.

Phase 1 gave every sampling baseline the circuit's fixed-width semantics, which
is the fair comparison against pyeq but is *not* what a team actually does. This
phase re-runs the same baselines in plain Python semantics -- the condition the
refactoring agents themselves ran, and the one a normal test suite runs -- and
adds CrossHair, pyeq's nearest competitor, in both conditions.

CrossHair runs on the 105 substantively changed pairs only. The other 183 are
byte-identical ASTs, where `diffbehavior` can only answer "same"; that is not a
result, it is a tautology, and it costs 30 minutes.

Parameters are annotated `: int` for CrossHair. Without annotations it explores
`a=''` and reports a TypeError difference, which is a real fact about untyped
Python and has nothing to do with the refactor.
"""

from __future__ import annotations

import ast, concurrent.futures as cf, importlib.util, inspect, json, os
import pathlib, subprocess, sys, tempfile, textwrap, time

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from corpus import CORPUS                       # noqa: E402
import baselines as B                           # noqa: E402

CH = str(HERE / ".venv" / "bin" / "crosshair")
CH_WIDTH, CH_TIMEOUT = 8, 10


def annotate(src: str) -> str:
    tree = ast.parse(src)
    fd = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef))
    for a in fd.args.args:
        a.annotation = ast.Name(id="int", ctx=ast.Load())
    return ast.unparse(ast.fix_missing_locations(tree))


def plain_source(fn, name: str) -> str:
    tree = ast.parse(textwrap.dedent(inspect.getsource(fn)))
    fd = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef))
    fd.name, fd.decorator_list = name, []
    return ast.unparse(ast.fix_missing_locations(fd))


def crosshair(orig, ref, wrapped: bool) -> dict:
    with tempfile.TemporaryDirectory() as td:
        if wrapped:
            body = ("def _w(v: int, width: int) -> int:\n"
                    "    half = 1 << (width - 1)\n"
                    "    return ((v + half) & ((1 << width) - 1)) - half\n\n"
                    + annotate(B.wrapped_source(orig, CH_WIDTH, "lhs")) + "\n\n"
                    + annotate(B.wrapped_source(ref, CH_WIDTH, "rhs")) + "\n")
        else:
            body = (annotate(plain_source(orig, "lhs")) + "\n\n"
                    + annotate(plain_source(ref, "rhs")) + "\n")
        (pathlib.Path(td) / "pair.py").write_text(body)
        t0 = time.perf_counter()
        try:
            p = subprocess.run(
                [CH, "diffbehavior", "pair.lhs", "pair.rhs",
                 "--per_condition_timeout", str(CH_TIMEOUT)],
                cwd=td, capture_output=True, text=True, timeout=CH_TIMEOUT * 6,
                env={**os.environ, "PYTHONPATH": td})
            v = {1: "differs", 0: "same"}.get(p.returncode, "error")
            out = (p.stdout + p.stderr).strip()
        except subprocess.TimeoutExpired:
            v, out = "timeout", ""
        return {"verdict": v, "seconds": round(time.perf_counter() - t0, 2),
                "output": out[:300]}


def plain_baselines(orig, ref, arity: int) -> dict:
    """The same four baselines, in ordinary Python semantics."""
    import random
    from hypothesis import given, settings, strategies as st, HealthCheck, seed
    lo, hi = -(1 << 15), (1 << 15) - 1          # a plausible test range

    def diff(vectors):
        for vec in vectors:
            try: a = orig(*vec)
            except Exception: a = ("raised",)
            try: b = ref(*vec)
            except Exception: b = ("raised",)
            if a != b: return list(vec)
        return None

    rng = random.Random(20260829)
    r200 = diff([tuple(rng.randint(lo, hi) for _ in range(arity)) for _ in range(200)])
    rng = random.Random(20260829)
    r20 = diff([tuple(rng.randint(lo, hi) for _ in range(arity)) for _ in range(20)])
    edge = diff(B._cartesian(B._edge_values(16), arity, 20000))

    found = []
    ints = st.integers(min_value=lo, max_value=hi)

    @seed(20260829)
    @settings(max_examples=1000, deadline=None, database=None,
              suppress_health_check=list(HealthCheck))
    @given(st.tuples(*[ints] * arity))
    def prop(vec):
        try: a = orig(*vec)
        except Exception: a = ("raised",)
        try: b = ref(*vec)
        except Exception: b = ("raised",)
        if a != b: found.append(list(vec))
        assert a == b
    try: prop()
    except AssertionError: pass
    return {"random200": r200, "random20": r20, "edge": edge,
            "hypothesis": found[-1] if found else None}


def main() -> int:
    originals = {f.__name__: f for f in CORPUS}
    prior = {(r["function"], r["pass"]): r
             for r in (json.loads(l) for l in open(HERE / "results.jsonl"))
             if not r.get("missing")}
    jobs = []
    for path in sorted((HERE / "refactors").glob("*.py")):
        spec = importlib.util.spec_from_file_location(f"p_{path.stem}", path)
        mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
        for name, orig in originals.items():
            ref = getattr(mod, name, None)
            if ref is None: continue
            rec = prior.get((name, path.stem))
            if rec is None or rec["unchanged"]: continue
            jobs.append((name, path.stem, orig, ref))
    print(f"c {len(jobs)} substantively changed pairs")

    out = HERE / "results_phase2.jsonl"
    done = 0
    with out.open("w") as fh, cf.ThreadPoolExecutor(max_workers=8) as ex:
        futs = {}
        for name, ps, orig, ref in jobs:
            futs[ex.submit(crosshair, orig, ref, True)] = (name, ps, "wrapped", orig, ref)
            futs[ex.submit(crosshair, orig, ref, False)] = (name, ps, "plain", orig, ref)
        acc: dict = {}
        for fut in cf.as_completed(futs):
            name, ps, cond, orig, ref = futs[fut]
            acc.setdefault((name, ps), {"function": name, "pass": ps})
            acc[(name, ps)][f"crosshair_{cond}"] = fut.result()
            done += 1
            if done % 40 == 0: print(f"  crosshair {done}/{len(futs)}")
        for (name, ps), rec in acc.items():
            orig = originals[name]
            ref = next(r for n, p, o, r in jobs if n == name and p == ps)
            rec["python_baselines"] = plain_baselines(
                orig, ref, len(inspect.signature(orig).parameters))
            fh.write(json.dumps(rec) + "\n")
    print(f"c -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
