# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Post-install smoke test: run this against the *installed* package.

Deliberately not part of the unittest suite. The suite imports `cdclkit` from
the checkout, so it cannot tell you whether the wheel contains every module,
whether the entry point resolves, or whether something works only because a
sibling file happened to be on the path. This runs from a clean virtualenv with
no checkout anywhere near it -- see the `smoke` target in the Makefile.

Kept small on purpose. It is asking "did the artefact arrive intact", not
"is the solver correct"; the suite already answers the second.
"""

from __future__ import annotations

import sys


def _fail(msg: str) -> None:
    print(f"c SMOKE FAILED: {msg}")
    sys.exit(1)


def slow(a, b):
    return a * 2 + b * 2


def fast(a, b):
    return (a + b) << 1


def main() -> int:
    import cdclkit

    # Every public name must actually be importable from the installed
    # package. A wheel missing a module fails here rather than in a user's
    # first session.
    for name in cdclkit.__all__:
        if not hasattr(cdclkit, name):
            _fail(f"cdclkit.__all__ promises {name!r} and the install lacks it")

    for mod in ("cli", "cnf", "solver", "proof", "encodings", "preprocess",
                "mus", "model", "brute", "heap", "lits", "pipeline",
                "portfolio", "native", "pyeq"):
        try:
            __import__(f"cdclkit.{mod}")
        except ImportError as e:
            _fail(f"cdclkit.{mod} is missing from the wheel: {e}")

    # solve / prove / check, end to end
    f = cdclkit.CNF()
    a, b = f.new_var(), f.new_var()
    f.add([cdclkit.lit(a), cdclkit.lit(b)])
    f.add([cdclkit.lit(a, True)])
    ok, model = cdclkit.solve(f)
    if not ok or model[a] or not model[b]:
        _fail(f"a two-clause formula solved wrong: ok={ok} model={model}")

    proof = cdclkit.MemoryProof()
    g = cdclkit.CNF()
    v = g.new_var()
    g.add([cdclkit.lit(v)])
    g.add([cdclkit.lit(v, True)])
    s = cdclkit.Solver(g.nvars, proof=proof)
    if s.add_cnf(g) and s.solve():
        _fail("a contradictory formula was reported satisfiable")
    if not cdclkit.check_proof(g, proof).ok:
        _fail("the installed checker rejected a proof from the installed solver")

    # the equivalence checker, including its proof
    from cdclkit.pyeq import equivalent

    r = equivalent(slow, fast, widths={"a": 6, "b": 6})
    if r.proved is not True:
        _fail(f"a known-equivalent pair was not proved: {r.report()}")
    if not r.proof_checked or r.proof_steps <= 0:
        _fail("proved=True arrived without a checked proof behind it")

    from cdclkit import native as native_mod

    print(f"c cdclkit {cdclkit.__version__} installed and working "
          f"(native engine: {'yes' if native_mod.available() else 'no'})")
    print(f"c   pyeq: {r.report()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
