# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""`--adaptive` must honour the flags it accepts.

`cdclkit solve f.cnf --adaptive --self-check` used to print `s UNSATISFIABLE`,
exit 20, and check nothing: the branch built a Config, a proof sink and a
conflict budget and passed none of them to the pipeline. `--check-model` *was*
handled, which is what made it read as deliberate rather than broken.

That matters more than an ordinary flag bug because README and SECURITY.md both
rest on `--self-check` meaning something.

The subtlety is preprocessing. It rewrites the formula -- bounded variable
elimination adds clauses that do not follow from the input -- so a refutation of
the reduced formula is not a refutation of what the user handed in. The
preprocessor logs its steps ahead of the search's, and the combined proof is
checked against the **original**. These tests assert that, not merely that a
proof exists.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import pathlib
import unittest

import dratify
from dratify.cnf import CNF

from cdclkit import MemoryProof, parse_dimacs
from cdclkit.pipeline import solve_adaptive
from cdclkit.solver import Solver
from cdclkit import native
from tests.util import fuzz_seed

PHP = """p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0
"""


#: n=60 at ratio 5.2 is unsatisfiable and, unlike a sparser instance, gives
#: bounded variable elimination something to remove -- which is the case that
#: matters here, because BVE is what makes a proof of the *reduced* formula
#: insufficient.
_N, _RATIO, _SEED = 60, 5.2, 7


def _harder_unsat(seed=_SEED):
    import random

    rng = random.Random(seed)
    f = CNF()
    f.new_vars(_N)
    for _ in range(int(_N * _RATIO)):
        vs = rng.sample(range(1, _N + 1), 3)
        f.add_dimacs([v if rng.random() < 0.5 else -v for v in vs])
    return f


def _hard_php():
    """A pigeonhole big enough that neither preprocessing nor luck solves it."""
    from cdclkit.cli import gen_php

    return gen_php(8, 7).to_dimacs()


class TestAdaptiveEmitsACheckableProof(unittest.TestCase):
    def _run(self, formula, engine, **kw):
        original = formula.copy()
        proof = MemoryProof()
        r = solve_adaptive(formula, engine=engine, proof=proof, **kw)
        return original, proof, r

    def test_the_proof_checks_against_the_original_not_the_reduced_formula(self):
        for engine in ("python", "native"):
            if engine == "native" and not native.available():
                continue
            with self.subTest(engine=engine):
                original, proof, r = self._run(
                    _harder_unsat(), engine, always_preprocess=True)
                self.assertIs(r.sat, False)
                self.assertTrue(r.preprocessed, "the test needs preprocessing "
                                                "to have actually run")
                self.assertLess(r.clauses_after, r.clauses_before)
                chk = dratify.check_proof(original, proof)
                self.assertTrue(chk.ok, chk.reason)
                self.assertTrue(chk.reached_empty)

    def test_it_works_without_preprocessing_too(self):
        original, proof, r = self._run(parse_dimacs(PHP), "python",
                                       never_preprocess=True)
        self.assertIs(r.sat, False)
        self.assertTrue(dratify.check_proof(original, proof).ok)

    def test_a_satisfiable_instance_emits_no_refutation(self):
        f = parse_dimacs("p cnf 2 1\n1 2 0\n")
        proof = MemoryProof()
        r = solve_adaptive(f, engine="python", proof=proof)
        self.assertIs(r.sat, True)

    def test_a_proof_from_a_parallel_portfolio_is_refused(self):
        """Workers race, so their steps would interleave into a stream that
        justifies nothing. Refusing beats emitting a proof that will not check.
        """
        with self.assertRaises(ValueError) as cm:
            solve_adaptive(parse_dimacs(PHP), engine="python",
                           jobs=2, proof=MemoryProof())
        self.assertIn("interleave", str(cm.exception))


class TestAdaptiveCLI(unittest.TestCase):
    """End to end, because the bug was in the wiring rather than the pipeline."""

    def _cli(self, *args, engine=None):
        root = pathlib.Path(__file__).resolve().parent.parent
        import os

        env = dict(os.environ)
        env.pop("CDCLKIT_ENGINE", None)
        if engine is not None:
            env["CDCLKIT_ENGINE"] = engine
        # prepend, do not replace: a pure-Python checkout finds dratify on the
        # inherited path, and clobbering it made these fail for the wrong reason
        env["PYTHONPATH"] = os.pathsep.join(
            [str(root)] + ([env["PYTHONPATH"]] if env.get("PYTHONPATH") else []))
        return subprocess.run(
            [sys.executable, "-m", "cdclkit", *args],
            capture_output=True, text=True, cwd=root, env=env)

    def test_adaptive_self_check_actually_checks(self):
        with tempfile.TemporaryDirectory() as d:
            cnf = pathlib.Path(d) / "php.cnf"
            cnf.write_text(PHP)
            r = self._cli("solve", str(cnf), "--adaptive", "--self-check")
        self.assertEqual(r.returncode, 20, r.stdout + r.stderr)
        self.assertIn("s VERIFIED", r.stdout,
                      "--adaptive --self-check printed a verdict without "
                      "checking a proof")

    def test_adaptive_writes_a_proof_file(self):
        with tempfile.TemporaryDirectory() as d:
            cnf = pathlib.Path(d) / "php.cnf"
            cnf.write_text(PHP)
            out = pathlib.Path(d) / "p.drat"
            r = self._cli("solve", str(cnf), "--adaptive", "--proof", str(out))
            self.assertEqual(r.returncode, 20, r.stdout + r.stderr)
            self.assertTrue(out.exists(), "--adaptive --proof wrote nothing")
            text = out.read_text()
        self.assertTrue(dratify.check_proof(parse_dimacs(PHP), text).ok)

    def test_adaptive_with_a_portfolio_and_a_proof_is_refused_not_ignored(self):
        with tempfile.TemporaryDirectory() as d:
            cnf = pathlib.Path(d) / "php.cnf"
            cnf.write_text(PHP)
            r = self._cli("solve", str(cnf), "--adaptive", "--self-check",
                          "-j", "2")
        self.assertEqual(r.returncode, 1)
        self.assertIn("interleave", r.stdout)

    # AGENTS.md said CDCLKIT_ENGINE selected the engine. Nothing read it, and
    # `--adaptive` picked native on its own whenever it was installed.

    def _php(self, engine=None):
        with tempfile.TemporaryDirectory() as d:
            cnf = pathlib.Path(d) / "php.cnf"
            cnf.write_text(PHP)
            return self._cli("solve", str(cnf), "--adaptive", engine=engine)

    def test_adaptive_uses_native_when_installed(self):
        r = self._php()
        self.assertEqual(r.returncode, 20, r.stdout + r.stderr)
        want = "native" if native.available() else "python"
        self.assertIn(f"c engine: {want}", r.stdout)

    def test_cdclkit_engine_python_overrides_adaptive(self):
        r = self._php(engine="python")
        self.assertEqual(r.returncode, 20, r.stdout + r.stderr)
        self.assertIn("c engine: python", r.stdout)

    def test_cdclkit_engine_native_without_the_build_is_an_error(self):
        if native.available():
            self.skipTest("native engine is built here")
        r = self._php(engine="native")
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("CDCLKIT_ENGINE=native", r.stderr)
        self.assertNotIn("Traceback", r.stderr)

    def test_portfolio_honours_cdclkit_engine_too(self):
        with tempfile.TemporaryDirectory() as d:
            cnf = pathlib.Path(d) / "php.cnf"
            cnf.write_text(PHP)
            r = self._cli("solve", str(cnf), "-j", "2", engine="python")
        self.assertEqual(r.returncode, 20, r.stdout + r.stderr)
        self.assertIn("c engine: python", r.stdout)

    def test_unknown_cdclkit_engine_is_an_error(self):
        r = self._php(engine="quantum")
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("unknown CDCLKIT_ENGINE", r.stderr)


class TestConflictBudgetEverywhere(unittest.TestCase):
    """`--conflicts` reached only the plain route. CHANGELOG 0.1.3 listed it among
    the flags `--adaptive` ignored and described the fix, and it still was: a caller
    who set a budget got an unbounded run."""

    _cli = TestAdaptiveCLI._cli
    ROUTES = ((), ("--adaptive",), ("-j", "2"), ("--adaptive", "-j", "2"),
              ("--preprocess", "--adaptive"), ("--preprocess", "-j", "2"))

    def _run(self, budget, route, engine, text=None):
        with tempfile.TemporaryDirectory() as d:
            cnf = pathlib.Path(d) / "f.cnf"
            cnf.write_text(text or _hard_php())
            return self._cli("solve", str(cnf), "--conflicts", str(budget), *route,
                             engine=engine)

    def _engines(self):
        return ["python"] + (["native"] if native.available() else [])

    def test_a_budget_too_small_is_unknown_on_every_route(self):
        for engine in self._engines():
            for route in self.ROUTES:
                for budget in (0, 3):
                    with self.subTest(engine=engine, route=route, budget=budget):
                        r = self._run(budget, route, engine)
                        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                        self.assertIn("s UNKNOWN", r.stdout)
                        self.assertNotIn("s UNSATISFIABLE", r.stdout)

    def test_a_budget_of_zero_is_unknown_when_preprocessing_could_answer(self):
        """The default -j runs a preprocessing worker, which refutes a small
        pigeonhole without a conflict. Whether that beat the budget would be a race
        between workers, so a budget turns that strategy off."""
        for engine in self._engines():
            with self.subTest(engine=engine):
                r = self._run(0, ("-j", "2"), engine, PHP)
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                self.assertIn("s UNKNOWN", r.stdout)

    def test_a_budget_big_enough_answers(self):
        for engine in self._engines():
            for route in self.ROUTES:
                with self.subTest(engine=engine, route=route):
                    r = self._run(10_000_000, route, engine, PHP)
                    self.assertEqual(r.returncode, 20, r.stdout + r.stderr)

    def test_a_negative_budget_is_an_error(self):
        for route in self.ROUTES:
            with self.subTest(route=route):
                r = self._run(-1, route, None)
                self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
                self.assertNotIn("Traceback", r.stderr)

    def test_the_library_takes_a_budget(self):
        from cdclkit.portfolio import solve_portfolio

        for engine in self._engines():
            with self.subTest(engine=engine):
                f = parse_dimacs(_hard_php())
                self.assertIsNone(solve_adaptive(f.copy(), engine=engine,
                                                 max_conflicts=5).sat)
                self.assertIsNone(solve_adaptive(f.copy(), engine=engine, max_conflicts=5,
                                                 never_preprocess=True).sat)
                self.assertIsNone(solve_adaptive(f.copy(), engine=engine, max_conflicts=5,
                                                 always_preprocess=True).sat)
                for jobs in (1, 2):
                    r = solve_portfolio(f.copy(), jobs=jobs, engine=engine,
                                        max_conflicts=5, preprocess_workers=0)
                    self.assertIsNone(r.sat)
                    self.assertFalse(r.finished)
                self.assertIs(solve_adaptive(parse_dimacs(PHP), engine=engine,
                                             max_conflicts=100_000).sat, False)

    def test_the_budget_covers_the_probe_too(self):
        """The limit is checked between conflicts, so a run may pass it by a few.
        It must be the same few as a plain solve with the same budget."""
        f = parse_dimacs(_hard_php())
        plain = Solver(f.nvars)
        plain.add_cnf(f)
        self.assertIsNone(plain.solve(max_conflicts=5))
        r = solve_adaptive(f, engine="python", max_conflicts=5)
        self.assertEqual(r.conflicts, plain.stats.conflicts)
        self.assertFalse(r.preprocessed, "no budget left to preprocess for")


class TestPreprocessThenSearch(unittest.TestCase):
    """`--preprocess` reduces the formula before any later route sees it, so
    every route has to reconstruct.

    `--preprocess --adaptive` returned before the only `pre.reconstruct` and
    printed `v -1` for the formula `(x1)`, exit 10. The adaptive pipeline's own
    reconstruction cannot help: it knows nothing about an outer preprocessor.
    """

    FORMULAS = [
        ("p cnf 1 1\n1 0\n", [[1]]),
        ("p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n", [[1, 2], [-1, 3], [-2, -3]]),
    ]
    ROUTES = [
        ("--preprocess",),
        ("--preprocess", "--adaptive"),
        ("--preprocess", "--adaptive", "-j", "2"),
        ("--preprocess", "--adaptive", "--self-check"),
        ("--preprocess", "--adaptive", "--check-model"),
        ("--preprocess", "--check-model"),
    ]

    _cli = TestAdaptiveCLI._cli

    def _printed_model(self, stdout):
        return {int(t) for line in stdout.splitlines() if line.startswith("v ")
                for t in line[2:].split()} - {0}

    def test_every_route_prints_a_model_of_the_input(self):
        engines = ["python"] + (["native"] if native.available() else [])
        for text, clauses in self.FORMULAS:
            for route in self.ROUTES:
                for engine in engines:
                    with self.subTest(text=text, route=route, engine=engine), \
                            tempfile.TemporaryDirectory() as d:
                        cnf = pathlib.Path(d) / "f.cnf"
                        cnf.write_text(text)
                        r = self._cli("solve", str(cnf), *route, engine=engine)
                        self.assertEqual(r.returncode, 10, r.stdout + r.stderr)
                        model = self._printed_model(r.stdout)
                        for c in clauses:
                            self.assertTrue(set(c) & model, f"{c} falsified: {r.stdout}")

    def test_self_check_refuses_a_wrong_model(self):
        """A SAT answer is the one a self-check can verify for almost nothing:
        evaluate it. --self-check used to look only at refutations."""
        import contextlib
        import io
        from unittest import mock

        from cdclkit import cli
        from cdclkit.pipeline import PipelineResult

        wrong = PipelineResult()
        wrong.sat, wrong.model = True, [False]
        with tempfile.TemporaryDirectory() as d:
            cnf = pathlib.Path(d) / "f.cnf"
            cnf.write_text("p cnf 1 1\n1 0\n")
            out = io.StringIO()
            with mock.patch("cdclkit.pipeline.solve_adaptive", return_value=wrong), \
                    contextlib.redirect_stdout(out):
                code = cli.main(["solve", str(cnf), "--adaptive", "--self-check"])
        self.assertEqual(code, 1, out.getvalue())
        self.assertIn("MODEL CHECK FAILED", out.getvalue())
        self.assertNotIn("s SATISFIABLE", out.getvalue())


if __name__ == "__main__":
    unittest.main()
