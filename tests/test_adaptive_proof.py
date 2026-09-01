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

    def _cli(self, *args):
        root = pathlib.Path(__file__).resolve().parent.parent
        import os

        env = dict(os.environ)
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


if __name__ == "__main__":
    unittest.main()
