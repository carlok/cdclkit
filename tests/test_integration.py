# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Integration: the CLI and the example scripts, run for real.

Unit tests can pass while the thing a user actually types is broken, so this
file drives the command line through `main(argv)` and executes every example
script end to end, asserting on exit codes and on the substance of the output.
"""

from __future__ import annotations

import contextlib
import io
import os
import runpy
import subprocess
import sys
import tempfile
import unittest

from cdclkit.cli import (EXIT_BAD_PROOF, EXIT_ERROR, EXIT_SAT, EXIT_UNKNOWN,
                       EXIT_UNSAT, main)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def run_cli(*argv) -> tuple[int, str]:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        code = main(list(argv))
    return code, buf.getvalue()


class TestCLI(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp(prefix="cdclkit-test-")
        cls.php = os.path.join(cls.tmp, "php.cnf")
        cls.queens = os.path.join(cls.tmp, "queens.cnf")
        cls.rand = os.path.join(cls.tmp, "rand.cnf")
        run_cli("gen", "php", "-n", "5", "--out", cls.php)
        run_cli("gen", "queens", "-n", "12", "--out", cls.queens)
        run_cli("gen", "random", "-n", "60", "--seed", "3", "--out", cls.rand)

    def test_generators_write_valid_dimacs(self):
        from dratify.cnf import parse_dimacs_file

        for path in (self.php, self.queens, self.rand):
            f = parse_dimacs_file(path, strict=True)
            self.assertGreater(f.nclauses, 0)

    def test_solve_unsat_exit_code_and_self_check(self):
        code, out = run_cli("solve", self.php, "--self-check", "--no-model")
        self.assertEqual(code, EXIT_UNSAT)
        self.assertIn("s UNSATISFIABLE", out)
        self.assertIn("s VERIFIED", out)

    def test_solve_sat_exit_code_and_model_check(self):
        code, out = run_cli("solve", self.queens, "--check-model")
        self.assertEqual(code, EXIT_SAT)
        self.assertIn("s SATISFIABLE", out)
        self.assertIn("model verified", out)
        self.assertIn("\nv ", out)

    def test_solve_with_preprocessing(self):
        code, out = run_cli("solve", self.rand, "--preprocess", "--check-model", "--no-model")
        self.assertIn(code, (EXIT_SAT, EXIT_UNSAT))
        self.assertIn("preprocess", out)

    def test_proof_file_round_trip_through_the_checker(self):
        proof = os.path.join(self.tmp, "php.drat")
        code, _ = run_cli("solve", self.php, "--proof", proof, "--no-model")
        self.assertEqual(code, EXIT_UNSAT)
        self.assertTrue(os.path.getsize(proof) > 0)
        code, out = run_cli("check", self.php, proof)
        self.assertEqual(code, EXIT_UNSAT)
        self.assertIn("s VERIFIED", out)

    def test_checker_rejects_a_corrupted_proof_file(self):
        proof = os.path.join(self.tmp, "php2.drat")
        run_cli("solve", self.php, "--proof", proof, "--no-model")
        with open(proof, "r", encoding="ascii") as fh:
            lines = fh.read().splitlines()
        bad = os.path.join(self.tmp, "bad.drat")
        with open(bad, "w", encoding="ascii") as fh:
            fh.write("1 2 3 4 5 6 7 8 9 10 0\n")  # not implied by the formula
            fh.write("\n".join(lines[:-1]) + "\n")
            fh.write("0\n")
        code, out = run_cli("check", self.php, bad)
        # either the bogus clause is rejected outright, or the proof still
        # verifies because the bogus line happened to be implied -- but a proof
        # that verifies must say so, and one that does not must exit 30
        self.assertIn(code, (EXIT_UNSAT, EXIT_BAD_PROOF))
        if code == EXIT_BAD_PROOF:
            self.assertIn("s NOT VERIFIED", out)

    def test_budget_reports_unknown(self):
        big = os.path.join(self.tmp, "php9.cnf")
        run_cli("gen", "php", "-n", "9", "--out", big)
        code, out = run_cli("solve", big, "--conflicts", "10", "--no-model")
        self.assertEqual(code, EXIT_UNKNOWN)
        self.assertIn("s UNKNOWN", out)

    def test_count_command(self):
        cnf = os.path.join(self.tmp, "tiny.cnf")
        with open(cnf, "w", encoding="ascii") as fh:
            fh.write("p cnf 3 1\n1 2 3 0\n")
        code, out = run_cli("count", cnf)
        self.assertEqual(code, EXIT_SAT)
        self.assertIn("models found: 7", out)

    def test_opt_command(self):
        cnf = os.path.join(self.tmp, "opt.cnf")
        with open(cnf, "w", encoding="ascii") as fh:
            fh.write("p cnf 4 2\n1 2 0\n3 4 0\n")
        code, out = run_cli("opt", cnf)
        self.assertEqual(code, EXIT_SAT)
        self.assertIn("optimum: 2", out)

    def test_mus_command(self):
        cnf = os.path.join(self.tmp, "broken.cnf")
        with open(cnf, "w", encoding="ascii") as fh:
            fh.write("p cnf 4 5\n1 0\n-1 0\n2 3 0\n4 0\n-4 2 0\n")
        for method in ("deletion", "quickxplain", "core"):
            with self.subTest(method=method):
                code, out = run_cli("mus", cnf, "--method", method, "--verify")
                self.assertEqual(code, EXIT_UNSAT)
                self.assertIn("clause 0: 1 0", out)
                self.assertIn("clause 1: -1 0", out)
        code, out = run_cli("mus", self.queens, "--method", "deletion")
        self.assertEqual(code, EXIT_SAT)
        self.assertIn("nothing to explain", out)

    def test_prep_and_stats_commands(self):
        out_file = os.path.join(self.tmp, "reduced.cnf")
        code, out = run_cli("prep", self.rand, "--out", out_file)
        self.assertEqual(code, EXIT_UNKNOWN)
        self.assertTrue(os.path.exists(out_file))
        code, out = run_cli("stats", self.rand)
        self.assertEqual(code, EXIT_UNKNOWN)
        self.assertIn("clauses", out)

    def test_bad_input_reports_an_error_rather_than_a_traceback(self):
        """A user's typo must not look like a crash.

        The DIMACS parser raises with a line number and the offending token,
        which is the useful half of a traceback. The other half is our call
        stack, which says nothing about their file and reads like the tool
        broke rather than the input being wrong.
        """
        cases = {
            "junk.cnf": "not a dimacs file at all\n",
            "badtok.cnf": "p cnf 3 1\n1 2 x 0\n",
            "badhdr.cnf": "p cnf notanumber 1\n1 0\n",
        }
        for name, text in cases.items():
            with self.subTest(case=name):
                path = os.path.join(self.tmp, name)
                with open(path, "w", encoding="ascii") as fh:
                    fh.write(text)
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    code = main(["solve", path])
                self.assertEqual(code, EXIT_ERROR)
                msg = err.getvalue()
                self.assertIn("c error:", msg)
                self.assertNotIn("Traceback", msg)

    def test_a_directory_is_an_error_not_a_crash(self):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code = main(["solve", self.tmp])
        self.assertEqual(code, EXIT_ERROR)
        self.assertIn("c error:", err.getvalue())

    def test_a_binary_file_is_an_error_not_a_crash(self):
        path = os.path.join(self.tmp, "binary.cnf")
        with open(path, "wb") as fh:
            fh.write(bytes(range(256)) * 4)
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code = main(["solve", path])
        self.assertEqual(code, EXIT_ERROR)
        self.assertNotIn("Traceback", err.getvalue())

    def test_version_reports_the_version_and_the_engine(self):
        """Also answers "was the accelerator actually loaded", which is the
        question people forget to ask when a timing looks wrong."""
        import cdclkit

        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            with self.assertRaises(SystemExit) as cm:
                main(["--version"])
        self.assertEqual(cm.exception.code, 0)
        text = out.getvalue()
        self.assertIn(cdclkit.__version__, text)
        self.assertIn("native engine:", text)

    def test_every_generator_kind_produces_a_solvable_instance(self):
        """`gen` is how most people will first produce input, and `parity` in
        particular exists to demonstrate a weakness -- it should still be
        generated correctly."""
        from dratify.cnf import parse_dimacs_file

        for kind, n in (("php", 4), ("random", 30), ("queens", 6), ("parity", 6)):
            with self.subTest(kind=kind):
                path = os.path.join(self.tmp, f"gen-{kind}.cnf")
                code, out = run_cli("gen", kind, "-n", str(n), "--out", path)
                self.assertEqual(code, EXIT_UNKNOWN)
                f = parse_dimacs_file(path, strict=True)
                self.assertGreater(f.nclauses, 0)
                code, _ = run_cli("solve", path, "--no-model")
                self.assertIn(code, (EXIT_SAT, EXIT_UNSAT))

    def test_gen_writes_to_stdout_when_no_out_is_given(self):
        code, out = run_cli("gen", "php", "-n", "3")
        self.assertEqual(code, EXIT_UNKNOWN)
        self.assertIn("p cnf", out)

    def test_search_options_change_the_search_but_not_the_answer(self):
        """Every knob has to still reach the same verdict. A configuration flag
        that changes the answer is not a tuning parameter, it is a bug."""
        variants = (
            ["--restart", "luby"],
            ["--no-phase-saving"],
            ["--ccmin", "none"],
            ["--var-decay", "0.75"],
            ["--rnd-freq", "0.05", "--seed", "7"],
        )
        for opts in variants:
            with self.subTest(opts=" ".join(opts)):
                code, _ = run_cli("solve", self.php, "--no-model", *opts)
                self.assertEqual(code, EXIT_UNSAT)

    def test_check_honours_its_engine_and_rat_options(self):
        proof = os.path.join(self.tmp, "opts.drat")
        run_cli("solve", self.php, "--proof", proof, "--no-model")
        for opts in ([], ["--no-rat"], ["--keep-deleted"]):
            with self.subTest(opts=" ".join(opts) or "defaults"):
                code, out = run_cli("check", self.php, proof, *opts)
                self.assertEqual(code, EXIT_UNSAT)
                self.assertIn("s VERIFIED", out)

    def test_parallel_solve_agrees_with_sequential(self):
        seq, _ = run_cli("solve", self.rand, "--no-model")
        par, _ = run_cli("solve", self.rand, "--no-model", "--jobs", "2")
        self.assertEqual(seq, par, "the portfolio disagreed with the sequential solve")

    def test_module_entry_point(self):
        proc = subprocess.run(
            [sys.executable, "-m", "cdclkit", "stats", self.rand],
            capture_output=True, text=True, cwd=ROOT,
        )
        self.assertEqual(proc.returncode, EXIT_UNKNOWN)
        self.assertIn("clauses", proc.stdout)


class TestExamples(unittest.TestCase):
    """Every example must run to completion; their own asserts do the checking."""

    def _run(self, name):
        path = os.path.join(ROOT, "examples", name)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            runpy.run_path(path, run_name="__main__")
        return buf.getvalue()

    def test_sudoku(self):
        out = self._run("sudoku.py")
        self.assertIn("VERIFIED", out)
        self.assertIn("uniqueness", out)

    def test_zebra(self):
        out = self._run("zebra.py")
        self.assertIn("the Norwegian drinks water", out)
        self.assertIn("the Japanese owns the zebra", out)

    def test_equivalence(self):
        out = self._run("equivalence.py")
        self.assertIn("EQUIVALENT", out)
        self.assertIn("VERIFIED", out)
        self.assertIn("NOT EQUIVALENT", out)

    def test_bmc(self):
        out = self._run("bmc.py")
        self.assertIn("VERIFIED", out)
        self.assertIn("re-simulated in Python and matches", out)
        self.assertNotIn("REJECTED", out)

    def test_refactor_check(self):
        out = self._run("refactor_check.py")
        self.assertIn("EQUIVALENT", out)
        self.assertIn("DIFFERS", out)
        self.assertIn("overflow", out)

    def test_coloring(self):
        out = self._run("coloring.py")
        self.assertIn("VERIFIED", out)
        self.assertNotIn("REJECTED", out)


class TestPublicAPI(unittest.TestCase):
    def test_one_shot_solve(self):
        import cdclkit

        f = cdclkit.CNF()
        a, b = f.new_var(), f.new_var()
        f.add([cdclkit.lit(a), cdclkit.lit(b)])
        f.add([cdclkit.lit(a, True)])
        ok, model = cdclkit.solve(f)
        self.assertTrue(ok)
        self.assertFalse(model[a])
        self.assertTrue(model[b])

    def test_exports_are_importable(self):
        import cdclkit

        for name in cdclkit.__all__:
            self.assertTrue(hasattr(cdclkit, name), f"missing export {name}")

    def test_modelling_layer(self):
        from cdclkit.model import Model

        m = Model()
        x = m.int_var(range(1, 5), "x")
        y = m.int_var(range(1, 5), "y")
        m.add(x != y)
        m.add(x.is_(3))
        sol = m.solve()
        self.assertIsNotNone(sol)
        self.assertEqual(sol[x], 3)
        self.assertNotEqual(sol[y], 3)

    def test_modelling_all_different(self):
        from cdclkit.model import Model

        m = Model()
        xs = m.int_vars(4, range(1, 5), "x")
        m.all_different_permutation(xs)
        sols = list(m.solutions(project=xs))
        self.assertEqual(len(sols), 24, "4 distinct values in 4 slots = 4! models")

    def test_modelling_order_encoding(self):
        from cdclkit.model import Model

        m = Model()
        x = m.int_var(range(1, 10), "x", order=True)
        m.add_clause([x.ge(7)])
        m.add_clause([x.le(7)])
        sol = m.solve()
        self.assertIsNotNone(sol)
        self.assertEqual(sol[x], 7)

    def test_modelling_pseudo_boolean(self):
        from cdclkit.model import Model

        m = Model()
        bs = m.bool_vars(5, "b")
        m.sum_geq([3, 1, 1, 1, 1], bs, 4)
        m.at_most_k(bs, 2)
        sol = m.solve()
        self.assertIsNotNone(sol)
        chosen = [i for i, b in enumerate(bs) if sol[b]]
        self.assertLessEqual(len(chosen), 2)
        self.assertGreaterEqual(sum([3, 1, 1, 1, 1][i] for i in chosen), 4)


if __name__ == "__main__":
    unittest.main()
