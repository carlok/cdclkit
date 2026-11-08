# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Every finding has a place, and a fixed one that comes back fails its generator.

Run from the repository root: python -m unittest campaign.test_status
"""

from __future__ import annotations

import contextlib
import io
import pathlib
import unittest
from unittest import mock

from campaign import status

FINDINGS = pathlib.Path(__file__).parent / "findings"


class TestEveryFindingIsPlaced(unittest.TestCase):
    def test_each_file_is_fixed_or_open_and_not_both(self):
        names = {p.stem for p in FINDINGS.glob("*-*.md")}
        self.assertTrue(names)
        self.assertEqual(names, status.FIXED | status.OPEN)
        self.assertFalse(status.FIXED & status.OPEN)

    def test_an_unplaced_finding_is_an_error(self):
        with self.assertRaises(KeyError):
            status.state("encodings-99")

    def test_status_md_names_each_one(self):
        text = (FINDINGS / "STATUS.md").read_text()
        for name in status.FIXED | status.OPEN:
            self.assertIn(f"| {name} |", text)


class TestARegressionFailsTheRun(unittest.TestCase):
    """Each generator's main, handed a run holding one mismatch of a fixed finding
    and one of an open one where it has any. The real run is minutes long, and the
    labelling is what is under test here."""

    def _run(self, main, argv=()):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = main(list(argv))
        return code, out.getvalue()

    def test_preprocess(self):
        from campaign import gen_preprocess as g

        def campaign(label):
            rep = g.Report()
            rep.mismatches[label] += 1
            rep.examples[label] = (1, [[1]], {}, "stub")
            return lambda seed, instances: (rep, [])

        with mock.patch.object(g, "campaign", campaign("cli-model-wrong")):
            code, out = self._run(g.main)
        self.assertEqual(code, 1, out)
        self.assertIn("REGRESSION", out)
        with mock.patch.object(g, "campaign", campaign("parity-stats")):
            code, out = self._run(g.main)
        self.assertEqual(code, 0, out)
        self.assertNotIn("REGRESSION", out)
        with mock.patch.object(g, "campaign", campaign("nobody-knows")):
            code, out = self._run(g.main)
        self.assertEqual(code, 1, out)
        self.assertIn("UNEXPLAINED", out)

    def test_engines(self):
        from campaign import gen_engines as g

        def run(label):
            rep = g.Report()
            rep.mismatch(label, "stub", ())
            for k in g.REQUIRED:
                rep.count(k)
            return lambda *a, **k: rep

        argv = ["--no-write"]
        with mock.patch.object(g, "run", run("engines-5")):
            code, out = self._run(g.main, argv)
        self.assertEqual(code, 1, out)
        self.assertIn("REGRESSION engines-5", out)
        with mock.patch.object(g, "run", run("engines-2")):
            code, out = self._run(g.main, argv)
        self.assertEqual(code, 0, out)
        with mock.patch.object(g, "run", run(None)):
            code, out = self._run(g.main, argv)
        self.assertEqual(code, 1, out)
        self.assertIn("UNEXPLAINED", out)

    def test_modelling(self):
        from campaign import gen_modelling as g

        def run(feature):
            def fake(*a, **k):
                t = g.Tally()
                t.bad("stub", "stub", {feature} if feature else ())
                for c in g.REQUIRED:
                    t.step(c)
                return t
            return fake

        for feature, want in (("incremental", "REGRESSION"), (None, "UNEXPLAINED")):
            with mock.patch.object(g, "run", run(feature)), \
                    mock.patch("sys.argv", ["gen_modelling", "--no-results"]):
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    code = g.main()
            self.assertEqual(code, 1, out.getvalue())
            self.assertIn(want, out.getvalue())

    def test_encodings(self):
        from campaign import gen_encodings as g

        real = g.execute

        def execute(label):
            def fake(tasks, pool):
                counts, _, steps, instances = real([], pool)
                for c in g.required_categories(g.ALL_SECTIONS):
                    counts[c] += 1
                counts["grid.cells_visited"] = g.grid_cell_count()
                return counts, [{"kind": "stub", "label": label}], steps, instances
            return fake

        argv = ["--no-write", "--jobs", "1"]
        with mock.patch.object(g, "execute", execute("encodings-2")):
            code, out = self._run(g.main, argv)
        self.assertEqual(code, 1, out)
        self.assertIn("REGRESSION encodings-2", out)
        with mock.patch.object(g, "execute", execute(None)):
            code, out = self._run(g.main, argv)
        self.assertEqual(code, 1, out)
        self.assertIn("UNEXPLAINED", out)

    def test_mus(self):
        from campaign import gen_mus as g

        real = g.run_all

        def fake(*a, **k):
            run = real(a[0], a[1], 1, 0)
            run.bad("stub", [], "stub", "mus-1")
            return run

        with mock.patch.object(g, "run_all", fake):
            code, out = self._run(g.main, ["--instances", "1", "--hard", "0"])
        self.assertEqual(code, 1, out)
        self.assertIn("REGRESSION mus-1", out)


if __name__ == "__main__":
    unittest.main()
