# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Every Python example in the README has to run, and print what it says.

The README is the first code a visitor copies, and until this test existed
nothing executed it. The sibling project found its own example broken this
way: fine on the input its author tried, and failing on the first line for
the most common input there is.

Each ```python block runs in a fresh namespace from a temporary directory. A
`print(x)  # value` line is an assertion: the printed value must match the
first word of the comment, so an example that runs but answers wrongly fails
too. A block preceded by `<!-- readme-test: skip ... -->` is not executed.
"""

from __future__ import annotations

import contextlib
import io
import os
import pathlib
import re
import shutil
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent

SKIP = re.compile(r"<!--\s*readme-test:\s*skip")
EXPECT = re.compile(r"^\s*print\(.*\)\s*#\s*(\S+)")


def blocks(markdown: str) -> list[tuple[int, str, bool]]:
    """(line number, source, skipped) for every ```python block."""
    lines = markdown.splitlines()
    out, i = [], 0
    while i < len(lines):
        if lines[i].strip() == "```python":
            start = i + 1
            skipped = i > 0 and bool(SKIP.search(lines[i - 1]))
            j = start
            while lines[j].strip() != "```":
                j += 1
            out.append((start + 1, "\n".join(lines[start:j]) + "\n", skipped))
            i = j
        i += 1
    return out


def expected_output(source: str) -> list[str]:
    return [m.group(1) for ln in source.splitlines()
            if (m := EXPECT.match(ln))]


class TestReadmeExamples(unittest.TestCase):
    def setUp(self):
        self.dir = pathlib.Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.dir)
        self.all = blocks((ROOT / "README.md").read_text(encoding="utf-8"))

    def test_the_readme_has_examples_to_test(self):
        """Guards the extractor: a regex that matches nothing passes everything."""
        self.assertGreaterEqual(len(self.all), 1)

    def test_every_example_runs_and_prints_what_it_promises(self):
        ran = 0
        for lineno, source, skipped in self.all:
            if skipped:
                continue
            with self.subTest(line=lineno):
                want = expected_output(source)
                out = io.StringIO()
                here = os.getcwd()
                os.chdir(self.dir)
                try:
                    with contextlib.redirect_stdout(out):
                        exec(compile(source, "README.md", "exec"),
                             {"__name__": "__readme__"})
                finally:
                    os.chdir(here)
                got = out.getvalue().split()
                self.assertEqual(
                    got, want,
                    f"README.md:{lineno} printed {got}, but its comments "
                    f"promise {want}")
                ran += 1
        self.assertGreater(ran, 0, "no README example was run")


if __name__ == "__main__":
    unittest.main()
