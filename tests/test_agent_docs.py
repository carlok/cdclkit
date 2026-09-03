# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""`AGENTS.md` has to agree with the code it describes.

`AGENTS.md` is the first thing an LLM agent reads about this package, so an
error in it does not stay in it -- it is copied into generated code, and the
reader has no reason to doubt a file whose whole purpose is to list the
mistakes people make. That makes it worth a drift guard, the same way
`tests/test_cli_defaults.py` guards the CLI against `Config`.

Both facts checked here were wrong when this file was written: the exit-code
section omitted `0` while asserting that exit codes are never `0`, and the
literal-encoding section -- under the heading "the single most common error" --
stated the doubled-index formula against DIMACS 1-based variable numbers.
"""

from __future__ import annotations

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
AGENTS = (ROOT / "AGENTS.md").read_text(encoding="utf-8")


class TestExitCodes(unittest.TestCase):
    def test_every_exit_code_the_cli_can_return_is_documented(self):
        from cdclkit import cli

        constants = {name: getattr(cli, name) for name in dir(cli)
                     if name.startswith("EXIT_")}
        self.assertTrue(constants, "no EXIT_ constants found in cdclkit.cli")

        section = AGENTS[AGENTS.index("## CLI exit codes"):]
        section = section[:section.index("\n## ", 3)]
        documented = {int(n) for n in re.findall(r"`(\d+)`", section)}

        missing = sorted(set(constants.values()) - documented)
        self.assertFalse(
            missing,
            f"AGENTS.md does not document exit code(s) {missing}. The CLI can "
            f"return them ({constants}), so an agent writing a shell wrapper "
            f"from this file would mishandle them.")

    def test_the_section_does_not_claim_zero_is_never_returned(self):
        """`EXIT_UNKNOWN` is 0, so 'exit codes are not 0' is false."""
        from cdclkit import cli

        heading = next(ln for ln in AGENTS.splitlines()
                       if ln.startswith("## ") and "exit code" in ln.lower())
        if cli.EXIT_UNKNOWN != 0:
            self.skipTest("the CLI no longer returns 0")
        self.assertNotIn(
            "not 0", heading,
            f"{heading!r} contradicts cli.EXIT_UNKNOWN == 0, which is "
            f"returned whenever a conflict budget runs out.")


class TestLiteralEncoding(unittest.TestCase):
    def test_the_documented_formula_matches_from_dimacs(self):
        """AGENTS.md's `2v` / `2v + 1` must say which `v` it means.

        The encoding is over the *internal* 0-based variable index. DIMACS
        variable 1 is internal variable 0, so its positive literal is 0, not 2.
        Stating the formula beside "DIMACS uses signed integers" without
        introducing the 0-based index invites exactly the off-by-one the
        section warns about.
        """
        from dratify.lits import from_dimacs

        self.assertEqual(from_dimacs(1), 0)
        self.assertEqual(from_dimacs(-1), 1)
        self.assertEqual(from_dimacs(3), 4)

        section = AGENTS[AGENTS.index("## Internal literals"):]
        section = section[:section.index("\n## ", 3)]
        self.assertRegex(
            section, r"0-based",
            "the literal-encoding section gives the doubled-index formula but "
            "never says the variable in it is the 0-based internal index, so "
            "`2v` reads as applying to the DIMACS number.")


if __name__ == "__main__":
    unittest.main()
