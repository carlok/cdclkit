# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""`cdclkit solve` must run the configuration the library documents.

`--restart` defaulted to "glucose" while `Config.restart` moved to "luby", so
every non-adaptive CLI solve ran the policy CHANGELOG.md records as *replaced* --
and the measurement quoted there (uf250 3.25 -> 1.02) did not describe what
`python3 -m cdclkit solve` actually did. The other five defaults matched, which
is exactly why the one that drifted went unnoticed.

This is the same shape as TestDefaultsAgree in test_native_solver.py, which
exists because the Python and Rust defaults drifted apart once too.
"""

from __future__ import annotations

import unittest

from cdclkit.cli import build_parser
from cdclkit.solver import Config


class TestCLIDefaultsMatchConfig(unittest.TestCase):
    #: CLI flag -> Config attribute. Anything the CLI can set that Config also
    #: has belongs here; a new knob on one side without the other is the bug.
    PAIRS = {
        "restart": "restart",
        "var_decay": "var_decay",
        "ccmin": "ccmin",
        "rnd_freq": "rnd_freq",
        "seed": "rnd_seed",
    }

    def setUp(self):
        self.args = build_parser().parse_args(["solve", "/dev/null"])
        self.cfg = Config()

    def test_every_shared_default_agrees(self):
        for flag, attr in self.PAIRS.items():
            with self.subTest(flag=flag):
                self.assertEqual(
                    getattr(self.args, flag), getattr(self.cfg, attr),
                    f"--{flag.replace('_', '-')} defaults to "
                    f"{getattr(self.args, flag)!r} but Config.{attr} is "
                    f"{getattr(self.cfg, attr)!r}; the CLI would run a "
                    f"different solver than the library")

    def test_phase_saving_is_expressed_as_a_negation(self):
        """--no-phase-saving only makes sense while the default is on."""
        self.assertTrue(self.cfg.phase_saving)
        self.assertFalse(self.args.no_phase_saving)

    def test_the_config_the_cli_builds_equals_the_library_default(self):
        """The end-to-end property: a bare `solve` is a default Config."""
        built = Config(
            restart=self.args.restart,
            var_decay=self.args.var_decay,
            ccmin=self.args.ccmin,
            phase_saving=not self.args.no_phase_saving,
            rnd_freq=self.args.rnd_freq,
            rnd_seed=self.args.seed,
        )
        self.assertEqual(built.as_dict(), self.cfg.as_dict())


if __name__ == "__main__":
    unittest.main()
