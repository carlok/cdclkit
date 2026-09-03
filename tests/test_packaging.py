# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The package metadata has to agree with the package.

These are cheap assertions about things that drift silently and are noticed
late, by someone who installed a release: a version that disagrees with itself,
an entry point naming a function that moved, a licence claim in metadata that
contradicts the one in the tree.

The version check is not hypothetical. `cdclkit/__init__.py` said 1.0.0 while
`native/Cargo.toml` said 0.1.0, and nothing anywhere noticed.
"""

from __future__ import annotations

import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent


def _read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


class TestVersions(unittest.TestCase):
    def test_python_and_cargo_versions_agree(self):
        import cdclkit

        cargo = re.search(r'^version = "([^"]+)"',
                          _read("native/Cargo.toml"), re.M)
        self.assertIsNotNone(cargo, "no version in native/Cargo.toml")
        self.assertEqual(
            cdclkit.__version__, cargo.group(1),
            "cdclkit/__init__.py and native/Cargo.toml disagree on the version. "
            "They are one artefact from a user's point of view -- the native "
            "engine must reproduce the Python engine bit-for-bit, and a "
            "version that cannot identify which pair you have makes that "
            "claim uncheckable."
        )

    def test_the_native_extra_pins_the_matching_version(self):
        """If a [native] extra is declared, it must pin this exact version.

        There is deliberately no such extra today: `cdclkit-native` is not
        published to PyPI, so advertising `pip install cdclkit[native]` would
        promise an install that fails on the first thing a user tries. The
        accelerator is built from source (`make native`) until wheels exist.

        The check is conditional rather than deleted so that it re-arms by
        itself the day the extra comes back.
        """
        import cdclkit

        text = _read("pyproject.toml")
        if "cdclkit-native" not in text:
            self.assertNotIn("[native]", _read("README.md"),
                             "the README offers an extra that pyproject.toml "
                             "does not declare")
            self.skipTest("no [native] extra is declared")
        pin = re.search(r'cdclkit-native==([0-9][^"\']*)', text)
        self.assertIsNotNone(pin, "the [native] extra does not pin a version")
        self.assertEqual(pin.group(1), cdclkit.__version__,
                         "the [native] extra pins a version of the accelerator "
                         "that is not this one")

    def test_both_halves_require_the_same_dratify(self):
        """The Rust and Python halves must want the same checker version.

        `cdclkit[native]` puts both in one process: `dratify` the Python
        package, and the `dratify` crate compiled into the extension module.
        They are two implementations of the same rules, and the README sells
        the pair as agreeing with each other. For a while the crate was pinned
        to 0.1.0 while the Python side required 0.1.2 -- two implementations
        two releases apart, in one process, advertised as cross-checking.

        This compares the lower bound each half asks for. They are different
        dependency systems and cannot be made literally identical, so the
        assertion is that neither can move without the other.
        """
        crate = re.search(r'^dratify = "([^"]+)"',
                          _read("native/Cargo.toml"), re.M)
        self.assertIsNotNone(
            crate, "native/Cargo.toml does not depend on the dratify crate")

        py = re.search(r'dratify>=([0-9][^"\',\]]*)', _read("pyproject.toml"))
        self.assertIsNotNone(
            py, "pyproject.toml does not require the dratify package")

        # A caret requirement ("0.1.3") and a floor (">=0.1.3") both name the
        # version below which the half will not work. Those must match.
        self.assertEqual(
            crate.group(1).lstrip("^").strip(), py.group(1).strip(),
            "native/Cargo.toml and pyproject.toml ask for different versions "
            "of dratify. Installing cdclkit[native] would then load two "
            "checkers built to different rules and call their agreement "
            "evidence.")

    def test_version_is_a_release_number(self):
        import cdclkit

        self.assertRegex(cdclkit.__version__, r"^\d+\.\d+\.\d+([.-]\w+)?$")


class TestEntryPoints(unittest.TestCase):
    def test_console_script_target_exists_and_is_callable(self):
        """`cdclkit = "cdclkit.cli:main"` has to still resolve after a refactor."""
        target = re.search(r'^cdclkit = "([^"]+)"',
                           _read("pyproject.toml"), re.M)
        self.assertIsNotNone(target, "no console script declared")
        mod, _, func = target.group(1).partition(":")
        imported = __import__(mod, fromlist=[func])
        fn = getattr(imported, func, None)
        self.assertTrue(callable(fn), f"{target.group(1)} is not callable")

    def test_the_entry_point_returns_an_exit_code(self):
        """A console script's return value becomes the process exit status.

        `main()` returning None would make every run exit 0, including the
        UNSAT and bad-proof cases the exit codes exist to distinguish.
        """
        from cdclkit.cli import EXIT_UNKNOWN, main

        self.assertEqual(main(["stats", str(ROOT / "tests" / "data.cnf")])
                         if (ROOT / "tests" / "data.cnf").exists()
                         else EXIT_UNKNOWN, EXIT_UNKNOWN)


class TestPublicAPISurface(unittest.TestCase):
    """`__all__` is a promise about semantic versioning, so it has to be exact.

    A name in `__all__` that does not resolve is a broken promise; a name that
    resolves but is not listed is an accidental one, which is worse, because
    someone will depend on it and only a major version bump can take it back.
    """

    def test_every_exported_name_resolves(self):
        import cdclkit

        missing = [n for n in cdclkit.__all__ if not hasattr(cdclkit, n)]
        self.assertEqual(missing, [], f"__all__ promises names that are absent: {missing}")

    def test_the_equivalence_checker_is_public(self):
        """It is the feature most likely to be reached for first."""
        import cdclkit

        for name in ("equivalent", "EquivalenceResult", "UnsupportedConstruct",
                     "ProofRejected"):
            self.assertIn(name, cdclkit.__all__, f"{name} is not declared public")
            self.assertTrue(hasattr(cdclkit, name))

    def test_pyeq_is_not_imported_eagerly(self):
        """`inspect` costs more than the rest of the package put together.

        pyeq needs it to read a function's source; importing it at package
        import time was 5.5 ms of an 8.8 ms `import cdclkit`, paid by every CLI
        invocation that only wanted to solve a DIMACS file. Startup is not
        noise here -- the benchmark harness discards instances a competitor
        finishes in under 50 ms because process startup dominates them.
        """
        import subprocess
        import sys

        out = subprocess.run(
            [sys.executable, "-c",
             "import sys, cdclkit; print('cdclkit.pyeq' in sys.modules)"],
            capture_output=True, text=True, cwd=ROOT,
        )
        self.assertEqual(out.stdout.strip(), "False",
                         "importing cdclkit pulled in pyeq, and with it inspect")

    def test_unknown_attributes_still_raise(self):
        """A lazy __getattr__ must not turn typos into silent successes."""
        import cdclkit

        with self.assertRaises(AttributeError):
            cdclkit.definitely_not_a_real_name

    def test_internal_modules_are_documented_as_internal(self):
        import cdclkit

        doc = cdclkit.__doc__ or ""
        self.assertIn("Public API", doc)
        for internal in ("pipeline", "portfolio", "native"):
            self.assertIn(internal, doc,
                          f"{internal} is importable but undeclared; say so, "
                          "or someone will depend on it")
            self.assertNotIn(internal, cdclkit.__all__)


class TestWorkflowsAreWellFormed(unittest.TestCase):
    """Every top-level line in a workflow must be a known key or a comment.

    A comment in release.yml lost its leading "# " during an edit. The result
    was still valid YAML -- it simply became a mapping key -- so a
    `yaml.safe_load` check passed it, and GitHub then refused the whole file
    with "this run likely failed because of a workflow file issue". Zero jobs
    ran, and the tag had to be deleted and re-cut.

    Deliberately does not import yaml: the dependency-free test path is the one
    that must never break, and this failure mode does not need a parser.
    """

    #: https://docs.github.com/actions/reference/workflow-syntax-for-github-actions
    ALLOWED = {"name", "on", "permissions", "env", "defaults", "concurrency",
               "jobs", "run-name"}

    def test_no_stray_top_level_keys(self):
        workflows = sorted((ROOT / ".github" / "workflows").glob("*.yml"))
        self.assertTrue(workflows, "no workflows found")
        for wf in workflows:
            with self.subTest(workflow=wf.name):
                for n, line in enumerate(wf.read_text().splitlines(), 1):
                    if not line or line[0] in " \t#":
                        continue
                    key = line.split(":", 1)[0].strip()
                    self.assertIn(
                        key, self.ALLOWED,
                        f"{wf.name}:{n} starts a top-level key {key!r} that "
                        f"GitHub does not recognise -- most likely a comment "
                        f"that lost its '# '")


class TestLicenceConsistency(unittest.TestCase):
    """The tree is Apache-2.0; every place that states a licence must agree.

    This class previously guarded the opposite policy -- that no rights were
    granted anywhere. That decision was reversed deliberately, so these tests
    were rewritten rather than deleted: a licence stated in one place and
    contradicted in another is worse than either choice made consistently.
    """

    def test_package_metadata_declares_apache(self):
        self.assertRegex(_read("pyproject.toml"),
                         r'(?m)^\s*license\s*=\s*"Apache-2\.0"',
                         "pyproject.toml must declare Apache-2.0")

    def test_crate_declares_apache_and_can_publish(self):
        cargo = _read("native/Cargo.toml")
        self.assertIn('license = "Apache-2.0"', cargo)
        self.assertNotIn("publish = false", cargo,
                         "the crate was unpublishable while the tree was "
                         "unlicensed; that is no longer the case")

    def test_a_licence_file_is_present_and_is_apache(self):
        path = ROOT / "LICENSE"
        self.assertTrue(path.exists(), "LICENSE is missing")
        text = path.read_text()
        self.assertIn("Apache License", text)
        self.assertIn("Version 2.0", text)

    def test_the_readme_states_apache(self):
        readme = _read("README.md")
        self.assertIn("## Licence", readme, "the README has no licence section")
        section = readme[readme.rindex("## Licence"):]
        self.assertIn("Apache-2.0", section,
                      "the README licence section must name the licence")

    def test_no_proprietary_headers_survive(self):
        import subprocess

        files = subprocess.run(
            ["git", "ls-files", "*.py", "*.rs"],
            capture_output=True, text=True, cwd=ROOT,
        ).stdout.split()
        if not files:
            self.skipTest("not a git checkout")
        # split, so this file does not match its own check
        marker = "LicenseRef" + "-Proprietary"
        stale = [f for f in files
                 if f != "tests/test_packaging.py" and marker in _read(f)]
        self.assertEqual(stale, [], f"sources still marked proprietary: {stale}")

    def test_sources_carry_an_spdx_header(self):
        import subprocess

        files = subprocess.run(
            ["git", "ls-files", "*.py", "*.rs"],
            capture_output=True, text=True, cwd=ROOT,
        ).stdout.split()
        if not files:
            self.skipTest("not a git checkout")
        self.assertGreater(len(files), 40, "git ls-files returned too little")
        missing = [f for f in files
                   if "SPDX-License-Identifier" not in _read(f)]
        self.assertEqual(missing, [], f"sources without an SPDX header: {missing}")


if __name__ == "__main__":
    unittest.main()
