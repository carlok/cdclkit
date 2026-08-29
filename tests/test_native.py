# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The native data layer, differentially tested against the Python reference.

Sprint 1's exit criterion is that a formula round-trips Python → native arena →
Python *identically*. Not "equivalently": the same clauses, in the same order,
with the same literals, and with the same accept/reject decision for every
clause added.

Every test here is skipped when the compiled module is absent, and the first
test asserts that absence is handled gracefully -- because the whole port
depends on the repo staying usable without a Rust toolchain.
"""

from __future__ import annotations

import itertools
import random
import unittest

from cdclkit import native
from dratify.cnf import CNF
from dratify.lits import from_dimacs, is_neg, mk_lit, neg, to_dimacs, var_of
from tests.util import random_cnf, fuzz_seed

HAVE = native.available()
requires_native = unittest.skipUnless(HAVE, "native engine not built for this interpreter")


class TestFallback(unittest.TestCase):
    """These must pass with or without the compiled module."""

    def test_probe_never_raises(self):
        self.assertIsInstance(native.available(), bool)

    def test_module_matches_availability(self):
        self.assertEqual(native.module() is not None, native.available())

    def test_require_raises_a_useful_error_when_absent(self):
        if native.available():
            self.assertIsNotNone(native.require())
        else:
            with self.assertRaises(RuntimeError) as cm:
                native.require()
            self.assertIn("maturin", str(cm.exception))

    def test_default_engine_is_python(self):
        self.assertEqual(native.engine_requested(), "python")

    def test_unknown_engine_is_rejected(self):
        import os

        previous = os.environ.get("CDCLKIT_ENGINE")
        os.environ["CDCLKIT_ENGINE"] = "quantum"
        try:
            with self.assertRaises(ValueError):
                native.engine_requested()
        finally:
            if previous is None:
                os.environ.pop("CDCLKIT_ENGINE", None)
            else:
                os.environ["CDCLKIT_ENGINE"] = previous


@requires_native
class TestLiteralEncoding(unittest.TestCase):
    """The two implementations must agree on what a literal *is*.

    This is the foundation of every later differential test: if a literal means
    a different number on each side, comparing anything downstream is
    meaningless.
    """

    def test_mk_lit_and_accessors_agree(self):
        n = native.require()
        for v in range(200):
            for negated in (False, True):
                self.assertEqual(n.mk_lit(v, negated), mk_lit(v, negated))
                l = mk_lit(v, negated)
                self.assertEqual(n.var_of(l), var_of(l))
                self.assertEqual(n.is_neg(l), is_neg(l))
                self.assertEqual(n.neg(l), neg(l))

    def test_dimacs_conversion_agrees(self):
        n = native.require()
        for d in itertools.chain(range(1, 300), range(-299, 0)):
            self.assertEqual(n.from_dimacs(d), from_dimacs(d))
        for l in range(600):
            self.assertEqual(n.to_dimacs(l), to_dimacs(l))

    def test_zero_is_rejected_by_both(self):
        n = native.require()
        with self.assertRaises(ValueError):
            from_dimacs(0)
        with self.assertRaises(ValueError):
            n.from_dimacs(0)


@requires_native
class TestArenaRoundTrip(unittest.TestCase):
    """Sprint 1's exit criterion."""

    def _load(self, f: CNF):
        n = native.require()
        db = n.ClauseDb(f.nvars)
        accepted = [db.add_clause(list(c)) for c in f.clauses]
        return db, accepted

    def test_round_trip_on_random_formulas(self):
        rng = random.Random(fuzz_seed(17))
        for _ in range(60):
            f = random_cnf(rng, max_vars=14, ratio=5.0)
            db, _ = self._load(f)
            self.assertEqual(db.num_clauses, f.nclauses)
            self.assertEqual(db.clauses(), [list(c) for c in f.clauses])
            self.assertEqual(db.num_vars, f.nvars)

    def test_normalisation_matches_python_exactly(self):
        """Tautology rejection and duplicate collapsing must agree clause by
        clause, including the boolean each `add` returns."""
        n = native.require()
        rng = random.Random(fuzz_seed(23))
        for _ in range(200):
            nvars = rng.randint(1, 6)
            raw = [mk_lit(rng.randrange(nvars), rng.random() < 0.5)
                   for _ in range(rng.randint(0, 5))]
            f = CNF(nvars)
            db = n.ClauseDb(nvars)
            self.assertEqual(db.add_clause(list(raw)), f.add(raw),
                             f"disagreement on {raw}")
            self.assertEqual(db.clauses(), [list(c) for c in f.clauses],
                             f"stored form differs for {raw}")

    def test_dimacs_path_agrees(self):
        n = native.require()
        rng = random.Random(fuzz_seed(31))
        for _ in range(100):
            nvars = rng.randint(1, 8)
            dimacs = [rng.choice([1, -1]) * rng.randint(1, nvars)
                      for _ in range(rng.randint(1, 4))]
            f = CNF(nvars)
            db = n.ClauseDb(nvars)
            self.assertEqual(db.add_dimacs(list(dimacs)), f.add_dimacs(dimacs))
            self.assertEqual(db.clauses(), [list(c) for c in f.clauses])

    def test_generated_benchmark_families_round_trip(self):
        """The real instances, not just random ones."""
        from cdclkit.cli import gen_php, gen_queens, gen_random_ksat

        for label, f in (("php", gen_php(7, 6)),
                         ("queens", gen_queens(12)),
                         ("rand3", gen_random_ksat(120, 511, 3, 4))):
            with self.subTest(family=label):
                db, _ = self._load(f)
                self.assertEqual(db.clauses(), [list(c) for c in f.clauses])
                self.assertEqual(db.num_vars, f.nvars)

    def test_empty_clause_survives(self):
        n = native.require()
        db = n.ClauseDb(3)
        self.assertTrue(db.add_clause([]))
        self.assertEqual(db.clause(0), [])
        self.assertEqual(db.num_clauses, 1)

    def test_out_of_range_clause_index_raises(self):
        n = native.require()
        db = n.ClauseDb(2)
        db.add_clause([0, 2])
        with self.assertRaises(ValueError):
            db.clause(5)

    def test_variable_count_grows_with_literals(self):
        n = native.require()
        db = n.ClauseDb(0)
        db.add_clause([mk_lit(9)])
        self.assertEqual(db.num_vars, 10)


@requires_native
class TestArenaLayout(unittest.TestCase):
    """The arena's reason for existing is memory locality; check it is real."""

    def test_memory_is_proportional_to_literals_not_clauses(self):
        n = native.require()
        db = n.ClauseDb(0)
        for i in range(1000):
            db.add_clause([mk_lit(i % 50), mk_lit((i + 1) % 50, True)])
        # 2000 literals * 4 bytes, plus two u32 side tables of 1000 entries.
        # Allow generous slack for Vec growth, but it must be within a small
        # constant of the data itself -- an object-per-clause layout would be
        # an order of magnitude more.
        self.assertLess(db.memory_bytes, 2000 * 4 + 1000 * 8 + 65536)
        self.assertEqual(db.num_lits, 2000)

    def test_len_and_repr(self):
        n = native.require()
        db = n.ClauseDb(2)
        db.add_clause([0, 2])
        db.add_clause([1])
        self.assertEqual(len(db), 2)
        self.assertIn("ClauseDb", repr(db))
        self.assertIn("clauses=2", repr(db))


if __name__ == "__main__":
    unittest.main()
