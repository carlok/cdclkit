# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""The DPLL against the oracle, and on cases past the oracle's limit.

Run from the repository root: python -m unittest campaign.test_dpll
"""

from __future__ import annotations

import itertools
import random
import unittest

try:
    from campaign import dpll, oracle
except ImportError:            # run from inside campaign/
    import dpll
    import oracle


class TestDpll(unittest.TestCase):
    def test_known_answers(self):
        self.assertTrue(dpll.satisfiable([]))
        self.assertFalse(dpll.satisfiable([[]]))
        self.assertFalse(dpll.satisfiable([[1], [-1]]))
        self.assertTrue(dpll.satisfiable([[1, -1]]))
        self.assertFalse(dpll.satisfiable([[1, 2], [1, -2], [-1, 2], [-1, -2]]))
        with self.assertRaises(ValueError):
            dpll.satisfiable([[0]])

    def test_agrees_with_the_oracle_and_its_models_are_models(self):
        rng = random.Random(4242)
        answers = set()
        for _ in range(5000):
            nvars = rng.randint(1, 16)
            f = [[rng.choice((1, -1)) * rng.randint(1, nvars)
                  for _ in range(rng.randint(1, 3))]
                 for _ in range(rng.randint(0, 4 * nvars))]
            m = dpll.model(f)
            self.assertEqual(m is not None, oracle.satisfiable(f), f)
            answers.add(m is not None)
            if m is not None:
                for c in f:
                    lits = set(c)
                    if not any(-l in lits for l in lits):
                        self.assertTrue(any(m.get(abs(l)) == (l > 0) for l in lits), (f, m))
        self.assertEqual(answers, {True, False})

    def test_past_the_oracle_a_chain_of_implications(self):
        n = 400
        chain = [[1]] + [[-v, v + 1] for v in range(1, n)]
        self.assertTrue(dpll.satisfiable(chain))
        self.assertFalse(dpll.satisfiable([*chain, [-n]]))

    def test_projected_models_are_exact(self):
        # 3 is 1 XOR 2, projected on (1, 3): all four combinations extend
        xor = [[-3, 1, 2], [-3, -1, -2], [3, -1, 2], [3, 1, -2]]
        self.assertEqual(len(dpll.projected_models(xor, [1, 3])), 4)
        # with 2 false, 3 equals 1
        self.assertEqual(dpll.projected_models([*xor, [-2]], [1, 3]),
                         {(False, False), (True, True)})

    def test_projected_models_against_a_plain_loop(self):
        rng = random.Random(99)
        for _ in range(300):
            f = [[rng.choice((1, -1)) * rng.randint(1, 7)
                  for _ in range(rng.randint(1, 3))]
                 for _ in range(rng.randint(0, 12))]
            expected = set()
            for values in itertools.product((False, True), repeat=4):
                units = [[v if b else -v] for v, b in zip((1, 2, 3, 4), values)]
                if oracle.satisfiable([*f, *units]):
                    expected.add(values)
            self.assertEqual(dpll.projected_models(f, [1, 2, 3, 4]), expected, f)


if __name__ == "__main__":
    unittest.main()
