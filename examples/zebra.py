# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Einstein's zebra puzzle, written with the finite-domain modelling layer.

Fifteen clues over five houses and five attributes each.  Modelled as 25
finite-domain integers -- each attribute value gets a variable whose value is
the *house number* that holds it -- with an all-different per attribute.  That
"value -> position" orientation is the one that makes clues like "the Norwegian
lives next to the blue house" a two-line constraint instead of a case analysis.

The puzzle is famous for having a unique solution, so this also demonstrates
solution enumeration: we ask for every solution and expect exactly one.

Run:  python3 examples/zebra.py
"""

from __future__ import annotations

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from cdclkit.model import Model

HOUSES = range(1, 6)

NATIONS = ["English", "Spanish", "Ukrainian", "Norwegian", "Japanese"]
COLORS = ["red", "green", "ivory", "yellow", "blue"]
DRINKS = ["coffee", "tea", "milk", "orange juice", "water"]
SMOKES = ["Old Gold", "Kools", "Chesterfields", "Lucky Strike", "Parliaments"]
PETS = ["dog", "snails", "fox", "horse", "zebra"]


def main() -> None:
    m = Model()
    groups = {}
    for label, names in (
        ("nation", NATIONS),
        ("color", COLORS),
        ("drink", DRINKS),
        ("smoke", SMOKES),
        ("pet", PETS),
    ):
        vs = {n: m.int_var(HOUSES, f"{label}:{n}") for n in names}
        # each attribute value sits in exactly one house, and no two values of
        # the same attribute share a house -- a permutation, so the redundant
        # "every house is used" direction is added too
        m.all_different_permutation(list(vs.values()))
        groups[label] = vs

    nation, color, drink, smoke, pet = (
        groups["nation"], groups["color"], groups["drink"], groups["smoke"], groups["pet"]
    )

    def same(a, b):
        """a and b are the same house."""
        m.add(a == b)

    def right_of(a, b):
        """a is immediately to the right of b."""
        m.add(("or", *[("and", a.is_(h + 1), b.is_(h)) for h in range(1, 5)]))

    def next_to(a, b):
        m.add(("or", *[
            ("and", a.is_(h), b.is_(h2))
            for h in HOUSES
            for h2 in HOUSES
            if abs(h - h2) == 1
        ]))

    #  1. Five houses in a row.                (structural, above)
    #  2. The Englishman lives in the red house.
    same(nation["English"], color["red"])
    #  3. The Spaniard owns the dog.
    same(nation["Spanish"], pet["dog"])
    #  4. Coffee is drunk in the green house.
    same(drink["coffee"], color["green"])
    #  5. The Ukrainian drinks tea.
    same(nation["Ukrainian"], drink["tea"])
    #  6. The green house is immediately to the right of the ivory house.
    right_of(color["green"], color["ivory"])
    #  7. The Old Gold smoker owns snails.
    same(smoke["Old Gold"], pet["snails"])
    #  8. Kools are smoked in the yellow house.
    same(smoke["Kools"], color["yellow"])
    #  9. Milk is drunk in the middle house.
    m.add(drink["milk"].is_(3))
    # 10. The Norwegian lives in the first house.
    m.add(nation["Norwegian"].is_(1))
    # 11. The Chesterfields smoker lives next to the fox owner.
    next_to(smoke["Chesterfields"], pet["fox"])
    # 12. Kools are smoked next to the house with the horse.
    next_to(smoke["Kools"], pet["horse"])
    # 13. The Lucky Strike smoker drinks orange juice.
    same(smoke["Lucky Strike"], drink["orange juice"])
    # 14. The Japanese smokes Parliaments.
    same(nation["Japanese"], smoke["Parliaments"])
    # 15. The Norwegian lives next to the blue house.
    next_to(nation["Norwegian"], color["blue"])

    st = m.stats()
    print(f"encoding: {st['vars']} variables, {st['clauses']} clauses, "
          f"{st['literals']} literals (avg clause length {st['avg_len']:.2f})")

    t0 = time.perf_counter()
    sols = list(m.solutions(project=[v for g in groups.values() for v in g.values()]))
    dt = time.perf_counter() - t0
    print(f"{len(sols)} solution(s) found in {dt*1000:.1f} ms")
    assert len(sols) == 1, "the zebra puzzle is supposed to be unique"

    sol = sols[0]
    header = f"{'house':<8}" + "".join(f"{h:<14}" for h in HOUSES)
    print(header)
    print("-" * len(header))
    for label in ("nation", "color", "drink", "smoke", "pet"):
        row = {sol[v]: name for name, v in groups[label].items()}
        print(f"{label:<8}" + "".join(f"{row[h]:<14}" for h in HOUSES))

    water = next(n for n, v in nation.items() if sol[v] == sol[drink["water"]])
    zebra = next(n for n, v in nation.items() if sol[v] == sol[pet["zebra"]])
    print(f"\nthe {water} drinks water; the {zebra} owns the zebra")
    assert (water, zebra) == ("Norwegian", "Japanese")


if __name__ == "__main__":
    main()
