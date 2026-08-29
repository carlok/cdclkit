# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.

import inspect, sys
sys.path.insert(0, "/Users/carlo/Documents/varie/hacks/scratch/burners/burner_1")
sys.path.insert(0, "/Users/carlo/Documents/varie/hacks/scratch/burners/burner_1/experiments/pyeq-llm-refactor")
from corpus import CORPUS
from guard import falls_off_the_end
from cdclkit import equivalent, UnsupportedConstruct

bad_guard, bad_subset, ok = [], [], 0
for f in CORPUS:
    if falls_off_the_end(f):
        bad_guard.append(f.__name__); continue
    w = {p: 8 for p in inspect.signature(f).parameters}
    try:
        r = equivalent(f, f, widths=w)
        if r.proved is not True:
            bad_subset.append((f.__name__, f"self-equivalence proved={r.proved}"))
        else:
            ok += 1
    except UnsupportedConstruct as e:
        bad_subset.append((f.__name__, str(e).splitlines()[0][:70]))

print(f"  {ok}/{len(CORPUS)} usable")
if bad_guard:
    print(f"  falls off the end ({len(bad_guard)}): {bad_guard}")
for n, why in bad_subset:
    print(f"  REJECTED {n}: {why}")
