# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Where each campaign finding stands, for every generator to read.

A generator labels a mismatch with the finding that explains it. What the label
means depends on this file:

* **Fixed.** The mismatch is a regression: it prints as REGRESSION and fails the
  run, however well the label explains it.
* **Open.** Reviewed and left as it is, so it is reported and does not fail the run.
  campaign/findings/STATUS.md says why for each one.
* Anything else is UNEXPLAINED, and fails.

So exit 0 now means no regression, nothing unexplained, and every category reached.
It used to mean that no finding existed at all, which could only ever come true by
fixing every one, and until then a new failure looked the same as an old one.
"""

from __future__ import annotations

FIXED = frozenset({
    "preprocess-1", "preprocess-2",
    "engines-4", "engines-5", "engines-6", "engines-7", "engines-8", "engines-9",
    "modelling-1", "modelling-2", "modelling-3", "modelling-4", "modelling-5",
    "modelling-6", "modelling-7", "modelling-8", "modelling-9", "modelling-10",
    "modelling-11", "modelling-12", "modelling-13", "modelling-17",
    "encodings-1", "encodings-2", "encodings-3", "encodings-4", "encodings-5",
    "encodings-6",
    "mus-1",
})

OPEN = frozenset({
    "preprocess-3", "preprocess-4",
    "engines-1", "engines-2", "engines-3",
    "modelling-14", "modelling-15", "modelling-16",
    "mus-2", "mus-3",
})


def state(finding: str) -> str:
    """"fixed" or "open". A finding nobody has placed is a mistake here, so it raises."""
    if finding in FIXED:
        return "fixed"
    if finding in OPEN:
        return "open"
    raise KeyError(f"{finding} is in neither FIXED nor OPEN in campaign/status.py")


def split(counts) -> tuple[dict, dict]:
    """Split a {finding: n} mapping into (regressions, still open)."""
    regressions = {k: v for k, v in counts.items() if state(k) == "fixed"}
    still_open = {k: v for k, v in counts.items() if state(k) == "open"}
    return regressions, still_open
