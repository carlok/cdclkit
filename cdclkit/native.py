# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Optional native engine: loader and capability probe.

cdclkit's Python core has no dependencies and never will. The native engine is a
strictly optional accelerator, and this module is the only place that knows
whether it exists.

The contract, in both directions:

* **If the compiled module is absent, nothing breaks.** `available()` returns
  False, every caller falls back to Python, and the test suite still passes in
  full under a plain `python3` with no Rust toolchain anywhere. That property
  is tested, not assumed -- it is what lets the port proceed in small commits
  without the repo ever being in a broken state.
* **If it is present, it is opt-in.** Nothing selects the native path on its
  own. A caller asks for it explicitly (`--engine native`, or
  `CDCLKIT_ENGINE=native`), because a silent switch between two implementations
  is how differential bugs hide.

Building it::

    python3 -m venv .venv
    .venv/bin/pip install maturin
    make native                 # or: cd native && ../.venv/bin/maturin develop --release

The build installs into `.venv`, so `.venv/bin/python` sees the native engine
and the system interpreter does not. That separation is deliberate: it keeps a
dependency-free path available at all times.
"""

from __future__ import annotations

import os

__all__ = [
    "available",
    "require",
    "module",
    "version",
    "build_hint",
    "engine_requested",
]

try:  # pragma: no cover - the import result is the thing being reported
    import cdclkit_native as _native
except ImportError:  # pragma: no cover
    _native = None
else:  # pragma: no cover - depends on whether the module was built
    # The Rust checker lives in the `dratify` crate, which this crate embeds,
    # but `dratify` ships no Python bindings of its own yet. Hand ours over so
    # that check_proof(engine="auto") uses it instead of falling back to the
    # pure-Python checker, which is ~18x slower on large proofs.
    #
    # This is not the silent engine switch the rest of this module warns about.
    # Two checkers must agree by construction -- if they ever disagree that is
    # a bug worth surfacing, not a difference worth preserving. The solver is
    # the thing that stays explicitly opt-in.
    try:
        import dratify as _dratify
        _dratify.register_native(_native)
    except (ImportError, AttributeError):  # dratify < 0.1.1 has no seam
        pass


BUILD_HINT = (
    "the native engine is not built for this interpreter. Build it with:\n"
    "    python3 -m venv .venv && .venv/bin/pip install maturin\n"
    "    make native\n"
    "then run with .venv/bin/python. The pure-Python engine needs none of this."
)


def available() -> bool:
    """True when the compiled native module can be imported."""
    return _native is not None


def module():
    """The native module, or None.  Prefer `require()` when you need it."""
    return _native


def require():
    """Return the native module, raising a useful error when it is missing."""
    if _native is None:
        raise RuntimeError(BUILD_HINT)
    return _native


def version() -> str | None:
    return getattr(_native, "__version__", None) if _native else None


def build_hint() -> str:
    return BUILD_HINT


def engine_requested(default: str = "python") -> str:
    """Which engine the environment asks for.

    Reads `CDCLKIT_ENGINE`; an explicit request for an unavailable engine is an
    error rather than a silent downgrade, because "I asked for native and got
    Python timings" is a bad way to spend an afternoon.
    """
    want = os.environ.get("CDCLKIT_ENGINE", default).strip().lower()
    if want not in ("python", "native"):
        raise ValueError(f"unknown CDCLKIT_ENGINE {want!r} (expected python or native)")
    if want == "native" and not available():
        raise RuntimeError("CDCLKIT_ENGINE=native but " + BUILD_HINT)
    return want
