# cdclkit-native

**The optional Rust engine for [`cdclkit`](https://pypi.org/project/cdclkit/).**
You probably do not want to install this directly.

```bash
pip install "cdclkit[native]"    # this is the one you want
```

That pulls this package in and wires it up. Installing `cdclkit-native` on its
own gives you a compiled module with nothing to drive it.

## What it is

`cdclkit` is a CDCL SAT solver written in readable Python. This package is the
same solver ported to Rust, and it is **bit-exact** with the Python one:
identical conflicts, decisions and propagations on every instance. It is not a
different solver that happens to be faster — it is the same search, and a test
suite compares the two counter by counter to keep it that way.

Roughly 18x faster than the pure-Python engine.

It is optional on purpose. The dependency-free Python path is the reference
implementation and the one that must never break; nothing selects this engine
on its own, a caller asks for it.

## It also carries the proof checker

The Rust DRAT checker from the [`dratify`](https://crates.io/crates/dratify)
crate is embedded here. On import, this module registers itself with the
[`dratify`](https://pypi.org/project/dratify/) Python package through its
`register_native()` seam, so proof checking gets the Rust implementation too
(~18x faster on large proofs) rather than only the solver.

That is why `pip install "cdclkit[native]"` speeds up `--self-check`, not just
the search.

## Wheels

abi3 (`abi3-py310`), so one wheel per platform covers every Python from 3.10 up:

| | |
|---|---|
| Linux | x86_64, aarch64 (manylinux 2.17) |
| macOS | x86_64, arm64 |

No Windows: it has never been tested here, and the classifiers say so rather
than implying support.

## Links

- [`cdclkit`](https://pypi.org/project/cdclkit/) — the toolkit this accelerates
- [`dratify`](https://pypi.org/project/dratify/) — the proof checker, zero dependencies
- [Source](https://github.com/carlok/cdclkit)

## Licence

Apache-2.0.
