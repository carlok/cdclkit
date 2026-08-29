# Releasing

The checklist exists so release two is not archaeology. Nothing here is
automated on purpose: a release is rare enough that the cost of remembering is
lower than the cost of a workflow that silently rots between uses.

## Before you start

The repository is **private and unlicensed**. A release today means a tagged
GitHub release with wheels attached, not a PyPI upload. Publishing to a public
index is a licence decision first and a packaging step second — see
[LICENSING.md](LICENSING.md).

## 1. The tree has to be honest

```bash
make gate                    # tests, examples, conflict baselines
make test-native             # the same suite against the Rust engine
cd native && cargo test && cargo clippy --all-targets
make smoke                   # build both wheels, install clean, run from /
make paper                   # tex/cdclkit.pdf builds with no warnings
```

All green, tree clean, nothing uncommitted.

Then the part that is not a command: **read the claims**. The README, the
paper and `CHANGELOG.md` all state numbers, and numbers go stale silently.
This has already happened once — the README said 129 tests when there were 263,
and carried a coverage table from three phases earlier. Check at minimum:

- test count and coverage percentage
- the competitor tables in the README and `tex/cdclkit.tex`
- the "Known limitations" list in `CHANGELOG.md`
- anything in the paper's roadmap that has since shipped

Any performance figure must be a **geometric mean of per-instance ratios**,
measured in the same session on the same machine, with each external solver's
process startup subtracted. Never a sum of wall times: this repository has a
documented history of one heavy-tailed random instance faking a large win three
separate times.

Two rules learned the hard way, both worth re-reading before quoting a number:

- **Never quote a single-sample number.** `--repeat 3` at minimum, and state
  the run-to-run spread the harness prints beside the geometric mean. A
  reported difference smaller than that spread is noise. kissat's own speed
  varied 35% between two runs of the same binary here.
- **Never exclude instances on a per-run absolute-time threshold.** The old
  rule dropped anything the competitor solved in under 50 ms, and the drift
  above moved half a family in and out of the sample -- the instances that
  dropped being the ones where the competitor is fastest.
- **Never compare on an instance both solvers failed to finish.** The ratio is
  1.0 by construction and dilutes the mean toward parity while measuring
  nothing.
- **Report the holdout group separately.** Configurations are chosen against
  the tune families; only the holdout families can say whether that generalised,
  and `bench/sweep.py` refuses to load them so it stays that way.
- **Run benchmarks under `caffeinate -i`, alone.** A suspended host and a
  concurrent build have each corrupted a run in this project's history, and
  both look exactly like a hard instance afterwards.

## 2. Version

One number lives in `cdclkit/__init__.py`. `native/Cargo.toml` must match, and
`tests/test_packaging.py` fails if they drift — they already did once, at
1.0.0 against 0.1.0.

```bash
$EDITOR cdclkit/__init__.py native/Cargo.toml pyproject.toml   # the [native] extra pins it too
python3 -m unittest tests.test_packaging
```

Semantic versioning applies to the names in `cdclkit/__init__.__all__` and
nothing else. `pipeline`, `portfolio` and `native` are internal.

## 3. Changelog

Move `[Unreleased]` to the new version with today's date. Write for someone
deciding whether to upgrade, not for someone reading a diff: what breaks, what
is fixed, and what is still not there. The "Known limitations" section is not
optional — the platforms that are untested and the things the tool cannot do
belong in the release, not in a later bug report.

## 4. Build, and record what built it

```bash
make dist
python3 -m twine check dist/*
```

Record the toolchain in the release notes, because "reproducible" is a claim
like any other:

```bash
python3 -VV
rustc --version && cargo --version
sw_vers 2>/dev/null || lsb_release -a 2>/dev/null
shasum -a 256 dist/*
```

The pure-Python wheel is `py3-none-any` and is byte-identical between builds
from the same source — `make repro` checks it, and it holds today. That is a
same-machine result; cross-machine reproducibility is plausible but has not
been measured, so do not claim it. The native wheel is per-platform and per
Python minor version and is not expected to reproduce across toolchains.

## 5. Tag and release

```bash
git tag -s v1.0.0 -m "cdclkit 1.0.0"     # signed; an unsigned tag proves nothing
git push origin main --follow-tags
gh release create v1.0.0 --notes-file <(sed -n '/## \[1.0.0\]/,/## \[0/p' CHANGELOG.md) \
    dist/*.whl dist/*.tar.gz tex/cdclkit.pdf bench/baseline.json
```

`bench/baseline.json` goes in deliberately. It is the conflict-count reference
the benchmark harness checks against, and attaching it makes every performance
claim in the release re-runnable by whoever downloads it.

Consider `gh attestation` / Sigstore on the wheels. For a project whose pitch
is verifiable provenance of *answers*, unverifiable provenance of the
*artefact* is the obvious hole — and CI already builds them, so it is close to
free.

## 6. After

Open `[Unreleased]` in the changelog again. If anything in this file was wrong
or missing while you were following it, fix it now rather than next time.

## If it goes public

Then, and only then, these become relevant, in this order:

1. A licence decision (`docs/LICENSING.md`). Everything else waits on it.
2. PyPI trusted publishing via GitHub OIDC — no long-lived token anywhere.
3. Reserve the name on PyPI before announcing it anywhere.
4. Sigstore attestations, which are worth more once the artefacts are public.
