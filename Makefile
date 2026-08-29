# cdclkit -- pure-Python CDCL SAT toolkit.  No dependencies, no build step.
PYTHON ?= python3

.PHONY: help test test-verbose test-native native venv coverage examples bench bench-check bench-full compare bench-public gate checkpoint history portfolio paper private-docs demo dist smoke repro clean clean-dist clean-native lint

help:
	@echo "make test      -- run the full test suite, no Rust needed (197 tests)"
	@echo "make native    -- build the optional Rust engine into .venv (needs cargo)"
	@echo "make test-native-- run the suite against the native build"
	@echo "make coverage  -- statement coverage via the stdlib trace module (slow)"
	@echo "make examples  -- run every example script"
	@echo "make bench     -- quick benchmark table"
	@echo "make bench-check-- compare conflict counts against bench/baseline.json"
	@echo "make bench-full-- full benchmark, all configurations, with proof checking"
	@echo "make compare   -- benchmark against external solvers on this machine"
	@echo "make bench-public-- fetch and run the public SATLIB corpus"
	@echo "make portfolio -- parallel portfolio timings on this machine"
	@echo "make gate      -- everything that must pass before a commit"
	@echo "make checkpoint LABEL=x -- gate, then record a benchmark checkpoint"
	@echo "make history   -- benchmark checkpoints recorded so far"
	@echo "make paper     -- build tex/cdclkit.pdf (positioning, business + technical)"
	@echo "make demo      -- solve a pigeonhole instance with a self-checked proof"
	@echo "make clean     -- remove __pycache__ and generated instances"

test:
	$(PYTHON) -m unittest discover -s tests

test-verbose:
	$(PYTHON) -m unittest discover -s tests -v

# The native engine is optional.  `make test` above deliberately uses the
# system interpreter with no Rust anywhere, because the dependency-free path is
# the one that must never break.  These targets exercise the other path.
VENV_PY = .venv/bin/python

venv:
	@test -x $(VENV_PY) || ($(PYTHON) -m venv .venv && .venv/bin/pip install -q maturin)
	@echo "c venv ready: $$($(VENV_PY) -VV | head -1)"

native: venv
	cd native && ../.venv/bin/maturin develop --release

test-native: 
	@test -x $(VENV_PY) || (echo "run 'make native' first" && exit 1)
	$(VENV_PY) -m unittest discover -s tests

clean-native:
	rm -rf native/target .venv
	cd tex && latexmk -C 2>/dev/null || true

coverage:
	$(PYTHON) tests/coverage_report.py

examples:
	@for f in examples/*.py; do echo "=== $$f ==="; $(PYTHON) $$f || exit 1; done

bench:
	$(PYTHON) bench/run_bench.py --quick --configs all

bench-public:
	$(PYTHON) bench/fetch_satlib.py
	$(PYTHON) bench/compare.py --instances bench/instances/satlib --engine portfolio --jobs 5 --timeout 120

compare:
	$(PYTHON) bench/compare.py --check-proofs

# The definition of "stable": no commit lands unless this passes.
gate:
	$(PYTHON) -m unittest discover -s tests
	$(PYTHON) bench/run_bench.py --quick --configs all --check-baseline
	$(PYTHON) bench/compare.py --quick

checkpoint: gate
	@test -n "$(LABEL)" || (echo "usage: make checkpoint LABEL=sprint0" && exit 1)
	$(PYTHON) bench/compare.py --record "$(LABEL)"

paper:
	cd tex && latexmk -pdf -quiet cdclkit.tex
	@echo "c built tex/cdclkit.pdf"

history:
	$(PYTHON) bench/compare.py --history

portfolio:
	$(PYTHON) bench/compare.py --engine portfolio

bench-check:
	$(PYTHON) bench/run_bench.py --quick --configs all --check-baseline

bench-full:
	$(PYTHON) bench/run_bench.py --proofs

# The solver follows SAT competition exit codes: 10 = SATISFIABLE,
# 20 = UNSATISFIABLE, 0 = UNKNOWN, 1 = error, 30 = the proof failed to verify.
# Make treats every non-zero status as a failure, so a target that runs the
# solver has to interpret the code rather than propagate it -- otherwise a
# perfectly good UNSAT answer aborts the build.
demo:
	$(PYTHON) -m cdclkit gen php -n 7 --out /tmp/cdclkit-php8.cnf
	@$(PYTHON) -m cdclkit solve /tmp/cdclkit-php8.cnf --self-check --no-model; \
	  status=$$?; \
	  case $$status in \
	    20) echo "c demo ok: unsatisfiable, proof verified (exit 20)" ;; \
	    10) echo "c demo ok: satisfiable (exit 10)" ;; \
	    30) echo "c demo FAILED: the proof did not verify (exit 30)"; exit 1 ;; \
	    *)  echo "c demo FAILED: unexpected exit $$status"; exit 1 ;; \
	  esac
	@rm -f /tmp/cdclkit-php8.cnf

lint:
	$(PYTHON) -m compileall -q cdclkit tests examples bench

dist: venv
	@$(VENV_PY) -c 'import build' 2>/dev/null || .venv/bin/pip install -q build hatchling
	rm -rf dist
	$(VENV_PY) -m build --outdir dist .
	cd native && ../.venv/bin/maturin build --release --out ../dist
	@ls -1 dist/

# The wheel is the artefact users get; the repo is not. Testing the repo and
# calling the release verified is how a missing package, a broken entry point
# or a file that never made it into the build reaches someone else first.
smoke: dist
	rm -rf .smoke && $(PYTHON) -m venv .smoke
	.smoke/bin/pip install -q "cdclkit[native]==$$($(PYTHON) -c 'import cdclkit; print(cdclkit.__version__)')" \
		--find-links dist --no-index
	@echo "c installed:" && .smoke/bin/pip list --format=freeze | grep cdclkit
	cd / && $(CURDIR)/.smoke/bin/cdclkit --version
	cd / && $(CURDIR)/.smoke/bin/cdclkit gen php -n 5 --out /tmp/cdclkit-smoke.cnf
	cd / && $(CURDIR)/.smoke/bin/cdclkit solve /tmp/cdclkit-smoke.cnf --self-check --no-model; \
		test $$? -eq 20 || (echo "expected exit 20 (UNSAT)" && exit 1)
	cd / && $(CURDIR)/.smoke/bin/python $(CURDIR)/tests/smoke_installed.py
	@echo "c smoke ok: the built artefacts work with no checkout on the path"

# A release claims provenance, so the claim gets a check. Two builds of the
# pure-Python wheel from the same source must hash the same.
repro:
	@$(MAKE) --no-print-directory dist >/dev/null
	@a=$$(shasum -a 256 dist/cdclkit-*-py3-none-any.whl | cut -d' ' -f1); \
	 $(MAKE) --no-print-directory dist >/dev/null; \
	 b=$$(shasum -a 256 dist/cdclkit-*-py3-none-any.whl | cut -d' ' -f1); \
	 if [ "$$a" = "$$b" ]; then echo "c reproducible: $$a"; \
	 else echo "c NOT reproducible:"; echo "c   $$a"; echo "c   $$b"; exit 1; fi

# Untracked documents for a specific reader. The examples are run first: a
# document whose examples do not work is worse than no document.
private-docs:
	@test -d docs/private || (echo "docs/private/ is absent (gitignored)" && exit 1)
	PYTHONPATH=. $(VENV_PY) docs/private/example_a_python.py
	PYTHONPATH=. $(VENV_PY) docs/private/example_b_modelling.py
	PYTHONPATH=. $(VENV_PY) docs/private/example_c_money.py
	cd docs/private && latexmk -pdf -quiet cdclkit-primer.tex cdclkit-status.tex provex-value.tex
	@ls -1 docs/private/*.pdf

clean-dist:
	rm -rf dist .smoke

clean: clean-dist
	find . -name '__pycache__' -type d -exec rm -rf {} + 2>/dev/null || true
	rm -rf bench/instances
