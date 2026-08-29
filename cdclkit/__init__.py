# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""cdclkit -- a CDCL SAT solving toolkit with checkable proofs, in pure Python.

Everything here is written from scratch against the standard library only.
The public surface:

    from cdclkit import Solver, CNF, Encoder, solve

    f = CNF()
    a, b, c = f.new_var(), f.new_var(), f.new_var()
    f.add([lit(a), lit(b)])          # a v b
    f.add([lit(a, True), lit(c)])    # ~a v c
    status, model = solve(f)

Modules:

``lits``        literal encoding and three-valued logic
``cnf``         clause/formula containers and DIMACS I/O
``heap``        indexed activity heap for VSIDS
``solver``      the CDCL core
``proof``       DRAT emission and an independent DRAT checker
``preprocess``  subsumption, strengthening, variable elimination
``mus``         minimal unsatisfiable subsets (deletion, QuickXplain)
``encodings``   Tseitin, cardinality, pseudo-boolean, totalizer, optimisation
``model``       a small typed modelling layer over the encoder
``pyeq``        prove two Python functions equivalent, or find an input where
                they are not
``brute``       reference solvers used to cross-check everything else
``cli``         the ``python -m cdclkit`` command line

Public API
----------
Everything in ``__all__`` below is public and follows semantic versioning: it
will not change incompatibly without a major version bump, and anything due to
be removed gets a ``DeprecationWarning`` for one minor release first.

Everything else is internal, including ``cdclkit.pipeline``, ``cdclkit.portfolio``
and ``cdclkit.native``. They are importable because Python has no way to stop
you, not because they are stable. If you need something from them, say so and
it can be promoted -- that is a smaller problem than finding out from a broken
build that someone depended on it.
"""

from __future__ import annotations

from dratify.cnf import CNF, Clause, parse_dimacs, parse_dimacs_file, write_dimacs
from .encodings import Encoder, Totalizer, optimise
from dratify.lits import from_dimacs, mk_lit, neg, to_dimacs
from .mus import MUSExtractor, mus
from .preprocess import Preprocessor, preprocess
from dratify.proof import DRATChecker, MemoryProof, ProofWriter, check_proof
from .solver import Config, SAT, Solver, Stats, UNKNOWN, UNSAT

__version__ = "0.1.1"

__all__ = [
    "CNF",
    "Clause",
    "Config",
    "DRATChecker",
    "Encoder",
    "EncodingDisagreement",
    "EquivalenceResult",
    "MUSExtractor",
    "MemoryProof",
    "Preprocessor",
    "ProofRejected",
    "ProofWriter",
    "SAT",
    "UNKNOWN",
    "UNSAT",
    "Solver",
    "Stats",
    "Totalizer",
    "UnsupportedConstruct",
    "check_proof",
    "differential_solve",
    "equivalent",
    "from_dimacs",
    "lit",
    "mk_lit",
    "mus",
    "neg",
    "optimise",
    "parse_dimacs",
    "parse_dimacs_file",
    "preprocess",
    "solve",
    "to_dimacs",
    "write_dimacs",
    "__version__",
]


#: Public names that live in `cdclkit.pyeq`, resolved on first access rather than
#: at import. `pyeq` needs `inspect` to read a function's source, and `inspect`
#: drags in `re` and `functools`: importing it eagerly was 5.5 ms of an 8.8 ms
#: `import cdclkit`, paid by everyone including the CLI solving a DIMACS file.
#: Startup is not a rounding error here -- the benchmark harness discards
#: instances a competitor finishes in under 50 ms because process startup
#: dominates them.
_LAZY = {
    "equivalent": "pyeq",
    "EquivalenceResult": "pyeq",
    "differential_solve": "model",
    "EncodingDisagreement": "model",
    "UnsupportedConstruct": "pyeq",
    "ProofRejected": "pyeq",
}


# Imported eagerly, not lazily: importing it is what registers the native
# checker with `dratify`, and a checker that is present but unregistered would
# silently cost ~18x on proof checking. The import is a single guarded attempt
# at a compiled module and costs nothing when it is absent.
from . import native as _native_loader  # noqa: F401,E402


def __getattr__(name: str):
    """PEP 562 lazy attribute access for the heavier public names."""
    mod = _LAZY.get(name)
    if mod is None:
        raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
    import importlib

    value = getattr(importlib.import_module(f".{mod}", __name__), name)
    globals()[name] = value  # resolve once; subsequent lookups skip __getattr__
    return value


def __dir__() -> list[str]:
    return sorted(__all__)


def lit(var: int, negated: bool = False) -> int:
    """Alias for :func:`cdclkit.lits.mk_lit`, the common spelling in user code."""
    return mk_lit(var, negated)


def solve(formula: CNF, proof=None, config: Config | None = None):
    """Solve a formula in one call.

    Returns ``(True, model)`` or ``(False, None)``.  ``model`` is a list of
    booleans indexed by variable.
    """
    s = Solver(formula.nvars, proof=proof, config=config)
    if not s.add_cnf(formula):
        return False, None
    if s.solve():
        return True, s.model
    return False, None
