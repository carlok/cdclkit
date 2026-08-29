# Security policy

## Reporting

Use GitHub's [private vulnerability
reporting](https://github.com/carlok/cdclkit/security/advisories/new). Please do
not open a public issue for anything in the first category below.

## What counts as a vulnerability here

**Critical: a wrong answer that looks right.** A satisfiable formula reported
UNSAT, or a model returned that does not satisfy the input. Both are checkable
by hand, so a report with the formula is enough. The CLI's `--self-check` and
`--check-model` exist to catch exactly these, so a case that slips past them is
worth more than one that does not.

**High: a crash or hang on untrusted input.** DIMACS files often come from
elsewhere. The parser should not be drivable into unbounded memory or an
exception a caller cannot distinguish from a verdict. Note that
`CNF.header_mismatch` exists because a malformed file once parsed to half its
clauses and every solver agreed on the wrong answer.

**Also wanted: a divergence between the Python and Rust engines.** They are
required to be bit-exact — identical conflicts, decisions and propagations. A
case where they differ is a real finding even if both answers are correct.

**Not a vulnerability:** being slow; running out of memory on a genuinely hard
instance; `pyeq` limitations, which are documented and experimental.

## Scope

The `cdclkit` and `cdclkit-native` packages at the latest released version.
Proof checking lives in [dratify](https://github.com/carlok/dratify) and has
its own policy.

## What this is not

Not formally verified. The engines are differentially tested against each other
and every UNSAT answer can be independently checked, which is not the same as a
machine-checked proof of the solver itself.
