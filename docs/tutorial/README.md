# Tutorial

A tutorial for a working Python or Rust programmer who knows boolean logic and
has never used a SAT solver.

    tutorial.tex     the document
    tutorial.pdf     built output
    code/            every example, runnable
    run_examples.sh  runs them all

Build with `latexmk -pdf tutorial.tex`.

Listings are pulled from `code/` with `\lstinputlisting`, so the document
cannot drift from the code that actually runs. The outputs quoted in the text
were captured from real runs; `./run_examples.sh` reproduces them.

Structure: common theory first (CNF, DIMACS, why UNSAT needs a proof), then a
Python section, then a Rust section. The Rust part covers the `dratify` proof
checker, since that is the piece with a Rust API — solving from Rust is not
what this project is for.

The PDF is committed so readers do not need a LaTeX installation. Build
artefacts (`.aux`, `.log`, `.toc`, the Rust `target/`) are gitignored.

A future version of this could be a set of HTML pages rather than a PDF; the
content is structured for that -- theory, then one section per language -- and
the examples already live as separate runnable files.
