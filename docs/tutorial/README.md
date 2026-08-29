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

## Planned: a web version

Not started. Recorded here so the requirement is not lost.

The target is a proper site -- something like the Lean Frontier pages -- served
under `carlok.github.io`, not a PDF with a download link and not the output of
a LaTeX-to-HTML converter. `tex4ht`, `pandoc` and `latex2html` all produce
pages that look converted, and that is the thing to avoid.

So: author the HTML, do not translate the PDF. What makes that cheap is that
the content is already shaped for it.

- **Structure already fits.** Theory, then one page per language. Roughly one
  HTML page per part, or per section if they run long.
- **Code snippets come from `code/`,** the same files `\lstinputlisting` reads
  here. Highlight them at build time (Pygments, Shiki, highlight.js) so the
  site cannot drift from what runs, exactly as the PDF cannot today.
- **Math needs real rendering** -- KaTeX or MathJax. There is not much of it
  (CNF notation, the RUP rule), but images of equations would look as
  converted as everything else.
- `run_examples.sh` stays the check that every snippet on the site executes.

The PDF stays. It is the offline artefact; the site is the one people land on.
