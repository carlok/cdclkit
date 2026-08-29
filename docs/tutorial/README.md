# Tutorial

A tutorial for a working Python or Rust programmer who knows boolean logic and
has never used a SAT solver.

    tutorial.tex     the document
    tutorial.pdf     built output
    code/            every example, runnable
    build/           files the examples write (gitignored)
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

The target is a static site under `carlok.github.io`, not the output of a
LaTeX-to-HTML converter. `tex4ht`, `pandoc` and `latex2html` all produce pages
that look converted, which is the thing being avoided.

### A reference for the standard, not a palette to copy

**LeanFrontier** (`carlok/LeanFrontier`, `docs/website/`) came up as an example
of the *level* to aim for. It is not a template — this site should look like
itself, and the colours below are one solution rather than the solution. What
is worth stealing is the discipline, not the hex codes.

`docs/website/` is `index.html`, one `assets/site.css` (168 lines), a favicon,
and nine field notes. What makes it good:

- **Zero JavaScript.** Not one `<script>` tag on any page.
- **A warm paper palette, not a dev-tool dark theme.** `--paper: #f4f1e8`,
  `--ink: #17221e`, `--accent: #0c6d56`. Georgia for display, Helvetica for
  body, SFMono for code -- system fonts only, nothing fetched.
- **Code blocks invert:** dark `--ink` background with light text, inside an
  otherwise light page, `overflow-x: auto`.
- **Syntax highlighting is hand-written spans** (`.lean-keyword`,
  `.lean-declaration`, `.lean-module`), not a JS library.
- **Accessibility is deliberate:** skip link, `aria-labelledby` on every
  section, `:focus-visible` outlines, a `prefers-reduced-motion` block.
- Layout is `width: min(1120px, calc(100% - 3rem))`, centred; pages are
  `<article class="note">` with a `note-header` and plain `<section>`s.

### How to build ours

Jinja2 templates rendered to static HTML at build time. The three things that
need care:

1. **Snippets come from `code/`,** the same files `\lstinputlisting` reads for
   the PDF. Highlight with **Pygments at build time** -- that produces the same
   kind of pre-highlighted spans LeanFrontier writes by hand, with no runtime
   JS and no drift from what runs.
2. **Math needs rendering without breaking the zero-JS property.** There is
   little of it (CNF notation, the RUP rule), so render with the **KaTeX CLI at
   build time** into static HTML plus its stylesheet. Loading KaTeX in the
   browser would be the easy path and would be the first `<script>` on the
   site.
3. **`run_examples.sh` stays the gate.** If a snippet on the site does not run,
   the build should fail, exactly as the PDF cannot currently drift.

Pick a palette that suits this project rather than inheriting one. The
properties to keep are the zero-JS constraint, system fonts, real focus states,
and code blocks that are legible rather than decorative.

The PDF stays. It is the offline artefact; the site is where people land.
