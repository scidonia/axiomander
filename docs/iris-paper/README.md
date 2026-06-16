# Iris Workshop Paper

**Specification Composition for LLM-Driven Python Verification: Why We Build on Iris**

A short workshop paper for the Iris / separation-logic community, justifying and
explaining Axiomander's specification-composition strategy.

## Source of truth

`iris-workshop-paper.tex` is the **primary** source. It uses the ACM `acmart`
document class in `sigconf` (two-column) format with `nonacm` (self-archived
draft, not a submitted proceedings copy).

`iris-workshop-paper.notes.md` is a secondary, prose-only copy kept for quick
reading and diffing; the LaTeX is authoritative.

## Build

```bash
cd docs/iris-paper
latexmk -pdf iris-workshop-paper.tex
# output: iris-workshop-paper.pdf  (6 pages, two-column ACM)
```

`latexmk -C` cleans build artifacts.

## Vendored class files

`acmart.cls` and the ACM bibliography support files
(`ACM-Reference-Format.bst`, `acm{authoryear,numeric}.{bbx,cbx}`,
`acmdatamodel.dbx`) are vendored here so the build is self-contained on a system
whose TeX Live lacks the `acmart` package. They are generated from the upstream
CTAN `acmart` distribution (`tex acmart.ins`). If your TeX install already
provides `acmart`, you may delete the local copies and let the installed version
be found.

## Dependencies

Standard TeX Live packages: `mathtools`, `mathpartir`, `booktabs`, `listings`,
`xcolor`, plus the `libertine`/`newtx` fonts that `acmart` pulls in (all present
in a full TeX Live).
