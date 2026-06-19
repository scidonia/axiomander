# Vericoding Paper (FSE-targeted draft)

**Vericoding: Specification-Centric Software Development for the AI Era**

A software-engineering vision/experience paper arguing that cheap LLM
implementation makes the *specification* the primary maintained artifact, grounded
in the Axiomander verifier. Targeted at FSE.

## Source of truth

`vericoding-paper.tex` is the **primary** source. It uses the ACM `acmart`
document class in `sigconf` (two-column) format with `nonacm` (self-archived
draft, not a submitted proceedings copy).

Starter outline: [`../vericoding-paper-outline.md`](../vericoding-paper-outline.md).
Grounding material: [`../whitepaper.md`](../whitepaper.md) (Axiomander
whitepaper) and the companion Iris paper in [`../iris-paper/`](../iris-paper/)
(source of the compositional-scaling measurement in Section 6).

## Build

```bash
cd docs/vericoding-paper
latexmk -pdf vericoding-paper.tex
# output: vericoding-paper.pdf  (two-column ACM)
```

`latexmk -C` cleans build artifacts.

## Vendored class files

`acmart.cls` and the ACM bibliography support files
(`ACM-Reference-Format.bst`, `acm{authoryear,numeric}.{bbx,cbx}`,
`acmdatamodel.dbx`) are vendored here so the build is self-contained on a system
whose TeX Live lacks the `acmart` package. If your TeX install already provides
`acmart`, you may delete the local copies.

## Dependencies

Standard TeX Live packages: `mathtools`, `mathpartir`, `booktabs`, `listings`,
`xcolor`, `amssymb`, plus the `libertine`/`newtx` fonts that `acmart` pulls in.
