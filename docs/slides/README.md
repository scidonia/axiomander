# Axiomander Slides

A [Slidev](https://sli.dev) deck motivating **vericoding** and presenting the
Axiomander architecture. Companion to [`docs/whitepaper.md`](../whitepaper.md).

## Run

```bash
cd docs/slides
npm install        # first time only
npm run dev        # live presentation at http://localhost:3030
```

## Build / Export

```bash
npm run build      # static site -> dist/
npm run export     # PDF (requires playwright-chromium: npx playwright install chromium)
```

## Notes

- Math (Hoare triples, WP rules, the frame rule) is rendered with KaTeX via
  `$...$` (inline) and `$$...$$` (display).
- Diagrams use Mermaid code fences.
- Speaker notes live in `<!-- ... -->` HTML comments after a slide's `---`.
