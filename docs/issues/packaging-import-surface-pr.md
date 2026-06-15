# Namespace the Python side under `py/axiomander/` and fix packaging

Fixes #<issue>.

## Change

- Move the Python package under a single namespace (history-preserving `git mv`):
  - `py/oracle/` -> `py/axiomander/oracle/`
  - `py/contracts/` -> `py/axiomander/contracts/`
  - `py/examples/` -> `py/axiomander/examples/`
  - `py/wp_transformer.py` -> `py/axiomander/wp_transformer.py`
  - `py/proof_obligations.py` -> `py/axiomander/proof_obligations.py`
  - add `py/axiomander/__init__.py`
  - `py/tests/` stays put.
- Packaging now discovers only the namespace package:

  ```toml
  [tool.setuptools.packages.find]
  where = ["py"]
  include = ["axiomander*"]
  ```

- Rewrite the ~17 absolute imports `oracle.*` / `contracts.*` to `axiomander.oracle.*` / `axiomander.contracts.*` (the ~11 relative `from .X` imports are unaffected); change `from py.wp_transformer import` to `from axiomander.wp_transformer import`.
- Drop the `sys.path` / `PYTHONPATH=py` workarounds in `mcp_config.json` (`-m axiomander.oracle.mcp_server`), `Makefile`, `README.md`, and `AGENTS.md`.

## Why this layout

Plain `where = ["py"]` without the namespace package is rejected: it would publish `oracle` and `contracts` as top-level packages, which are far too generic to be safe neighbors in a shared venv. Wrapping them in `axiomander` keeps the import surface clean and collision-free, while `py/` remains the Python source root alongside `coq/` and the TypeScript component.

## Acceptance

- `pip install -e .` then `python -c "import axiomander.oracle.advisor"` works with no `PYTHONPATH` / `sys.path` manipulation.
- `pytest py/tests/ -q` passes.
- Downstream consumers can depend on axiomander via:

  ```toml
  [dependency-groups]
  dev = ["axiomander"]

  [tool.uv.sources]
  axiomander = { path = "../CausalInference/Vericoding/axiomander", editable = true }
  ```

  and use `from axiomander.oracle.advisor import analyze_file`.
- `coq/` and the TypeScript component are untouched.
