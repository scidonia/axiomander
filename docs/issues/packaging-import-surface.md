# Axiomander cannot be installed as a Python dependency — packaging publishes a package named `py`

## What happens

Installing axiomander as a library (e.g. `pip install -e .`, or as a `uv` path/editable dependency from another project) produces an unusable import surface. After install, the only importable top-level package is literally `py`, so a consumer would have to write:

```python
from py.oracle.advisor import analyze_file
```

But all of axiomander's own code and tooling import it as:

```python
from oracle.advisor import analyze_file
```

The two are inconsistent, and neither matches a clean installed package.

## Why it happens

`pyproject.toml` declares:

```toml
[tool.setuptools.packages.find]
where = ["."]
```

With the source living in `py/oracle/`, `py/contracts/`, etc., setuptools discovers and installs `py` as the package name.

The codebase only works today because of two workarounds that mask the problem in-repo:

- a runtime `sys.path.insert(0, ".../axiomander/py")` hack in the entry scripts, and
- `PYTHONPATH=py` in the Makefile, MCP config, and docs.

Both make `oracle` and `contracts` importable as top-level names during development, but neither survives a real install.

## Evidence

- `pyproject.toml`: `[tool.setuptools.packages.find] where = ["."]`.
- Absolute imports assume top-level `oracle` / `contracts` (no `py.` prefix): `Makefile`, `mcp_config.json`, `README.md`, `AGENTS.md`, and ~17 absolute imports across `py/oracle/`.
- `py/proof_obligations.py` does `from py.wp_transformer import ...`, which only resolves when CWD is the repo root and breaks once installed.

## Impact

- Downstream projects cannot depend on axiomander without replicating the `sys.path` / `PYTHONPATH` hacks.
- `oracle` and `contracts` are extremely generic names; even if exposed as top-level packages, they would risk collisions in a shared venv.

## Constraint to keep in mind

Axiomander is a multi-language repo (Coq in `coq/`, a TypeScript component, Python in `py/`). Any fix should preserve `py/` as the Python source root rather than flattening everything to the repo root.
