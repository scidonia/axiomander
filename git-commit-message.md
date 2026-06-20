The CI build failure was caused by the "Install Python deps" step in `.github/workflows/ci.yml` only running `pip install pytest`, which left `pydantic` (and all other runtime dependencies) uninstalled. Since tests import the axiomander package directly via `PYTHONPATH=py`, the missing `pydantic` caused a `ModuleNotFoundError` at collection time.

**Two changes made to the axiomander repo:**

1. **`.github/workflows/ci.yml`** — Added a `Setup uv` step (`astral-sh/setup-uv@v5`) and replaced `pip install pytest` with `uv sync --extra testgen`. This installs the full locked dependency set (including `pydantic`, `z3-solver`, the git-sourced `coqpyt`, and `hypothesis`). The "Run tests" step now uses `uv run python -m pytest` instead of bare `python -m pytest`.

2. **`py/axiomander/oracle/iris_pipeline.py:653`** — Changed the docstring to a raw string (`r"""..."""`) to clear the `SyntaxWarning: invalid escape sequence '\ '` that appeared in the same CI run.

Verified locally: `uv sync --extra testgen` succeeds and both previously-failing test modules now collect 152 tests with no errors.