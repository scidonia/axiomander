# fix: make CI workflow pass end-to-end (fix/11-ci-submodule-https)

## Summary

This branch fixes six cascading CI failures that prevented the GitHub Actions
workflow from completing. Each commit addresses one root cause discovered by
reading the actual CI error output. The final state: `dune build` succeeds,
`pytest py/tests/` passes, and the full workflow runs without errors.

---

## Commits & root causes fixed

### 1 — `8a85de0` Submodule HTTPS URL + recursive checkout

**Symptom:** `git submodule update --init --recursive` failed in CI because
`vendor/rocq-piler` was registered with an SSH URL (`git@github.com:…`).
GitHub Actions runners have no SSH key for private repos.

**Fix:**
- `.gitmodules` — changed `vendor/rocq-piler` URL from `git@github.com:…`
  to `https://github.com/…`
- `.github/workflows/ci.yml` — added `submodules: recursive` to the
  `actions/checkout@v4` step so submodules are fetched automatically

---

### 2 — `b9fbdb7` Replace non-existent apt package with opam-based CoqHammer deps

**Symptom:** `sudo apt-get install -y libcoq-hammer-dev` failed with
`E: Unable to locate package libcoq-hammer-dev` — that package does not exist
in Ubuntu's apt repositories.

**Fix:**
- `.github/workflows/ci.yml` — removed the non-existent apt package; added
  two `opam pin` + `opam install --deps-only .` steps that build
  `coq-hammer-tactics` and `coq-hammer` from the already-vendored
  `vendor/coqhammer` submodule (the same path used by `make setup-coq` locally)
- `axiomander.opam` — added `coq-hammer` and `coq-hammer-tactics` to the
  `depends:` field so `opam install --deps-only .` resolves them

---

### 3 — `63cf430` Install full Python deps via `uv sync`

**Symptom:** `pytest` collection failed with `ModuleNotFoundError: pydantic`
because the "Install Python deps" step only ran `pip install pytest`, leaving
all runtime dependencies (pydantic, networkx, etc.) uninstalled.

**Fix:**
- `.github/workflows/ci.yml` — replaced `pip install pytest` with
  `uv sync --extra testgen` (installs the full dependency set from `uv.lock`
  including all extras needed by the test suite)
- Added `astral-sh/setup-uv@v5` step before the install step

---

### 4 — `1abb12d` Fix Iris/Coq load-path and dune build

**Symptom:** `dune build` failed with:
```
Cannot find a physical path bound to logical path proofmode
with prefix iris.proofmode
```
Two root causes:
1. `coq/dune` was missing the `(theories iris)` dependency, so Coq couldn't
   find the Iris `proofmode` library at build time.
2. `dune-project` was missing the `(using coq 0.9)` stanza, causing dune to
   ignore the Coq build rules entirely.

**Fix:**
- `coq/dune` — added `(theories iris)` to the `(coq.theory …)` stanza; also
  added the full set of Iris/stdpp theory dependencies (`iris.bi`,
  `iris.proofmode`, `iris.heap_lang`, `stdpp`, `stdpp.fin_maps`)
- `dune-project` — added `(using coq 0.9)` language stanza
- `py/axiomander/oracle/iris_pipeline.py` — fixed the `coqc` invocation to
  pass `-R` load-path flags for both the local `coq/` directory and the
  installed Iris/stdpp libraries; added `eval $(opam env)` environment
  injection so the subprocess sees the correct `COQPATH`
- `py/tests/test_iris_proof_gen.py`, `py/tests/test_iris_python_pipeline.py`
  — updated test fixtures to match the corrected pipeline interface

---

### 5 — `60be2d6` Use `rocq-*` opam package names for Rocq 9.x

**Symptom:** `opam install --deps-only .` failed with "unknown package
`coq-iris`" because Rocq 9.x renamed all opam packages from `coq-*` to
`rocq-*`.

**Fix:**
- `axiomander.opam` — renamed `coq-iris` → `rocq-iris` and
  `coq-stdpp` → `rocq-stdpp` in the `depends:` field

---

### 6 — `6904d9c` Register `coq-released` at switch-creation time via `opam-repositories`

**Symptom:** Even with the correct `rocq-*` package names, `opam install`
still failed with "unknown package" because `ocaml/setup-ocaml@v3` only
registers the default `opam.ocaml.org` repository in the CI switch.
`rocq-iris` and `rocq-stdpp` live in the **Coq/Rocq opam overlay**
(`https://coq.inria.fr/opam/released`), which was absent.

**First attempt (insufficient):** Adding a post-hoc `opam repo add … --all-switches`
step after `setup-ocaml` ran did not reliably make the repository visible to the
switch — `setup-ocaml@v3` caches the opam root and switch at creation time, so
repositories added afterward are not reflected in the cached package index.

**Fix:**
- `.github/workflows/ci.yml` — removed the standalone "Add coq-released" step;
  instead, registered `coq-released` **at switch-creation time** using the
  `opam-repositories:` input of `ocaml/setup-ocaml@v3`:
  ```yaml
  - name: Setup OCaml
    uses: ocaml/setup-ocaml@v3
    with:
      ocaml-compiler: "5.2"
      opam-repositories: |
        coq-released: https://coq.inria.fr/opam/released
        default: https://opam.ocaml.org
  ```
  Listing `coq-released` first mirrors the local switch (rank 1) and guarantees
  `rocq-iris`, `rocq-stdpp`, and all other Rocq packages are resolvable before
  any `opam install` or `opam pin` step runs.

---

## Files changed

| File | Change |
|---|---|
| `.github/workflows/ci.yml` | Submodule checkout; replace apt with opam; uv sync; add coq-released repo |
| `.gitmodules` | SSH → HTTPS URL for `vendor/rocq-piler` |
| `axiomander.opam` | Add CoqHammer deps; rename `coq-*` → `rocq-*` |
| `coq/dune` | Add `(theories iris …)` and `(using coq 0.9)` |
| `dune-project` | Add `(using coq 0.9)` language stanza |
| `py/axiomander/oracle/iris_pipeline.py` | Fix `coqc` load-path flags; inject opam env |
| `py/axiomander/oracle/mcp_server.py` | Minor: silence `notifications/initialized` |
| `py/tests/test_iris_proof_gen.py` | Update fixtures for corrected pipeline |
| `py/tests/test_iris_python_pipeline.py` | Update fixtures for corrected pipeline |

---

## How to verify locally

```bash
# From the axiomander repo root:
eval $(opam env)
dune build
uv run python -m pytest py/tests/ -v
```
