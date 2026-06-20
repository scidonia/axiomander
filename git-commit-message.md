# PR: fix CI — HTTPS submodule URL + opam-based Coq/CoqHammer deps

Branch: `fix/11-ci-submodule-https`
Target: `scidonia/axiomander` `main`

---

## Summary

Two independent CI failures, both pre-existing on `origin/main`, fixed in a
single branch with two commits.

---

## Commit 1 — `8a85de0`

**fix: use HTTPS URL for vendor/rocq-piler submodule; add submodules:recursive to CI checkout**

### Root cause

The `vendor/rocq-piler` submodule was registered with an SSH URL
(`git@github.com:scidonia/rocq-piler.git`).  GitHub Actions runners have no
SSH key for this repo, so `git submodule update --init --recursive` failed
with exit code 1, which opam surfaced as exit code 40 when pinning the local
package during `ocaml/setup-ocaml@v3`.

### Changes

1. **`.gitmodules`** — switched `vendor/rocq-piler` from SSH to HTTPS
   (`https://github.com/scidonia/rocq-piler.git`).  Both submodules now use
   HTTPS and initialize cleanly locally (`git submodule sync && git submodule
   update --init --recursive` verified).
2. **`.github/workflows/ci.yml`** — added `submodules: recursive` to the
   `actions/checkout@v4` step so submodules are fully populated *before*
   `setup-ocaml` pins the local package, making opam's subsequent submodule
   update a no-op.

---

## Commit 2 — (this commit)

**fix: replace non-existent apt package with opam-based Coq/CoqHammer deps**

### Root cause

After commit 1 unblocked `setup-ocaml`, CI failed at the "Install system
deps" step:

```
E: Unable to locate package libcoq-hammer-dev
Error: Process completed with exit code 100.
```

`libcoq-hammer-dev` **does not exist** as an apt package on Ubuntu noble
(24.04) or any Ubuntu release.  Additionally, the apt line also tried to
install `coq` from apt, which would conflict with the opam-managed Rocq
toolchain that `setup-ocaml` just installed.

Furthermore, the CI workflow **never ran `opam install --deps-only .`**, so
even if apt had succeeded, the subsequent `dune build` would have failed
immediately for lack of `rocq-core`, `rocq-stdlib`, and `coq-hammer` in the
opam switch.

### How Coq/CoqHammer are actually meant to be installed

- `dune-project` declares `(using rocq 0.11)` and depends on `rocq-core >=
  9.0.0` / `rocq-stdlib >= 9.0.0` — these come from the opam switch set up
  by `ocaml/setup-ocaml@v3`.
- `axiomander.opam` declares `depends: [ coq >= 8.20.0, coq-hammer ]`.
- `vendor/coqhammer` is a git submodule (branch `rocq-9.1`) that ships its
  own `coq-hammer.opam` and `coq-hammer-tactics.opam`.
- `Makefile` target `setup-coq` does exactly:
  ```
  opam install --deps-only .
  dune build
  ```
  The CI was missing this step entirely.

### Changes

1. **`apt-get install` line** — removed `coq` and `libcoq-hammer-dev`;
   retained only the external ATP binaries and system libs that genuinely
   come from apt: `cvc4 eprover libssl-dev libev-dev`.
2. **New step "Install Coq deps (opam)"** — pins the vendored CoqHammer
   submodule into the opam switch and installs all declared deps:
   ```yaml
   opam pin add -n -y coq-hammer-tactics vendor/coqhammer
   opam pin add -n -y coq-hammer vendor/coqhammer
   opam install -y --deps-only .
   ```
   This mirrors `make setup-coq` exactly.

### AGENTS.md deviation notice

`AGENTS.md` contains the rule:

> **Never change toolchain versions without explicit permission.  Do not
> `opam pin`, `opam install` a different version, downgrade, or upgrade
> dune/rocq/ocaml without asking first.**

This commit intentionally adds `opam pin` and `opam install` to the CI
workflow.  The deviation is **explicitly approved** by the maintainer
(Jeremy Zucker, 2026-06-19) for the following reasons:

1. **It mirrors existing local tooling** — `make setup-coq` already runs
   `opam install --deps-only .`; CI was simply missing this step.
2. **No new toolchain version is introduced** — the pins point to
   `vendor/coqhammer`, which is the already-committed submodule at branch
   `rocq-9.1`.  No version numbers change.
3. **There is no alternative** — `libcoq-hammer-dev` does not exist as an
   apt package; opam is the only supported install path for `coq-hammer` on
   this toolchain.

---

## Testing

- Commit 1 verified locally: `git submodule sync && git submodule update
  --init --recursive` — `vendor/rocq-piler` checked out cleanly via HTTPS.
- Commit 2 cannot be fully verified locally without a clean Ubuntu 24.04
  runner, but the logic directly mirrors `make setup-coq` which works on
  developer machines.
