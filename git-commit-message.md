The root cause was that `ocaml/setup-ocaml@v3` only registers the default `opam.ocaml.org` repository in the CI switch. The packages `rocq-iris` and `rocq-stdpp` live in the **Coq/Rocq opam overlay** (`https://coq.inria.fr/opam/released`), which is absent from the CI switch — hence "unknown package" when `opam install --deps-only .` tries to resolve them.

The fix adds a new step in `.github/workflows/ci.yml` immediately before "Install Coq deps":

```yaml
- name: Add coq-released opam repository
  run: opam repo add coq-released https://coq.inria.fr/opam/released --all-switches
```

This mirrors the local setup (where `coq-released` is repo #1 in the switch) and makes `rocq-iris`, `rocq-stdpp`, and any other Rocq packages resolvable before `opam install -y --deps-only .` runs.