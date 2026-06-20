The CI failure `Cannot find a physical path bound to logical path proofmode with prefix iris.proofmode` had two root causes:

1. **Missing opam dependencies**: `coq-iris` and `coq-stdpp` were not listed in `axiomander.opam`, so CI's `opam install --deps-only` never installed them. Fixed by adding both to the `depends:` block.

2. **Wrong logical prefix in compiled `.vo` files**: The `coq/dune` file used `(rocq.theory (name SCoqIris ...))` which baked `SCoqIris.` as the logical prefix into the compiled `.vo` files. But the `.v` source files use bare `Require Import SnakeletExnLang` (no prefix). Fixed by replacing the `rocq.theory` stanza for the Iris-dependent modules with individual `(rule ...)` stanzas that invoke `coqc` directly with `-R . ''` (empty logical prefix), matching what the source files expect.

3. **Test helpers bypassed `_coq_flags()`**: Both `test_iris_proof_gen.py` and `test_iris_python_pipeline.py` had their own `run_coqc()` helper that hardcoded `["coqc", "-R", str(COQ_ROOT), "", tmp]` pointing at the source `coq/` directory without iris/stdpp flags. Fixed by replacing both with `["coqc"] + _coq_flags() + [tmp]`.

Result: **198/198 tests pass** locally (up from 123/198).