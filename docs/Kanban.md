# Kanban

## Iris Backend — Done

### Core language
- [x] `wp_while_inv_gen` — Qed (heap-counter while with side condition)
- [x] `wp_while_str` — Qed (string-guard while, Hoare rule)
- [x] `call_opaque_pred` + ghost threading — Z-witness extraction
- [x] `OpaqueSpec.post_pred / post_witness / ghost_vars / ghost_wits`
- [x] Per-branch ghost_close — observer verified for non-branched subcontracts
- [x] `OpaqueTerm` — unknown calls in contracts → True (trusted)
- [x] IntEnum resolution — linter + lowering + multi-file via `build_shape_registry`
- [x] Docstring contract wiring — `axiomander:` blocks feed Iris pipeline
- [x] Multi-post ensures — conjoined under shared existential
- [x] `->` → `implies()` rewrite, `owns`/`frame`/`preserves` parsing
- [x] `finish_pure` — handles string existentials, set membership, bool, int, float, sn_val
- [x] Ghost_close rz-shadowing fix — unique hypothesis names per callee

### IMP retirement features
- [x] String param types — annotation-driven `LitString` vs `LitInt` vs `sn_val`
- [x] String indexing — `StrIndexOp` binop via `String.substring`
- [x] String operations — `StartsWithOp` / `EndsWithOp` (real, not mock)
- [x] Dict indexing — `d[k]` with KeyError semantics via `MkKeyErrOp`
- [x] Dict/field projection — `dict_lookup`, `DictGetOp`, `model_field_Z`
- [x] List append SSA — value-type lists rebind via `SLet` after append
- [x] Set operations — `InOp`, `SetAddOp`, `UnionOp`, `InterOp` in Coq + lowering
- [x] Float arithmetic — `LitFloat`, coercion (int+float→float), `z2float`
- [x] Float contracts — `PrimFloat.leb`/`ltb`/`eqb`, `_FLOAT_PARAMS` global
- [x] Boolean contracts — `BoolLit` preserved (not collapsed to IntLit), bool result kind
- [x] Pydantic field access — `field_access` via `DictGetIntOp`, shape registry type detection
- [x] Structured result fields — `result.x` in postconditions via `model_field_Z v "x"`
- [x] Symbolic while loops — single-variable (`i < n`) heap promotion
- [x] Multi-variable while loops — all assigned locals heap-promoted (`i`, `acc`)
- [x] Loop invariant verification — invariant premises in per-loop lemmas
- [x] Loop invariant SMT discharge — `Expr.to_smt()` → cvc4/z3, no regex/string parsing
- [x] Score: 79+ tests (74 Iris + 5 fulfil_order), 0 failures

### Proof engineering
- [x] Staged proof output — per-stage IDs in tactic comments
- [x] Residual goal capture — `capture_residual()` produces `.v` fragment with `Show.`
- [x] `nia` / `sfirstorder` / `lia` tactic ladder in finish_pure and invariant subgoals
- [x] `length_app` rewrite for list-length simplification

### Architecture: Expr AST → to_coq/to_smt (late compilation)
- [x] `WhileInv.invariant_exprs` stores `contract_ir.Expr` nodes, not pre-compiled strings
- [x] `invariants` @property compiles lazily via `iris_prop()`
- [x] `collect_inv_obligations` calls `expr.to_smt()` directly — no regex, no string parsing
- [x] Variable renaming via AST walk (`rename_expr`), not `re.sub`
- [x] `z → z+1` substitution via `subst_z_plus_one` AST walk

### fulfil_order
- [x] 3 subcontracts (do_validate_fraud, do_capture_payment, do_commit_order) + composition

---

## Remaining Gaps

### Language completeness
- [x] **`is_valid` field constraints** — `ge`/`le`/`gt`/`lt`
  via model_field_Z projection works at IR level.  `_is_valid` handler emits
  `model_field_Z` comparisons from shape registry.  Negative tests demonstrate
  constraint violations are caught.  Coq side uses trusted `model_field_Z` axiom.
- [ ] **String lower/upper for Unicode** — ASCII case-mapping is done
  (Coq Fixpoint via `Ascii.N_of_ascii` byte arithmetic). SMT string theory
  (cvc4/z3) lacks `str.to_lower`/`str.to_upper`.  Full Unicode would require
  UCD tables or codepoint-aware `LitUnicode : list Z -> sn_val`.
- [x] **`d.get(k, default)`** — real body (If(k in d, d[k], default))
  works at IR level.  Now handles BOTH concrete (literal) and opaque dicts
  via `dict_has` Definition (returns bool via LitBool wrapper, not raw
  match).  `case_bool` destructs all booleans including literals; `focus_redex`
  added so If is visible through Let bindings.  5 tests pass (hit, miss,
  opaque, dict_set basic + expression).
- [x] **`dict_set` lowering** — `TupleOp` binop constructs LitTuple [v1; v2]
  from two values.  `dict_set` transparent helper uses `SBinOp("tuple", ...)`
  instead of SLit tuple (which can't reference variables).  2 tests pass.

### Verification strength
- [x] **Body--invariant coupling** — resolved.  `subst_body_update` replaces `a_i → a_i + (z+1)`
  in the invariant conclusion, fixing the bug where the SMT axiom used old `a_0`.  Per-loop
  lemmas use `smt_ax_N; [exact Hz | exact Hcond | exact HinvN]`.  Call-site invariant
  blocks use `nia|lia|simpl; reflexivity`.
- [x] **Invariant SMT discharge** — resolved.  `collect_inv_obligations` walks WhileInv nodes,
  compiles via `expr.to_smt()` (no regex).  `discharge_inv_obligations` + `_smt_check`
  sends to cvc4/z3 (QF_NIA).  Fallback to `nia|sfirstorder|lia` for non-division cases.
- [x] **Complex invariants with division** — `acc == i*(i+1)//2` compiles to `Z.div`.
  SMT handles it in the obligation; contract-level Postcondition uses `Z.div` via
  `nia`.  Current tests pass.  For robustness, rewrite contracts as `2*acc == i*(i+1)`.

### IMP backend (removed — moot)

### Infrastructure
- [x] **Fault isolation** — `verify_iris_safe()` wraps `python_to_iris_proof` + `coqc`
  in try/except, returns `GoalStatus`. One crashing function does not cascade.
- [x] **CLI entry point** — `main()` with `--function`, `--json`, `--quiet`, toolchain
  guard, exit codes 0/1/2. Parity with pipeline.py's CLI.
- [x] **Dafny-flavored JSON schema** — `PipelineReport.to_json()` produces standard
  schema via existing `reporting.py` types. `verify_iris_safe` returns `GoalStatus`;
  `run_iris_pipeline` returns `PipelineReport`.
- [x] **Failure classification** — `_classify_iris_failure` runs `classify_failure` +
  `action_guidance` on unproved goals. Loop detection via AST walk.
- [x] **CLI dispatch** — `verify-function` / `check-function` / `verify-changed` /
  `verify-impacted` / `explain-cache` still route to IMP backend. When IMP is
  retired, these must dispatch to Iris. Currently users must know to use the
  separate `iris-verify` command.
  → Resolved: `check-function` and `verify-function` now route to Iris by
  default. `--backend imp` flag preserved for fallback. `verify-changed`
  and `verify-impacted` remain IMP-only (need Iris incremental support).
- [x] **Caching + incremental verification** — Iris re-verifies everything from
  scratch on every run. IMP tracks per-function hashes (body, contracts, callees)
  and only re-verifies what changed. Iris needs hash-based caching with
  transitive caller invalidation.
  → Resolved: file-based cache in `.axiomander/cache/entries/iris_*.json`.
  `verify-function` uses `use_cache=True`. Hash keys body + contracts.
  Cold run ~2s, warm run <10ms.
- [x] **frame-report command** — the `frame-report` tool function exists in
  `mcp_server.py` but is not wired as a typer CLI command. It was removed
  during the main PR. Needs to be re-added (works for both backends).
  → Resolved: typer command added. Shows pre/post conditions and
  frame variables per function.

### Nice-to-have
- [ ] **Existential quantifier** — `exists e in EventBus.emitted` (domain-specific)
- [ ] **For loops over dicts** — `for k, v in d.items()`
- [ ] **isinstance type dispatch** — tag-based branching
- [ ] **Multiple loop VCGs** — currently only outermost/last loop gets VCG (IMP)
- [x] **Implication postconditions** — `ensures result == "fulfilled" -> Orders.row(...).status == "fulfilled" and ...`
  parsed by docstring_contracts + compiled to Coq (X -> Y /\ Z) via
  contract_ir_iris.  `finish_pure` now handles implication goals.
  Single-line `ensures: expr -> ...` and multi-line `ensures expr ->` continuation
  both work.  See py/examples/doc_implies_ok.py for verified example.
- [x] **Resource ownership** — `owns queue_item: OrderQueue.item(order_id)` etc.
  displayed in frame-report with validation.  Deeper IR integration
  (resource footpoint compilation) remains future work.
- [x] **Frame declarations** — `frame: may_modify / must_not_modify / may_emit / must_not_emit`
  parsed, displayed, and validated against actual body writes in
  frame-report command.

### Deferred
- [ ] History model — `exactly_once_domain_effect`
- [ ] Event log ghost theory — `may_emit` / `must_not_emit`
- [ ] Global invariants — `preserves GlobalInvariant.*`
- [x] **Frame declarations** — `frame: may_modify / must_not_modify / may_emit / must_not_emit`
  parsed by docstring_contracts, validated against actual body writes
  in frame-report command.
- [ ] Old-value capture — `old(x)` in docstring ensures
- [ ] Termination measures
- [ ] CI — GitHub Action
