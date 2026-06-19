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
- [x] Score: 75 tests (70 Iris + 5 fulfil_order), 0 failures

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
- [ ] **`is_shape` / `is_valid`** — model field constraints (`Field(ge=0)`) compile to `True`
  placeholder. Need to generate type-guard and constraint conjunctions from shape registry.
- [ ] **String `lower` / `upper`** — mock (copy identity). Need ASCII case-mapping
  `Fixpoint` in Coq (`to_lower`, `to_upper` on `Ascii.ascii`).
- [ ] **`d.get(k, default)`** — mock (returns default). Need real `dict_lookup` with
  fallback semantics.
- [ ] **`DictUpdateOp` / dict assignment** — `d[k] = v` functional update over `LitDict`.

### Verification strength
- [ ] **Body–invariant coupling** — the body stages (heap ops) and the SMT obligation
  are generated independently. They agree because both derive from the same source,
  but there's no formal Coq check that the body actually implements the SMT-verified
  update. Currently: trust that the lowerer + promotion produce consistent body/obligation.
- [ ] **Invariant update proof for non-SMT cases** — when `smt_ax_N` is not generated
  (SMT timeout or no solver), the invariant subgoal falls back to `nia|sfirstorder|lia`
  which cannot handle `Z.div`. The obligation is left open.
- [ ] **Complex invariants with division in contracts** — `acc == i*(i+1)//2` compiles
  to `Z.div` in Coq Props. `lia`/`nia` can't handle it. SMT handles it in the obligation
  but the contract-level Postcondition still uses `Z.div`. Write `2*acc == i*(i+1)` instead.

### IMP backend (pre-existing, not Iris)
- [ ] `set_count` — set operations inside while loops fail VCG
- [ ] `in_vocab` — set membership inside while loops fails VCG

### Nice-to-have
- [ ] **Existential quantifier** — `exists e in EventBus.emitted` (domain-specific)
- [ ] **For loops over dicts** — `for k, v in d.items()`
- [ ] **isinstance type dispatch** — tag-based branching
- [ ] **Multiple loop VCGs** — currently only outermost/last loop gets VCG (IMP)

### Deferred
- [ ] History model — `exactly_once_domain_effect`
- [ ] Event log ghost theory — `may_emit` / `must_not_emit`
- [ ] Global invariants — `preserves GlobalInvariant.*`
- [ ] Frame lemmas from `frame:` declarations
- [ ] Old-value capture — `old(x)` in docstring ensures
- [ ] Termination measures
- [ ] CI — GitHub Action
