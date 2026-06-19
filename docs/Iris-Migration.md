# Iris Backend — Remaining Gaps

Status: June 2026
Source: gap analysis vs IMP bespoke backend, 13 failing tests in current suite.

See `docs/iris-migration-plan.md` for the detailed phased closure plan and
design decisions. This document is the checklist of what remains to reach
feature parity with the IMP backend.

## Current State

- `SnakeletLang.v`: 0 Admitted
- `SnakeletWp.v`: 0 Admitted
- 31 of 44 Iris tests pass; 13 fail
- IMP tests: unchanged

## Gap Checklist

### 1. Failing Tests (13 tests)

Pipeline integration and proof generation regressions. Call chains,
transparent helpers, ANF of calls-in-expressions, branches with calls,
heap+loop+call combined, and SMT axiom slots all fail. Fix before
adding new features.

- [ ] pipeline: opaque call chain
- [ ] pipeline: transparent helper call
- [ ] pipeline: call-in-expression ANF
- [ ] pipeline: call in branch
- [ ] pipeline: heap + loop + call combined
- [ ] pipeline: SMT axiom via Python
- [ ] proof_gen: chain opaque/transparent/opaque
- [ ] proof_gen: chain with arithmetic
- [ ] proof_gen: parametric chain with theorem pre
- [ ] proof_gen: case split with calls in branches
- [ ] proof_gen: case split branch calls linear post
- [ ] proof_gen: SMT axiom slot
- [ ] proof_gen: multi-arg opaque spec

### 2. Data Structures (Phase 5)

`SDictGet.to_coq()`, `SDictSet.to_coq()` implemented.
List/dict/set contract props compile to `True` (no real Iris Prop).

- [x] `SDictGet.to_coq()` — snakelet_ir.py:270
- [x] `SDictSet.to_coq()` — snakelet_ir.py:282
- [x] List append/dict insert WP lemmas in SnakeletWp.v (dict get/set)
- [x] Lowering: Python dict ops -> SnakeletLang (SDictGet/SDictSet via iris_lowerer)
- [x] Coq: dict_lookup/insert, PureDictGet/Set pure_step, wp_dict_get/set lemmas
- [x] Pipeline: ANF + param subst + validation + proof gen for dict nodes
- [ ] Contract compilation: `len`, `index`, `dict_len`, `tuple`, `dict`, `set`, `list_eq` -> real Iris Props
- [ ] List append/set add WP lemmas

### 3. Frame Conditions (Phase 3)

The CALL path handles result correctness but not frame enforcement via
separation logic. IMP has clobber + per-callee frame lemmas.

- [ ] Extend `SApp` with reads/writes field sets
- [ ] Thread `l ↦ v` resources through the stage generator
- [ ] Multi-call bodies with disjoint memory

### 4. Exceptions (Phase 4)

- [x] `STry.to_coq()` — snakelet_ir.py:259
- [ ] `SFork.to_coq()` — snakelet_ir.py:226
- [ ] `SFAA.to_coq()` — snakelet_ir.py:237
- [x] `wp_raise` WP lemma (already existed in SnakeletWp.v)
- [x] `wp_try` WP lemma (wp_try_val already existed in SnakeletWp.v)
- [x] Pipeline: _subst_params, _validate_ops, _anf, param detection
- [x] Proof gen stages: raise_val for SRaise, try_val for STry
- [x] Unary minus `-x` lowered as `0 - x` for variable operands
- [x] Tests: test_raise_proved, test_try_except_proved

### 5. Typed Operations (Phase 6)

- [ ] `mod` and `div` in supported op set (iris_pipeline.py:52)
- [ ] String operations: concat, equality, `len`, `String.index`
- [ ] Float operations: `VFloat` binops in SnakeletLang
- [ ] `isinstance`: tag-based dispatch
- [ ] `None`/`NoneType`: `LitNone` value, `is None` comparison
- [ ] Boolean short-circuit: `and`/`or` → `If` expansion

### 6. Pydantic / Shape IR (Phase 9)

- [ ] Connect `shape_ir.py` to Iris field-resource model
- [ ] `is_valid` constraint expansion in Iris
- [ ] `isinstance` dispatch for Pydantic models

### 7. Pipeline Integration (Phase 7)

- [ ] Content-based dispatch: route supported functions to Iris, fall back to IMP
- [ ] Cache: per-stage hashing, recompile only changed stages
- [ ] SMT escalation: export residual obligation → axiom → regenerate stage
- [ ] LLM oracle: feed structured residual goal from coq-lsp

### 8. Contract Vocabulary (Phase 8)

List/dict/set quantifiers (`all()`, `any()`, `sum()`) compile to
`True` in `contract_ir_iris.py`. Need proper Iris Prop compilation
after data types exist.

- [ ] `all()`/`any()` over lists → real Iris Props
- [ ] `sum()` over lists → real Iris Props
- [ ] `re_match` → real Iris Props

### 9. Ghost State

IMP has file system, concurrency control, SQL ghosts. Iris has only
`ghost_map` for the call table.

- [ ] File system ghost state
- [ ] Concurrency control ghost state

### 10. Break/Continue in Loops

- [ ] Support in Iris lowerer for while loops

## Gaps Already Closed

- Heap operations: `SLoad.to_coq()`, `SStore.to_coq()`, `SAlloc.to_coq()` implemented
- Pure arithmetic + conditionals
- Opaque/transparent calls
- For-loops over list literals
- Symbolic while loops with invariants (iLoeb pattern)
- Multi-assert contracts
- ANF normalization
