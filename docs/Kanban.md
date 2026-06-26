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

### Required for fulfil_order

These clauses from the full `contract.py` docstring are not yet verified.
Each needs new infrastructure — none existed in IMP or any prior backend.

- [x] **Existential quantifier** — `any(P(i) for i in range(N))` for small ranges (N<=5)
  expands to disjunction `P(0) \/ P(1) \/ ... \/ P(N-1)`.  Larger ranges produce
  `exists i, lo <= i < hi /\ P(i)`.  finish_pure handles \/ branches via nia.
- [ ] **Domain-specific predicates** — `no_lost_inventory(Order(order_id))`
- [ ] **History model** — `exactly_once_domain_effect(order_id)`: forall histories, count(successful_fulfilments) <= 1
- [ ] **Event log ghost theory** — `may_emit` / `must_not_emit` frame declarations
- [ ] **Global invariants** — `preserves GlobalInvariant.*` (3 items)
- [ ] **Resource ownership verification** — `owns queue_item / order_row / payment_auth / stock` compiled to Iris resource preconditions (currently displayed but rejected by verifier)
- [ ] **Old-value capture** — `old(x)` in docstring ensures (parsed but not compiled)

### Nice-to-have
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
- [x] **Termination measures** — D2 measured recursion (WP-11) + `while` user
      variant (WP-13) in the fluid-lowerer phase 2.
- [x] **Super compiler** — partial evaluation over λ_A contract expressions.
      Evaluate literal lists, small-range forall/exists, and constant-fold
      arithmetic before lowering.  Reuses `snakelet_eval.py` as the oracle.
      37 tests pass; integrated behind `supercompile_contracts=True` flag.
      Replaces contracts only when result is a literal boolean; otherwise
      emits supercompiled definitions alongside original.
- [ ] **Reflection-adequacy theorem** — prove `R(t) ⇝* lit(⟦t⟧_E)` in Coq.
      The theorem that the fluid-lowerer's Coq term always reduces to the
      same value as the executable semantics (theory §2.3).  Closes the
      TCB gap between trusted Python→IR lowering and kernel-checked Coq.
- [x] **CI** — GitHub Action. Fixed in 9b98d03: HTTPS submodule, coq-released
      opam repo, rocq-iris/rocq-stdpp/coq-hammer deps, pydantic+hypothesis,
      PYTHONPATH fix.

### Fluid lowerer — `R : lambda_A^tot -> CoqTerm` (reflection-first)

Design at [`docs/fluid-lowerer-design.md`](fluid-lowerer-design.md);
theory at [`docs/fluid-contract-language-theory.md`](fluid-contract-language-theory.md).

A single, total, type-directed function `lower(node, ctx) -> CoqTerm` that
subsumes `contract_ir_iris.iris_prop` + per-node `to_coq(...)` emitters into
one principled recursion over an explicit type environment.  Carries the
totality judgment `Gamma |- t : tau (down)`; nodes outside the fragment are
**rejected** with a diagnostic, never silently mistranslated.

Key design decisions:
- **Type-directed coercions** — comparison form `= true`, float wrapping, string
  equality are chosen from the *inferred type* of subterms, not from positional
  position (replaces `z_scope` flag).
- **Explicit immutable `LowerCtx`** — no module globals (replaces `_LIST_MODEL`,
  `_POST_BOUND`, `_FLOAT_PARAMS`, `_STRING_PARAMS`, `_BOOL_PARAMS`).
- **Reuse `contract_linter` front-end** (AST -> IR stays as-is); replace the
  IR -> Coq back-end.
- **Value-model closure:** `index/dict_len/dict_count/sum/tuple/dict/set/list_eq`
  (currently stubbed to `"True"`) lowered through `LitList/LitTuple/LitDict/LitSet`.

#### Phase 1 — core bounded-recursor lowerer (D0)

- [x] **WP-0 — Module scaffold + types** (S).  `fluid_lowering.py`: `Ty`,
      `CoqTerm`, `FluidLowerError`, `LowerCtx`.  No lowering yet.
- [x] **WP-1 — Scalar core** (M).  `var/int/bool/strlit/float/binop/logical/
      implies/min/max/slice_len` clauses.  Byte-for-byte parity with `iris_prop`
      on the existing scalar corpus; positional `z_scope` replaced by
      type-directed coercion.
- [x] **WP-2 — Bounded recursors** (M).  `all`/`any` over list & range;
      `sum(1 for x in xs if p)` via `countb`.  Closes the current `"True"` stub
      for list quantifiers.  Predicate body lowered via `lower` (not the
      string-based `_compile_comprehension_filter`).
- [x] **WP-3 — Totality gate + diagnostics** (S).  Reject: unknown call,
      self-recursive predicate, unbounded quantifier over non-range/non-list
      domain, untyped variable.  Each → `FluidLowerError` with construct name.
- [x] **WP-4 — Value-model closure** (L).  Immutable structures:
      `LenExpr`/`IndexExpr` over `LitList`; `list_eq`; `tuple`/`set`/`dict`
      literals; `dict_len`/`dict_count` via dict model.  May require small Coq
      lemmas (`nth`/`length` over `LitList`) in `ListPredicates.v`.
- [x] **WP-5 — Pre/postcondition wrappers** (S).  `compile_precondition_fluid`,
      `compile_postcondition_fluid` using inferred result type for existential
      binder/constructor (replaces `_result_value_kind` heuristic).
- [x] **WP-6 — Pipeline wiring behind a flag** (M).  `AXIOMANDER_FLUID=1` env
      or `Contracts` flag.  Default stays legacy until WP-1..5 reach parity.
- [x] **WP-7 — Cutover + delete legacy** (M).  Flip default.  Delete `iris_prop`
      `_placeholder` paths, per-node `to_coq(scoped=...)`, string-based
      `_compile_comprehension_filter`.  `predicate_lowering.Recursor` enum kept
      or inlined.
- [x] **WP-8 — Adequacy harness** (M).  Property test: compare `snakelet_eval`
      vs `vm_compute` lowered Coq term on random (value, predicate) pairs.
      Translation validation (theory §7), short of a Coq-verified `R`.

#### Phase 2 — recursive and loop predicates (D1/D2)

See [`docs/fluid-lowerer-design.md` §9](fluid-lowerer-design.md#9-recursive-and-loop-predicates-d1d2).

- [x] **WP-9 — `classify_recursion` + `PredicateDef`** (M).  AST walk:
      `NONREC` / `STRUCTURAL(arg)` / `MEASURED(expr)` / `REJECT(reason)`.
      Call sites lower to application of the emitted definition name.
- [x] **WP-10 — Slice-to-match reassociation** (L).  Normalize `xs[1:]`,
      `xs[0]` recursion → `match xs with [] | x :: rest` so Coq's guard checker
      accepts the emitted `Fixpoint`.  Partial + honest: returns `None` if no
      subterm can be exposed → reclassify as MEASURED/REJECT.
- [x] **WP-11 — Emit `Fixpoint` (D1) / `Equations` (D2)** (L).  D1: emit
      guarded `Fixpoint` → kernel acceptance *is* the proof.  D2: emit
      `Equations`/`Program Fixpoint` + route decrease obligations to the 3-tier
      prover; reject on failure.
- [x] **WP-12 — Loop predicate → recursor normalization** (M).  Imperative
      `for x in xs:` body that accumulates a boolean/count → `forallb`/
      `existsb`/`countb` (D0 recursors).  Replaces `detect_loop_pattern` dead
      code.
- [x] **WP-13 — `while` user variant** (L).  Generalize `wp_while_str`
      (guard-falsification special case) to a user `decreases` variant
      decreasing in `<` on `N`.  WP-side decrease obligation.

### Predicate lifting — legacy (to be retired)

The pattern-matcher (`predicate_lowering.py`) is the wrong foundation
(string-templated Coq, can't compose, never checks output).  It is superseded
by the fluid lowerer above.  Only the `Recursor` enum is still referenced
(`contract_linter.py:386`); all other code (`detect_loop_pattern`,
`_py_expr_to_coq`, `_extract_lambda`) has zero live callers.

- [x] **Delete** `predicate_lowering.py` dead code (after WP-7 cutover).

### Translation gap — verify or validate the lowerer

Highest-value theoretical investment (see comparative-assessment §3.1).
The Python→IR lowerer is trusted; "Coq is the trust base" is only true below
the IR boundary.

- [ ] **Translation validation** — check each lowering instance against a
      reference semantics (cheaper than full verification; CompCert-style).
- [ ] **OR verified extraction** — extract the lowerer from a Coq definition.

### Dual search — simultaneous proof + refutation at Level 3

Plan at [`docs/dual-search-refutation.md`](dual-search-refutation.md).
Turns "could not prove, retry" into "this contract is false; here is the
input that breaks it; here is the fix" — with a kernel-checked disproof.
Concrete counterexamples are provable in Coq by `vm_compute; discriminate`,
so refutations are *sound*, not heuristic SMT models.

- [ ] **Step 1 — disproof emitter** (`refutation.py`): given a witness, emit
      `Lemma ..._refuted : ~ O. intros H. specialize (H c). vm_compute in H.
      discriminate.` and check with coqc.
- [ ] **Step 2 — refuter lane**: `property_test_gen` returns the first failing
      input; validate via `snakelet_eval` (fast, no Coq) before certifying.
- [ ] **Step 3 — race harness**: prover and refuter race a shared deadline at
      Level 3; first kernel-checked result wins → VERIFIED / REFUTED / UNKNOWN.
- [ ] **Step 4 — grounded LLM explanation**: on REFUTED, feed witness + trace
      to the LLM for a diagnosis + minimal fix.  LLM narrates a kernel-checked
      fact (cannot hallucinate the failure).
- [ ] **Step 5 — reporting**: populate `ProofLevel.COUNTEREXAMPLE` from the
      refuter (today only SMT does); show witness + trace + diagnosis.

---

## Self-verification — Contracts on Axiomander's own code

The goal: fully characterize the behaviour of axiomander's own decision
functions with axiomander contracts.  Contracts must be *complete* — every
possible input must have a specified output.  No `result >= 0`-style weak bounds.

### Verified (Level 1)

- [x] **`implies(antecedent, consequent) -> bool`** — truth table: `(not A) or C`
  (`contract_runtime.py:25`)
- [x] **`_spec_is_proved(level: int) -> int`** — all 5 input levels mapped
  (`reporting.py:255`)
- [x] **`_spec_classify_failure(...) -> int`** — all 4 branches + default
  (`reporting.py:278`)
- [x] **`_spec_outcome_for(...) -> int`** — all 4 branches covering
  COUNTEREXAMPLE/VERIFIED/ERROR/UNPROVED (`reporting.py:317`)

### Contract gaps in `reporting.py`

These functions have incomplete or missing contracts in the live source.
The ideal complete contract is described; most require verifier features
that don't exist yet (see "Verifier Contracts Needed" below).

> **Progress:** Scalar specs (int-encoded decision logic) verified for all
> four functions.  The real functions need field-access lowering (#1, #2),
> string-substring matching (#3), and comprehension lowering (#4).

- [x] **`GoalStatus.is_proved() -> bool`** — already has a complete contract
      (3 cases covering all 6 ProofLevel values).  Scalar spec `_spec_is_proved`
      verified.  Real method needs `self.level` field-access lowering.
      (`reporting.py:92`)

- [x] **`_outcome_for(goal: GoalStatus) -> GoalOutcome`** — no contract existed.
      Scalar spec `_spec_outcome_for` added and verified (4 branches).
      Real function needs `goal.level` / `goal.error_detail` field-access
      lowering.  Contract vocabulary: `not`, `and` with negation, enum refs
      all working.  (`reporting.py:48`)

- [x] **`classify_failure(goal_name, error, has_loop) -> Action`** — body proves
      (Level 1).  Contract verified.  `close_case_contradiction` tactic
      handles `case_bool` Hcond decomposition in `finish_pure`.
      (`reporting.py:208`)

- [x] **`build_report(source_file, goals, elapsed_total_ms) -> PipelineReport`**
      — contract compiles via `countb (fun g => Z.leb 2 g) M_goals`.  Body needs
      for-loop lowering for the comprehension.  Scalar spec `_spec_build_report`
      verified (proved ≤ total invariant).  (`reporting.py:367`)

### Contracts needed in other modules

- [x] **`_sha256(*parts: str) -> str`** — scalar spec `_spec_sha256_length`
      verified: always returns length 64.  Full body verification needs
      `hashlib.sha256()`/`update()`/`hexdigest()` opaque specs (future).
      (`cache.py:145`)

- [x] **`Obligation.coq_block -> str`** — scalar spec `_spec_coq_block_ending`
      verified (Qed vs Admitted dispatch).  Same logic as `_spec_is_proved`.
      (`obligations.py:64`)

### Verifier features needed to support these contracts

> **Note:** Most features are now built.  `not`, `str in str`, enum refs,
> `and`/`or` with `not`, and comprehension in contracts all work.

| Feature | Needed by | Status |
|---|---|---|
| `not` on booleans in contracts | `classify_failure`, `_outcome_for` | Done |
| `str in str` (substring check) | `classify_failure` | Done |
| Enum literals in contracts | `is_proved`, `_outcome_for` | Done |
| `and`/`or` with `not` combinations | `classify_failure` | Done |
| Comprehension in contracts (`sum(...)`) | `build_report` | Done |
| Comprehension/for-loop in body | `build_report` | Remaining |
| Method calls in contracts (`g.is_proved()`) | `build_report` | Done (in comprehension) |
| `len(str)` in contracts | `_sha256`, `classify_failure` | Done |
