# Axiomander Iris Backend — Current State

Branch: `feature/iris-backend-prototype`

The full migration plan from the IMP WP calculus to Iris as primary backend
is in [`docs/iris-migration-plan.md`](docs/iris-migration-plan.md).

## What's Done

### SnakeletLang.v — 0 Admitted
- Full WP Iris language: `sn_val`, `sn_expr`, `sn_state`, ectx items (10 Ki constructors), `fill`/`fill_item`/`fill_K`
- `LanguageCtx (fill_item Ki)` fully Qed (fill_step_inv, fill_not_val, to_val_pure_step/to_val_head_step)
- `fill_item_no_val_inj` Qed (100-case explicit induction)
- `fill_K_val` Qed
- `LanguageCtx (fill_K K)` Qed via standalone `fill_step_list` + `fill_step_inv_list` lemmas
- **Unified function table with opaque AND transparent calls:**
  `Inductive fun_entry := FunSpec (pre : list sn_val → Prop) (post : list sn_val → sn_val → Prop) | FunDef (params : list string) (body : sn_expr)`
  and
  ```coq
  Class FunCtx := {
    fun_entries : string → option fun_entry;
    fun_specs_total : ∀ f pre post vs,
      fun_entries f = Some (FunSpec pre post) → pre vs → ∃ v, post vs v;
  }.
  ```
  with `#[export] Instance default_fun_ctx ... | 100` (empty, low priority so user
  instances win).  One name maps to at most one entry, so spec-driven and
  unfolding semantics are mutually exclusive *by construction*.
  **Contract discipline:** opaque calls only step when [pre args] holds —
  calling outside the precondition is *stuck*, so WP (NotStuck) forces the
  caller to establish it.  [fun_specs_total] is the callee-side
  total-correctness promise (pre implies some post-satisfying result),
  discharged once per table when implementations are verified against their
  contracts; this is what lets [wp_call] derive reducibility from [pre]
  alone, keeping call-site obligations modular.
- **Language parameterized by the table the right way:** `head_step`, `prim_step`,
  the mixin, `snakelet_lang`, and both `LanguageCtx` instances live in
  `Section with_fun_ctx` under `Context `{FC : FunCtx}`.  The parameter is
  *typeclass-implicit*, so `snakelet_lang : ∀ {FC}, language` stays canonical and the
  WP notation stays clean — canonical-structure resolution leaves `FC` as an evar
  that typeclass search then solves at each use site.  (The earlier attempt with an
  explicit `Variable fun_specs` broke notation; that was the wrong axis.)
- Call head steps:
  - `HeadCallSpec : fun_entries f = Some (FunSpec pre post) → pre vs → post vs v → head_step (Call f (map Val vs)) σ (Val v) σ []`
  - `HeadCallUnfold : fun_entries f = Some (FunDef params body) → length vs = length params → head_step (Call f (map Val vs)) σ (subst_list params vs body) σ []`
- `subst_list` (left-to-right capture-free substitution of value args)
- `map_Val_inj : map Val vs1 = map Val vs2 → vs1 = vs2`

### SnakeletWp.v — 0 Admitted
- Section has `Context `{FC : FunCtx}` — all WP lemmas parametric in the table
- Full WP calculus Qed: `wp_binop`, `wp_if_true`, `wp_if_false`, `wp_let`,
  `wp_alloc`, `wp_load`, `wp_store`, **`wp_call`**, **`wp_call_unfold`**
- `prim_call_inv` (replaces the unsound `prim_call_det`): the conclusion is a
  disjunction over the two step sources; since a post is a *relation*, the
  opaque branch existentially quantifies the result:
  `prim_step (Call f (map Val vs)) σ κ e2 σ2 efs → κ=[] ∧ σ2=σ ∧ efs=[] ∧
   ((∃ pre post w, fun_entries f = Some (FunSpec pre post) ∧ pre vs ∧ post vs w ∧ e2 = Val w) ∨
    (∃ params body, fun_entries f = Some (FunDef params body) ∧ length vs = length params ∧ e2 = subst_list params vs body))`
- `wp_call s E f pre post vs Φ : fun_entries f = Some (FunSpec pre post) → pre vs →
   (∀ w, ⌜post vs w⌝ -∗ Φ w) -∗ WP Call f (map Val vs) @ s; E {{ Φ }}`
  — the modular contract rule: caller proves *pre*, receives *post*;
  reducibility comes from `fun_specs_total`, not from a call-site witness.
- `wp_call_unfold s E f params body vs Φ : fun_entries f = Some (FunDef params body) →
   length vs = length params → ▷ WP subst_list params vs body @ s; E {{ Φ }} -∗
   WP Call f (map Val vs) @ s; E {{ Φ }}`
  — transparent calls; the call β-reduces to the substituted body.
  Cross-branches in both proofs die by `congruence` on the single table lookup.
  Both follow the `wp_lift_step` pattern of `wp_alloc` (no value subgoal arises).
- `into_val_val` is `\`{FunCtx}`-parametric (otherwise it would bake the
  default table into the language index and `wp_value` would fail under demo specs)
- `gen_heap` setup, `snakelet_pures` Ltac

### SnakeletDemo.v — 2 Admitted (both intentional negative tests), 16 Qed
- Pure expression demos, parametric contracts (add/mul for any Z), wp_bind demo, max/abs
- `demo_table` written with `String.eqb` chains (NOT match on string literals)
  so `demo_table_total` can case-split on the booleans; `demo_fun_ctx` packs
  table + totality proof
- Table: ["square"]/["double"] opaque with `int1_pre` (arity/typing constraint),
  ["decr"] opaque with *nontrivial* pre (`1 ≤ x`), ["twice"] transparent
  (`FunDef ["x"] (Var "x" + Var "x")`)
- `call_square`, `call_double`, `call_decr` Qed via `wp_call` (caller proves pre)
- `call_twice_transparent` Qed via `wp_call_unfold` (parametric in the argument:
  unfolds the body, then `wp_binop`)
- `call_unknown_stuck` Qed: positively proves `¬ reducible (Call "nonexistent" ...) σ`
- `call_twice_wrong_arity_stuck` Qed: a transparent call with wrong arity is stuck
- `call_decr_pre_violation_stuck` Qed: calling outside the precondition is stuck —
  the contract is enforced, not assumed
- **`call_chain`, `call_chain_mixed` Qed by `snakelet_auto.` alone**: a body
  chaining square (opaque) → twice (transparent) → decr (opaque, pre 1≤50),
  and a chain mixing calls with pure arithmetic — zero manual steps
- **`call_chain_staged` Qed by explicit stage script** (the generated-proof
  form): `call_opaque "square". pure_step. call_transparent "twice".
  pure_step. pure_step. call_opaque "decr". finish_pure.`
- **`abs_staged` Qed with `case_bool` path fork**: symbolic `x <? 0`
  conditional, branch constraints flow into `finish_pure`'s lia
- Negative check (probe): `call_opaque "double"` on a square-call goal fails
  with "goal redex is not a call to the given function"
- Gotcha: `[#5]` inside `%S` collides with stdpp's vector notation `[# ...]` —
  write `[Val (LitInt 5)]` for call argument lists
- Proof note: `simpl in Hentry` does NOT reduce `demo_table "f"`; pin the entry
  with `assert (fun_entries "f" = Some ...) by reflexivity` and rewrite
- Note: WP lemma `@`-applications take one extra implicit now (`_ _ _ _ s E`)

### SnakeletTactics.v — clean
- `reshape_expr` Ltac + `wp_bind` tactic ported from heap_lang
- **Stage tactics — the instruction set for generated proofs.**  The
  pipeline emits proof scripts as sequences of these (syntax-directed:
  IR node category → stage tactic), one line per stage; each stage fails
  independently with a named, classifiable error.  The script IS the trace.
  - `call_opaque` / `call_opaque "f"` — spec'd call: auto-focus Let-bound
    call (`snakelet_focus_call`, ANF assumption), table lookup via
    `eval hnf`, pre via `snakelet_solve_pre`, post substitution via
    `snakelet_intro_post`.  Optional name argument asserts the expected
    redex (drift detection; fails with named error on mismatch).
  - `call_transparent` / `call_transparent "f"` — definition call: unfolds
    to the substituted body.
  - `pure_step` — one pure reduction (let-with-value, binop-with-values,
    literal if).
  - `case_bool` — path fork on a symbolic boolean; the `eqn:` hypothesis is
    the path constraint; refuses literal conditions.  The *generator*
    decides split points; `snakelet_auto` never splits.
  - `finish_pure` — terminal stage; `snakelet_pure_hyps` converts boolean
    path constraints (Z.ltb/leb/eqb = true/false) to Props for `lia`;
    ladder: reflexivity | lia | done | eexists;split;[refl|lia].
  - SMT escalation contract: obligations `snakelet_solve_pre` cannot solve
    are exported to SMT by the pipeline; resulting axioms are supplied
    explicitly in the generated script.
- **`snakelet_auto`** — interactive composition of the same instruction set
  (demos/manual use only; generated output never calls the monolith).
  Loop of `snakelet_step`:
  - pure WP steps (`snakelet_pure_step` from Wp; let/binop/if with values)
  - `snakelet_call_step`: matches `Call f args`, strips `Val`s off `args`
    (`strip_vals`), computes the table entry with `eval hnf` (preserving the
    named pre/post for readable side goals), then applies `wp_call`
    (reflexivity + `snakelet_solve_pre` + intro result, `subst`) or
    `wp_call_unfold` (reflexivity ×2 + `iNext`)
  - `wp_bind` to focus a redex in evaluation position
  - `wp_value'` for terminal values
  Ends with `iPureIntro; first [reflexivity|lia|done]`.
- `snakelet_solve_pre`: discharges simple pre shapes
  (`∃ x, args = [...]` with optional `∧` linear-arith side conditions);
  extensible with more branches
- `snakelet_simpl`: `simpl; try (unfold of_val)` — the generic `wp_bind`
  continuation reintroduces `of_val`, which `simpl` will NOT unfold; without
  this the syntactic matches stall
- Failure behavior: if a sub-step fails (nondeterministic post, unprovable
  pre), the whole step rolls back and the goal is left at the call —
  earlier progress kept

### Tests: 52/52 pass

## Blockers — all three RESOLVED

1. **`prim_call_det`** — was unsound as stated for nondeterministic spec relations
   (nothing forces the step result to equal the given `v`).  Replaced by
   `prim_call_inv` (existential form), Qed.  The old proof also did
   `inversion H0` on `pure_step x x'` *before* destructing `K`, so `x` was
   still opaque and all 5 pure constructors survived — destruct `K` first.
2. **`wp_call`** — derived from `prim_call_inv` using the same `wp_lift_step`
   skeleton as `wp_alloc`; `to_val (Call ...) = None` is discharged by `done`,
   so the problematic value subgoal never appears.
3. **`FunSpecs` override** — the instance was *baked into the `head_step`
   inductive at definition time* (`@fun_specs default_fun_specs` in `HeadCall`),
   so no priority trick could ever work.  Fixed by typeclass-implicit section
   parameterization (see above); default instance demoted to priority 100.

### iris_proof_gen.py — syntax-directed staged proof generator (Phase 2)
- `py/axiomander/oracle/iris_proof_gen.py`: walks SnakeletIR + a `FunTable`
  (`OpaqueSpec(args, side, result)` | `TransparentDef(params, body)`)
  and emits a complete `.v`: SMT axioms, generated FunCtx table
  (pre/post defs, String.eqb-chain table, mechanically-proven totality
  lemma, instance), theorem, staged proof script.
- **No symbolic execution**: stage *selection* is IR syntax + table entry
  kind; stage *semantics* live in the Coq tactics which extract everything
  from the goal.  One stage per IR node; one `pure_step` per reduction
  (focusing is goal-driven inside `pure_step`, which now auto-wp_binds
  non-value Let/BinOp/If redexes — never bind plumbing in the script).
- Forward/SP style: case splits duplicate continuation stages per arm
  (CPS walk, `k()` per path); branch hypotheses are path constraints.
- SMT slot: `call_opaque_pre (<tactic>)` (Coq side) + `axioms` /
  `pre_overrides` (Python side) — nonlinear pre discharged via
  `exact (smt_ax_0 n)`; tested both directions (with axiom proves,
  without axiom fails).
- ANF enforced at generation: non-value call args -> IrisGenError.
- `snakelet_ir.py`: `to_coq()` completed for SVar/SLet/SIf/SApp/SReturn/
  SSeq (SnakeletLang constructors); heap/exception nodes raise
  NotImplementedError (phase 3).
- `test_iris_proof_gen.py`: 15 end-to-end tests (generate ->
  coqc): chains, parametric pre flow, nested binop trees, case splits
  (incl. calls in branches), SMT slot, negative tests (wrong post, pre
  violation, unknown callee, non-ANF), empty table, multi-arg specs.

### contract_ir_iris.py — Iris Prop compilation for contract IR (NEW)
- `py/axiomander/oracle/contract_ir_iris.py`: pure-function dispatch `iris_prop(node,
  param_set, post_var)` compiles `contract_ir.Expr` nodes to plain Coq Props
  for Iris pre/postconditions.  No IMP state model (no `s "x"%string`,
  `asZ`, `hget`).  Parameters are bare `Z` variables.
- Convenience: `compile_precondition(node)` and `compile_postcondition(node,
  ret_var)` — the latter wraps as `exists z : Z, v = LitInt z /\ P[ret:=z]`,
  matching `finish_pure`'s ladder exactly.
- All integer/Z logic nodes compile natively: Var, IntLit, BoolLit, BinOp
  (+, -, *, /, mod, =, <=, <, >, >=, <>), Logical (and/or/not), MinExpr
  (Z.min), MaxExpr (Z.max), ImpliesExpr (->), SliceLenExpr (end - start).
- Quantifiers over ranges compile: AllExpr/AnyExpr with lower/upper produce
  `forall/exists (i : Z), lo <= i < hi ->/` `P`.  Over lists → `True` (p3).
- String ops: BinOp(=) on StrLitExpr → `String.eqb ... = true`;
  StringEqualsExpr, StringContainsExpr (String.index),
  ReMatchExpr (re_match) all compile.
- RecursorExpr compiles: `forallb (fun item => ...) xs` as-is.
- Phase-3 nodes (list/dict/set/index operations, Pydantic shapes,
  exceptions, resource ownership) compile to `True` — they need
  SnakeletLang value-model support.  When a full contract with these
  operations needs to be checked, the existing `.to_smt()` path through
  `smt_export`/`theory_smt` provides the SMT coverage.
- **Why a separate module, not a method on contract_ir.Expr:**
  `contract_ir.py` is the single source of truth for the IMP pipeline's
  `to_coq(scoped=...)` and the shared `to_smt()`.  Adding `to_coq_iris()`
  as a method would couple the Iris compilation to the IMP/SMT node
  classes and risk drift when one compilation path is updated.  A
  standalone dispatch avoids method pollution and keeps the two
  compilation paths independently maintainable.

### iris_pipeline.py — now uses ContractLinter + contract_ir_iris
- `extract_contracts(source, fn_node)`: works on raw `ast.FunctionDef`.
  Leading `assert`s → `compile_precondition` via ContractLinter.
  Final `assert` before `return` → `compile_postcondition` via
  ContractLinter.  ContractLinter handles the full Python contract
  vocabulary (implies, min, max, forall, string ops, etc.).
- `_fold` skips `PyAssert` nodes (contracts are extracted at the AST
  level, not lowered to SnakeletIR).
- Parameter substitution (`_subst_params`), ANF, and validation unchanged.
- Tests: 4 new strong-contract tests (ranged bounds, min/max in contracts,
  implies compound, multi-predicate preconditions with compound post).
  19 pipeline end-to-end tests total from Python source.

### Bugs found by the end-to-end exercise (all fixed)
- `iris_lowerer._lower_compare` used stale PyCompare shape
  (`ops`/`comparators` lists vs current `op`/`left`/`right`).
- `wp_bind` tactic iterated context frames innermost-first; the wp_bind
  lemma must be applied outermost-first (single-frame demos never
  exposed it).
- `reshape_expr`'s `BinOpRCtx` branch passed an expr where the ctx item
  wants a value (SnakeletLang's ectx is value-restricted on both binop
  sides — a binop with two non-value operands is operationally STUCK;
  hence ANF in the pipeline).
- `pure_step`/`snakelet_focus_call`/named call variants now locate the
  redex via `reshape_expr` (deep Let nests from ANF hoisting).
- `snakelet_solve_pre`: bare `repeat eexists` overreaches — `eexists`
  applies to ANY single-constructor inductive (splits conjunctions,
  unify-solves equalities), leaving a bare side-condition that the
  subsequent `split` chokes on.  Fixed: `hnf; repeat lazymatch goal with
  |- @ex _ _ => eexists end` then dispatch.

### Location-keyed heap tactics (robust generated proofs)
- **Problem:** `iApply (wp_store with "[$]")` resolves the premise
  `l ↦ ?v` against the spatial context BEFORE unifying `l` with the goal
  expression's location — with multiple cells it grabs the wrong one.
  Name-based selection (emit "Ha"/"Hb" from the generator) is brittle:
  substitution erases `Var "x"`, fresh Coq names drift.
- **Fix (heap_lang style): environment-form tactic lemmas** in
  SnakeletWp.v — `tac_wp_load`/`tac_wp_store` state load/store against
  the proof-mode environment with `envs_lookup i Δ = Some (false, l ↦ v)`
  where `l` is concrete (extracted from the goal by `reshape_expr`).
  `iAssumptionCore` finds the hypothesis by unification on the location;
  `envs_simple_replace` updates it in place (name preserved across store).
- `rev_ectx`: reshape_expr accumulates ectx innermost-first but `fill_K`
  is head-outermost — reverse before passing K to the tac lemmas
  (single-frame contexts mask this bug; If∘BinOp nests expose it).
- `snakelet_popvals`: pops leftover value-WP layers
  (`WP Val v {{w, WP ...}}`) from nested wp_bind continuations; prefixed
  to every stage tactic, so scripts never contain `iApply wp_value'`
  plumbing and are insensitive to bind-layer stacking.
- `snakelet_simpl` now includes `cbn` (simpl does not reduce concrete
  arithmetic inside value constructors: LitInt (0+1) stays unreduced).
- **Result: generated scripts are bare stage sequences** — no hypothesis
  names, no locations, no cbn, no value-pops.  `two_cells_staged` and
  `two_cells_staged_swapped` close with the IDENTICAL script; the
  counting while loop is a uniform 7-stage block per iteration:
  `loop_unfold. heap_load. pure_step. pure_step. heap_load. pure_step.
  heap_store. pure_step.`
- heap_alloc names its cell anonymously (`iIntros (l) "?"`); nothing
  downstream refers to it by name.

### While loops + heap through the full pipeline (Phase 2b complete)
- `SWhile` IR node; `iris_lowerer._lower_call` intercepts heap builtins:
  `ref(v)` -> SAlloc, `load(c)` -> SLoad, `store(c, v)` -> SStore
  (c must be a variable name).  `_fold` handles `PyWhile` (lowers to
  `SLet "_" (SWhile cond body) rest`) and `PyExprStmt`.
- **Loop generation (concrete-state loops):** the generator emits ONE
  `repeat (<iteration block>)` stage — loop_unfold + cond stages +
  select-branch pure_step + body stages + bind-";;" pure_step, joined
  with `;` — followed by the explicit exit iteration + continuation.
  Each repeat iteration is atomic (Ltac backtracking): on the exit pass
  the block fails partway (body stages can't fire after the false
  branch) and rolls back, leaving the goal at the exit unfolding.
  Symbolic-bound loops fail the first block (pure_step refuses symbolic
  conditions) -> repeat exits with zero unrollings -> failure lands at
  the exit stages: graceful, classifiable, no divergence.
- **`fail 1` -> `fail` in stage-tactic inner continuations**: level-1
  failures escape `repeat`, breaking the exit-iteration rollback.  All
  stage tactics now fail at level 0 so repeat catches and rolls back.
- ANF: while conditions are re-evaluated per iteration so nothing may
  be hoisted out of the While; supported cond shape is a binop over
  atoms with at most one Load (value-restricted ectx).  Body is
  ANF-normalized normally (hoists stay inside the loop).
- End-to-end tests from Python source: heap roundtrip, counting loop,
  **combined opaque call + heap + while + arithmetic + contracts**
  (`mixed(x)`: square(x) + loop-to-3 + post x*x+3), wrong-post negative,
  symbolic-bound negative.

### Mechanical-ladder boundary notes (empirical, this Coq version)
- `lia` FAILS on `x * x >= 0` (no hypotheses) and `1 <= n * n + 1` —
  these need the SMT slot (or nia).
- `lia` PROVES `0 < x -> x * x >= 0` — hypothesis products work, so
  path constraints from `case_bool` are load-bearing for nonlinear posts.
- `binop_eval` comparisons produce `bool_decide (...) = true/false`
  path constraints (NOT `Z.ltb`); `snakelet_pure_hyps` handles both.
- `snakelet_solve_pre` ladder: `done | by repeat eexists |
  by (repeat eexists; split; [done|lia])` (multi-arg needs `repeat`).

### Phase 7: Pipeline integration — mcp_server dispatch (COMPLETE)

`_try_iris_backend` in `mcp_server.py` wires `python_to_iris_proof` into
the main verification path.  The dispatch is **backwards-compatible**
and requires zero configuration changes:

1. `_verify_function` calls `_try_iris_backend` right after the contract
   lint check and *before* the IMP body generation.
2. On Iris success (coqc returns 0) → returns PROVED (level1, iris)
   immediately, short-circuiting the IMP path.
3. On IrisGenError (body uses unsupported constructs: isinstance,
   strings, lists, dicts, sets, Pydantic, etc.) → returns None, falling
   through to IMP.
4. On Iris compilation failure → also returns None, falling through to
   IMP (the Iris path never blocks the IMP fallback).

Behavior verified across the full test suite (224 tests):
- Pure arithmetic, heap ops, while loops, call chains → Iris proves
- String ops, set ops, isinstance, Pydantic → falls through to IMP
- Iris compilation failure → gracefully falls through to IMP
- IMP baseline unchanged (130/132 pass; 2 pre-existing set-operation failures)

## Key Files
- `coq/SnakeletLang.v` — Language definition, ectx, `fill`
- `coq/SnakeletWp.v` — WP calculus, all WP lemmas, `prim_*_det` lemmas
- `coq/SnakeletDemo.v` — Demos and examples
- `coq/SnakeletTactics.v` — `reshape_expr`, `wp_bind`, stage tactics
- `coq/SnakeletEval.v` — Fuel evaluator
- `py/axiomander/oracle/snakelet_ir.py` — SnakeletIR + to_coq (SnakeletLang syntax)
- `py/axiomander/oracle/iris_proof_gen.py` — staged proof generator
- `test_iris_proof_gen.py` — 15 generator end-to-end tests
- `test_snakelet_rocq.py` — 24 extraction tests
- `test_snakelet_conservative.py` — 28 conservative tests

## Build Commands
```bash
eval $(opam env)
coqc -R coq "" coq/SnakeletLang.v
coqc -R coq "" coq/SnakeletWp.v
coqc -R coq "" coq/SnakeletDemo.v
uv run pytest test_snakelet_rocq.py test_snakelet_conservative.py -q
```
