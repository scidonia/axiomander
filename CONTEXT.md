# Axiomander Iris Backend — Current State

Branch: `feature/iris-backend-prototype`

## What's Done

### SnakeletLang.v — 0 Admitted
- Full WP Iris language: `sn_val`, `sn_expr`, `sn_state`, ectx items (10 Ki constructors), `fill`/`fill_item`/`fill_K`
- `LanguageCtx (fill_item Ki)` fully Qed (fill_step_inv, fill_not_val, to_val_pure_step/to_val_head_step)
- `fill_item_no_val_inj` Qed (100-case explicit induction)
- `fill_K_val` Qed
- `LanguageCtx (fill_K K)` Qed via standalone `fill_step_list` + `fill_step_inv_list` lemmas
- **Unified function table with opaque AND transparent calls:**
  `Inductive fun_entry := FunSpec (spec : list sn_val → sn_val → Prop) | FunDef (params : list string) (body : sn_expr)`
  and `Class FunCtx := { fun_entries : string → option fun_entry }` with
  `#[export] Instance default_fun_ctx ... | 100` (empty, low priority so user
  instances win).  One name maps to at most one entry, so spec-driven and
  unfolding semantics are mutually exclusive *by construction* — no coherence
  side conditions on instances.
- **Language parameterized by the table the right way:** `head_step`, `prim_step`,
  the mixin, `snakelet_lang`, and both `LanguageCtx` instances live in
  `Section with_fun_ctx` under `Context `{FC : FunCtx}`.  The parameter is
  *typeclass-implicit*, so `snakelet_lang : ∀ {FC}, language` stays canonical and the
  WP notation stays clean — canonical-structure resolution leaves `FC` as an evar
  that typeclass search then solves at each use site.  (The earlier attempt with an
  explicit `Variable fun_specs` broke notation; that was the wrong axis.)
- Call head steps:
  - `HeadCallSpec : fun_entries f = Some (FunSpec spec) → spec vs v → head_step (Call f (map Val vs)) σ (Val v) σ []`
  - `HeadCallUnfold : fun_entries f = Some (FunDef params body) → length vs = length params → head_step (Call f (map Val vs)) σ (subst_list params vs body) σ []`
- `subst_list` (left-to-right capture-free substitution of value args)
- `map_Val_inj : map Val vs1 = map Val vs2 → vs1 = vs2`

### SnakeletWp.v — 0 Admitted
- Section has `Context `{FC : FunCtx}` — all WP lemmas parametric in the table
- Full WP calculus Qed: `wp_binop`, `wp_if_true`, `wp_if_false`, `wp_let`,
  `wp_alloc`, `wp_load`, `wp_store`, **`wp_call`**, **`wp_call_unfold`**
- `prim_call_inv` (replaces the unsound `prim_call_det`): the conclusion is a
  disjunction over the two step sources; since a spec is a *relation*, the
  opaque branch existentially quantifies the result:
  `prim_step (Call f (map Val vs)) σ κ e2 σ2 efs → κ=[] ∧ σ2=σ ∧ efs=[] ∧
   ((∃ spec w, fun_entries f = Some (FunSpec spec) ∧ spec vs w ∧ e2 = Val w) ∨
    (∃ params body, fun_entries f = Some (FunDef params body) ∧ length vs = length params ∧ e2 = subst_list params vs body))`
- `wp_call s E f spec vs v Φ : fun_entries f = Some (FunSpec spec) → spec vs v →
   (∀ w, ⌜spec vs w⌝ -∗ Φ w) -∗ WP Call f (map Val vs) @ s; E {{ Φ }}`
  — opaque calls; premises give reducibility, wand covers every admitted result.
- `wp_call_unfold s E f params body vs Φ : fun_entries f = Some (FunDef params body) →
   length vs = length params → ▷ WP subst_list params vs body @ s; E {{ Φ }} -∗
   WP Call f (map Val vs) @ s; E {{ Φ }}`
  — transparent calls; the call β-reduces to the substituted body.
  Cross-branches in both proofs die by `congruence` on the single table lookup.
  Both follow the `wp_lift_step` pattern of `wp_alloc` (no value subgoal arises).
- `into_val_val` is `\`{FunCtx}`-parametric (otherwise it would bake the
  default table into the language index and `wp_value` would fail under demo specs)
- `gen_heap` setup, `snakelet_pures` Ltac

### SnakeletDemo.v — 2 Admitted (both intentional negative tests), 14 Qed
- Pure expression demos, parametric contracts (add/mul for any Z), wp_bind demo, max/abs
- `demo_fun_ctx` instance genuinely overrides the default; table has
  ["square"]/["double"] opaque (named `square_spec`/`double_spec`) and
  ["twice"] transparent (`FunDef ["x"] (Var "x" + Var "x")`)
- `call_square`, `call_double` Qed via `wp_call`
- `call_twice_transparent` Qed via `wp_call_unfold` (parametric in the argument:
  unfolds the body, then `wp_binop`)
- `call_unknown_stuck` Qed: positively proves `¬ reducible (Call "nonexistent" ...) σ`
- `call_twice_wrong_arity_stuck` Qed: a transparent call with wrong arity is stuck
- Note: WP lemma `@`-applications take one extra implicit now (`_ _ _ _ s E`)

### SnakeletTactics.v — clean
- `reshape_expr` Ltac + `wp_bind` tactic ported from heap_lang

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

## Key Files
- `coq/SnakeletLang.v` — Language definition, ectx, `fill`
- `coq/SnakeletWp.v` — WP calculus, all WP lemmas, `prim_*_det` lemmas
- `coq/SnakeletDemo.v` — Demos and examples
- `coq/SnakeletTactics.v` — `reshape_expr`, `wp_bind`
- `coq/SnakeletEval.v` — Fuel evaluator
- `py/oracle/snakelet_ir.py` — Python → Coq IR translation
- `py/tests/test_snakelet_rocq.py` — 24 extraction tests
- `py/tests/test_snakelet_conservative.py` — 28 conservative tests

## Build Commands
```bash
eval $(opam env)
coqc -R coq "" coq/SnakeletLang.v
coqc -R coq "" coq/SnakeletWp.v
coqc -R coq "" coq/SnakeletDemo.v
PYTHONPATH=py uv run pytest py/tests/test_snakelet_rocq.py py/tests/test_snakelet_conservative.py -q
```
