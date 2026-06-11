# Axiomander Iris Migration — Development Plan

Status: Draft — June 2026
Branch: `feature/iris-backend-prototype`

## Goal

Replace the IMP-based WP calculus with the Iris separation-logic framework as
Axiomander's primary verification backend.  The Iris backend already has a
proven WP calculus (0 Admitted in Lang and Wp), a syntax-directed staged proof
generator, an end-to-end Python pipeline using the shared ContractLinter, and
a set of stage tactics that produce classifiable, independently-failing
obligations.  This document defines the migration phases, the feature-gap
closure order, and the design decisions that govern the transition.

## Architecture

The Iris path composes four layers, all distinct from the IMP pipeline:

```
Python source (*.py)
    │
    ├─ [Contract extraction]        ContractLinter (shared) → contract_ir →
    │                                contract_ir_iris → pure Coq Props
    │
    ├─ [Body lowering]              PyIR → iris_lowerer → SnakeletIR
    │
    ├─ [Normalization]              Parameter substitution, ANF
    │
    └─ [Proof generation]           iris_proof_gen → staged .v file
         │
         └─ coqc / SMT escalation   (per-stage failure → SMT → axiom →
                                     regenerate call stage)
```

**Key design decisions already settled:**

- **Stage tactics, not monoliths.** The pipeline emits one stage tactic per
  IR node (`call_opaque`, `call_transparent`, `pure_step`, `case_bool`,
  `finish_pure`). Each stage can fail independently with a named,
  classifiable error. The proof script IS the trace.

- **Syntax-directed, not interactive.** Stage selection is determined by
  IR syntax + table entry kind. The generator needs no symbolic execution
  and no knowledge of intermediate values — the Coq stage tactics
  extract everything from the goal at proof time.

- **SMT escalation lives at the stage boundary.** When `snakelet_solve_pre`
  cannot crack a precondition (nonlinear arithmetic, strings), the pipeline
  exports to SMT and regenerates the stage as `call_opaque_pre (exact
  smt_ax_N)`.  Pure postcondition failures at `finish_pure` are also SMT
  candidates.

- **ContractLinter is shared.** Both IMP and Iris pipelines parse assert
  expressions through the same `ContractLinter` → `contract_ir.Expr` path.
  Compilation to Iris Props lives in `contract_ir_iris.py` (a separate
  dispatch, not a method on the shared IR nodes, to avoid IMP/Iris
  compilation drift).

- **Contracts are Python `assert` statements.** Zero imports, zero
  decorators.  Positional classification: leading asserts = precondition,
  assert immediately before the final return over the returned variable =
  postcondition.

## Contract Language — Composition and Separation

Contracts are plain Python expressions parsed by Python's `ast` module.
The ContractLinter produces `contract_ir.Expr` nodes from these Python
fragments.

**Default composition is separating conjunction (∗).**  Multiple assert
statements composing a precondition or postcondition are joined with `∗`,
the native Iris BI connective.  Pure nodes are injected as `⌜pure_prop⌝`.
This is uniform (one composition rule), scales to concurrency (invariants
and atomic updates compose via `∗`), and is no heavier than `∧` for the
current pure-integer fragment (because `⌜P⌝ ∗ ⌜Q⌝ ≡ ⌜P ∧ Q⌝`).

**User-facing pure vocabulary (compiled via contract_ir_iris):**

| Python expression | Coq Prop |
|---|---|
| `assert x >= 1` | `⌜x >= 1⌝` |
| `assert min(a, b) <= c` | `⌜Z.min a b <= c⌝` |
| `assert implies(A, B)` | `⌜(A -> B)⌝` |
| `assert a >= 0 and b <= 10` | `⌜(a >= 0) /\ (b <= 10)⌝` |
| `assert all(x != i for i in range(0, 10))` | `⌜forall i : Z, 0 <= i < 10 -> x <> i⌝` |
| `assert s == "hello"` | `⌜String.eqb s "hello" = true⌝` |
| `assert s.re_match("[0-9]+")` | `⌜re_match s "[0-9]+"⌝` |
| `assert owns(x)` (future) | `x ↦ ...` (resource, no `⌜⌝`) |

**SMT bridge:** The same `contract_ir.Expr` nodes can produce SMT-LIB via
`.to_smt()`.  Obligations the mechanical ladder (lia) cannot solve are
exported, and UNSAT results become `Axiom smt_ax_N : ...` in the
generated `.v` file, referenced by a regenerated call stage.

## Feature Gap and Phased Closure

The IMP pipeline handles ~75 test categories (loops, heap mutations,
frame conditions, exceptions, strings, floats, dicts, sets, isinstance,
Pydantic, quantifiers, ghost state).  Iris currently handles ~5
(pure arithmetic, conditionals, opaque/transparent calls).  Each missing
feature follows the same engineering pattern: head step → determinant
lemma → WP lemma → stage tactic → lowering → test.

### Phase 1: Heap Operations (week 1)

**What:** `wp_load`, `wp_store`, `wp_alloc` already Qed in `SnakeletWp.v`.
The block is Python-side: `SLoad.to_coq()`, `SStore.to_coq()` raise
`NotImplementedError`.  Each needs `to_coq()` completed and a stage tactic
(already exist as the WP lemmas).

**Unlocks:** mutable state, dict/set mutations (SDictGet/SDictSet reuse
the same patterns).

### Phase 2: While/For Loops with Invariants (weeks 2–3)

**What:**
- **Coq:** A `wp_while` lemma for `While e body` with an invariant `I`.
  The WP loop rule: `I ⊢ WP body {{ v, I }}` gives `I ⊢ WP While e body
  {{ Φ }}`, plus the exit condition when the guard is false.  Standard
  Iris pattern adapted from `heap_lang`.
- **Lowering:** `iris_lowerer.py` rejects `PyWhile`/`PyFor`.  For-loops
  desugar to while loops (same pattern as `py_to_imp.py`).  Invariants
  come from the user's `assert` inside the loop body — already classified
  as "invariant" by the ContractLinter.
- **Proof generator:** A `loop_invariant` stage tactic taking the
  invariant as a `constr` argument (the only stage that genuinely needs a
  user-supplied argument — everything else derives from the goal).

**Unlocks:** ~13 test categories (while, for, break/continue, range
iteration, nested loops).

### Phase 3: Full CCall Frame Conditions (week 4)

**What:** The current `wp_call` handles correctness of the result but not
frame enforcement.  In Iris, frame conditions use separation logic: the
caller frames the callee's heap footprint; no `clobber`, no `forall x, ~In
x writes`.  The work is extending `SApp` with a reads/writes field set and
threading the `l ↦ v` resources through the stage generator.

**Unlocks:** multi-call bodies where calls share disjoint memory, ~5
frame-condition tests.

### Phase 4: Exception Handling (0.5 week)

**What:** `Raise`/`Try` head steps exist in SnakeletLang but no WP lemmas.
Iris encodes exceptional return in the postcondition (no outcome
discrimination).  `wp_raise` discharges the postcondition with the
exception value; `wp_try` branches.

**Unlocks:** ~3 exception tests.

### Phase 5: Data Structure Operations (weeks 5–6)

**What:** List, dict, and set mutations.  Each data type needs:
- **Coq:** WP lemmas (`ListAppend`, `DictSet`, `SetAdd`, etc.).  Each is
  a head step + determinant lemma + WP lemma following the `wp_store`
  pattern.
- **Lowering:** Complete `iris_lowerer.py` for Python data-structure
  operations → SnakeletLang operations.
- ~8 operations total, each ~1 day.

**Unlocks:** ~10 list/dict/set test categories.

### Phase 6: Typed Subset — Strings, Floats, isinstance, None (weeks 7–10)

**What:**
- **String operations:** concatenation, equality, `len`, `String.index`.
  Extend SnakeletLang's `binop_eval` for string ops.  ~1 week.
- **Float operations:** add `VFloat` binops to the supported fragment.
  ~1 week.
- **isinstance:** tag-based dispatch via `HeadCall` with type-tag
  arguments.  ~1 week.
- **None/NoneType:** add `LitNone` value, `is None` comparison.  ~0.5 week.
- **Boolean short-circuit:** lower `and`/`or` to `If` expansion.  ~0.5 week.

Each is a narrow extension following the same head-step pattern.

**Unlocks:** ~12 typed-operation test categories.

### Phase 7: Pipeline Integration (weeks 11–12)

**What:** Wire `python_to_iris_proof()` into `mcp_server.py::_verify_function()`.

- **Content-based dispatch:** detect which constructs a function uses;
  route to Iris path when all are supported, fall back to IMP otherwise.
- **Cache integration:** the staged proof hashes per-stage; recompile only
  changed stages.
- **SMT escalation:** when a stage fails at the mechanical ladder boundary,
  export the residual obligation via `smt_export`/`theory_smt` → emit axiom
  → regenerate stage.
- **Level 3 LLM:** the residual goal from a failed stage feeds the
  `langgraph_oracle` for Coq proof search — same pattern as the IMP
  escalation, but the goal arrives structured (tactic name + goal state
  from coq-lsp) rather than via stderr regex.
- **Docstring contracts:** `parse_axiomander_docstring()` already produces
  synthetic `ast.Assert` nodes that flow through the same ContractLinter
  pipeline.  The Iris path picks these up naturally once wired to
  `_verify_function`.

### Phase 8: SMT/Axiom Bridge for Advanced Contracts (week 12)

**What:** The `all()`, `any()`, `sum()`, `re_match` contract vocabulary
compiles through `contract_ir_iris` but list quantifiers and sum emit
`True` (phase 3 — need list/dict value-model support).  Once Phase 5
provides list/dict types in the body, these nodes get proper Iris Prop
compilation.  The SMT axiom emission for nonlinear/unprovable obligations
is already wired.

### Phase 9: Pydantic / Shape IR (weeks 13–14)

**What:** The IMP pipeline has full Pydantic model support (Shape IR →
flat field keys, `is_valid` constraint expansion, `isinstance` dispatch).
Iris handles field ownership through `l ↦ v` points-to; the shape
compilation is language-independent.  Mostly a lowering exercise
connecting `shape_ir.py` to the Iris field-resource model.

### Phase 10: Test Migration and Deprecation (ongoing, from Phase 1)

**What:** Each phase closure activates the corresponding `test_pipeline.py`
test categories for the Iris path.  The test runner runs both backends.
When an Iris-phase test passes, it gates out the IMP variant.  Deprecation
is complete when zero tests require the IMP path.  The IMP path is then
gated behind `--legacy-imp`.

## Migration Gating

During the migration period, both pipelines coexist.  The dispatch logic:

```python
# In _verify_function in mcp_server.py
if _iris_fragment_supported(fn_body):
    return _verify_iris(source, fn_name, table, ...)
else:
    return _verify_imp(source, fn_name, contracts, ...)  # existing path
```

`_iris_fragment_supported` checks for constructs still exclusive to IMP
and returns False if any are present.  Each phase removes a check.

## What Does NOT Change

- **ContractLinter.** Both paths share it.  IR compilation diverges only at the final
  rendering step (IMP `to_coq(scoped=True)` vs. Iris `contract_ir_iris.iris_prop()`).
- **SMT export.** `smt_export.py` and `theory_smt.py` operate on Coq goal
  strings — framework-agnostic.  The Iris path feeds them residual
  obligations from failed stages; the IMP path feeds them from `coqc`
  error dumps.  Same solvers, better-structured input on the Iris side.
- **LLM oracle.** `langgraph_oracle.py` receives goal state and attempts
  Coq proof search.  Works with either backend.
- **Cache.** The incremental hash cache tracks function body, contracts,
  and callee contracts.  Framework-agnostic.  Iris adds per-stage hashes
  for finer granularity but does not replace the function-level cache.

## Risks

| Risk | Mitigation |
|------|------------|
| Loop invariant discovery is hard for users | Keep the IMP invariant format (assert inside loop body); the `loop_invariant` stage takes the same expression |
| SnakeletLang's ectx is value-restricted on both binop sides → both-nonvalue binops are stuck | ANF normalization already in the pipeline; this is load-bearing |
| coq-lsp round-trip latency in the SMT/LLM escalation path | Batch coqc for mechanical stages; coq-lsp only for structured residual goals (same as IMP escalation today) |
| RegMatch.vo not in dune build (already removed) | Source-tree .vo managed alongside other Snakelet modules; test infra using `-R coq ""` |
| Dune build conflict for source-tree .vo files of modules in dune theory | Only Imp-theory modules in dune; Snakelet modules are standalone `-R coq ""` compiled — no conflict |

## Current State (June 2026)

- `SnakeletLang.v`: 0 Admitted (full Iris language)
- `SnakeletWp.v`: 0 Admitted (full WP calculus: binop, let, if, load, store,
  alloc, call-opaque, call-transparent)
- `SnakeletTactics.v`: stage tactic instruction set (call_opaque,
  call_transparent, pure_step, case_bool, finish_pure, call_opaque_pre)
- `SnakeletDemo.v`: 2 Admitted (intentional negative stubs), 16 Qed
- `iris_proof_gen.py`: syntax-directed staged proof generator
- `iris_pipeline.py`: end-to-end Python→Iris, using shared ContractLinter
- `contract_ir_iris.py`: contract_ir → Iris Prop compilation
- 86 tests pass (34 Iris-specific, 52 SnakeletLang extraction/eval)
- IMP pipeline: 100+ integration tests (unchanged)
- The Iris pipeline handles: pure integer arithmetic, conditionals, opaque
  calls (FunCtx via contract table), transparent call unfolding, ANF
  normalization, SMT axiom escalation slot, multi-assert contracts, the
  full integer+implies+min/max+forall/exists-range contract vocabulary.
