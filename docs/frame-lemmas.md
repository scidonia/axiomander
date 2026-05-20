# Per-Callee Frame Lemma Generation

## Problem

The CCall WP rule produces a `forall x, ~ In x (target :: writes) -> ...` subgoal
that covers ALL variables. This general form causes two issues:

1. **WP term blowup** — each successive CCall nests the full WP expansion inside
   the previous call's postcondition, creating terms too large for `coqc`.
2. **Pattern matching fragility** — the `ls` coercion prevents compiled Ltac from
   matching the fully-reduced form, requiring fragile exclusions in `cbn`.

## Solution

Generate **per-callee, per-variable frame lemmas** at the Python IR level.
Instead of one huge `forall x, ...` goal, the proof uses many small
`apply lemma_name` calls — each trivial to prove via `wp_ccall_frame`.

```coq
(* Generated lemma: inc's writes are ["result"], caller's "a" is preserved *)
Lemma inc_frame_a : forall (s : state) (r : Z),
  ~ In "a" ("a2" :: "result" :: nil) ->
  lget s "a" = lget (clobber (lupd s "a2" (VZ r)) ("result" :: nil)) "a".
Proof. apply wp_ccall_frame. Qed.

(* In the caller's proof, instead of the forall subgoal we just apply: *)
  apply inc_frame_a.   (* proves "a" is unchanged across inc(a) *)
```

## Architecture

### Phase 1 — Collect frame variables (in `PyToImpLowerer`)

After lowering, walk the ImpIR tree. For each `ImpCCall` node:

```
callee_writes  ← from contract_map (callee's declared writes)
target         ← caller variable receiving return value
caller_locals  ← all String variables in scope at the call site

frame_vars = caller_locals \ (target :: mapped_writes)
```

Where `mapped_writes` maps callee parameter names to the caller's actual
argument variable names (if the arg is a simple variable).

Store `frame_vars` on the `ImpCCall` node (new `frame_vars: list[str]` field).

### Phase 2 — Generate lemmas (in `_generate_coq`)

For each `ImpCCall` in the body, for each `v` in `frame_vars`:

```coq
Lemma {callee}_frame_{v} : forall (s : state) (r : Z),
  ~ In "{v}" ("{target}" :: {writes_list}) ->
  lget s "{v}" = lget (clobber (lupd s "{target}" (VZ r)) {writes_list}) "{v}".
Proof. apply wp_ccall_frame. Qed.
```

Emit all lemmas in a `(* Frame lemmas *)` block between the body
definition and the main theorem (line ~2902 of `_generate_coq()`).

### Phase 3 — Use lemmas in proof

In the generated proof script, replace the frame condition subgoal with
`apply {callee}_frame_{v}` for each frame variable:

```
Proof.
  intros.
  wp_prove.
  apply inc_frame_a.
  apply inc_frame_b.
  ...
  lia.
Qed.
```

### Phase 4 — Deduplication

Cache lemmas by `(callee_name, variable_name)` key. Same callee called
twice → same lemmas, emitted once.

### Phase 5 — Fallback

If no frame lemmas are emitted (e.g., callee writes = nil and target is
the only new variable), `wp_prove` handles the forall directly via the
existing `wp_ccall_frame` pattern match (which already works for 5/9 tests).

## Impact

| Before | After |
|--------|-------|
| One huge `forall` for all variables | One `apply` per frame variable |
| WP term grows exponentially with CCalls | WP term stays linear (lemmas are separate) |
| `cbn` exclusions needed globally | No exclusions needed |
| `coqc` hangs on multi-CCall | Instant (trivial lemma proofs) |

## Data Flow

```
Python source
  │
  ├── _build_contract_map() → callee_writes
  │
  ├── PyToImpLowerer._lower_ccall()
  │     ├── Resolves callee_writes → mapped to caller arg names
  │     ├── Computes frame_vars = locals \ (target :: mapped_writes)
  │     └── Stores on ImpCCall.frame_vars
  │
  └── _generate_coq()
        ├── Walks ImpIR → collects all (callee, var) pairs
        ├── Deduplicates
        ├── Emits Lemma block (after Definition, before Theorem)
        ├── Emits apply calls in proof script
        └── Qed.
```

## Files Changed

| File | Change |
|------|--------|
| `imp_ir.py` | Add `frame_vars: list[str]` to `ImpCCall` |
| `py_to_imp.py` | Compute `frame_vars` in `_lower_ccall()` |
| `mcp_server.py` | Generate lemmas + proof uses in `_generate_coq()` |
| `WpTactics.v` | No changes needed (uses existing `wp_ccall_frame`) |
