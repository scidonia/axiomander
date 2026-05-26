# Staged Proof Engineering for Coq + SMT + LLM Systems

## Purpose

This guide describes a robust architecture for building a verification system that combines:

- Mechanical proof automation
- SMT solving
- Interactive theorem proving in Coq
- LLM-assisted proof completion

The core design goal is:

> Never lose partial proof work.

A failed proof attempt should produce reusable artifacts, not dead ends.

---

# 1. Core Philosophy

Do **not** structure the system as:

```text
Try Coq.
If Coq fails, ask LLM.
```

Instead, structure the system as:

```text
Program
→ IR
→ Verification Conditions
→ Normalization
→ Mechanical tactics
→ SMT
→ Residual goals
→ LLM assistance
→ Re-integrate result
```

The LLM should operate on the residual proof state, not the original source program.

---

# 2. Generate Small Named Obligations

Never emit one giant theorem.

Instead generate many small obligations with stable identifiers.

Example:

```text
obligation_id:
  sort.insert.preserves_sorted.branch_2
```

With:

```text
Context:
  xs_sorted : sorted(xs)
  pivot_le_head : pivot <= head(xs)

Goal:
  sorted(pivot :: xs)
```

Advantages:

- Fine-grained caching
- Better SMT performance
- Better LLM prompts
- Incremental proof reuse
- Easier debugging
- Parallelization

---

# 3. Normalize Obligations Before Proof

Before invoking Coq or SMT, normalize obligations into canonical form.

Recommended normalization passes:

- Alpha renaming
- Controlled unfolding
- Arithmetic extraction
- Path condition simplification
- Heap normalization

---

# 4. Durable Proof Artifacts

Every proof stage should produce durable artifacts.

Recommended directory structure:

```text
proof-cache/
  obligation_id/
```

Example:

```text
proof-cache/
  sort.insert.preserves_sorted.branch_2/
    source.py
    ir.json
    wp.v
    normalized_goal.v
    smt.smt2
    tactic_trace.json
    residual_goals.v
    llm_prompt.md
    llm_candidate.v
    final_proof.v
    status.json
```

This enables:

- replay
- debugging
- offline analysis
- proof migration
- learning from failed attempts

---

# 5. Mechanical Tactic Pipeline

Use a deterministic tactic ladder.

Example:

```coq
intros.
cbn in *.
subst.
autorewrite with axiomander in *.
try lia.
try nia.
try congruence.
try firstorder.
try eauto with axiomander.
```

Then domain-specific tactics:

```coq
heap_simpl.
region_disjoint.
frame.
smt.
```

Every tactic attempt should produce a trace.

---

# 6. SMT Integration

Avoid opaque “solver says yes” workflows.

Instead preserve:

- solver version
- SMT query hash
- proof certificate if available
- reconstructed Coq proof
- trusted boundary metadata

Example:

```json
{
  "solver": "z3",
  "version": "4.13",
  "query_hash": "abc123",
  "status": "sat"
}
```

---

# 7. Residual Goal Capture

When Coq gets stuck, save the exact residual proof state.

Persist:

- original obligation
- normalized obligation
- proof script attempted
- last successful tactic
- remaining goals
- hypotheses
- blocked lemmas
- counterexamples/models

The LLM should receive this residual state.

---

# 8. Narrow LLM Tasks

Bad prompt:

```text
Please prove this theorem.
```

Good prompt:

```text
The tactic ladder solved all goals except this one.
Find a Coq lemma or proof script for the remaining goal only.
Do not change definitions.
Do not use Admitted.
Prefer induction, inversion, lia, or existing lemmas.
```

The LLM should produce:

- a missing lemma
- a proof patch
- a tactic sequence
- an invariant suggestion

---

# 9. Multi-Level Caching

Cache:

- source hash
- IR hash
- WP hash
- normalized obligation hash
- SMT query hash
- tactic traces
- residual goals
- successful proof scripts
- failed proof states
- LLM suggestions

This ensures failed work remains useful.

---

# 10. Failure Classification

Every failed proof should classify as one of:

1. bug in code
2. missing precondition
3. missing invariant
4. missing library lemma
5. insufficient automation

The LLM should classify before attempting repairs.

---

# 11. Recommended Architecture

Recommended pipeline:

```text
Python
  ↓
Typed IR
  ↓
Effect/Heap IR
  ↓
Weakest Preconditions
  ↓
Normalization
  ↓
Coq tactics
  ↓
SMT discharge
  ↓
Residual goals
  ↓
LLM proof assistance
  ↓
Re-check in Coq
```

The LLM never becomes the trusted checker.

Coq remains the final authority.

---

# 12. Critical Principle

The system should never say:

```text
proof failed
```

Instead it should say:

```text
proof failed after reducing to this residual goal,
with these hypotheses,
after these tactics succeeded,
and this appears to require lemma L or invariant I.
```

That is the correct handoff boundary between:

- mechanical proof
- SMT automation
- interactive proving
- LLM assistance

This is what makes the entire system compositional and reusable.
