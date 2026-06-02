# Self-Verification Plan — Proving Axiomander's Own Contracts

## Goal

Make every contract in Axiomander's own codebase verifiable at Level 1-3.
Currently scalar standins capture the decision logic; the real
implementations fail on IMP model limitations.

---

## Phase 1 — Reduced class-field expansion (highest impact)

**Problem:** `def is_proved(self: GoalStatus) -> bool` expands all 11
`GoalStatus` fields to Coq params, but only `self.level` is used in the
body. Frame conditions on the other 10 fields bloat the proof past
what `wp_prove` can handle.

**Fix:** In `_expand_params`, after expanding a class-typed param, filter
to only fields actually read/written in the function body. This is the
same analysis `purity_analyzer.py` already does for `mentioned_fields` —
reuse it.

**Files:** `mcp_server.py` `_expand_params`, `purity_analyzer.py`

**Expected:** `GoalStatus.is_proved()` proves at Level 1.
`GoalStatus.is_proved()` has 11 fields. `_spec_is_proved(level)` already
proves at Level 1 — the real method is identical, modulo the 10 unused
fields.

---

## Phase 2 — String operations in IMP (enables 4 functions)

**Problem:** `_escape_field`, `CoqVar.to_coq`, `classify_failure` (real),
and `TheoremIR.to_coq` all operate on strings. The IMP model has
no string operations.

**Functions affected:** `_escape_field` (replace), `classify_failure`
(lower, `in`), `CoqVar.to_coq` (concatenation), `TheoremIR.to_coq`
(concatenation + membership).

**Fix:** Add `AStrConcat`, `AStrReplace`, `AStrLower` to `aexp` in `Imp.v`
with corresponding WP cases. Alternatively: treat string operations as
opaque pure functions at Level 3 (LLM oracle handles them).

**Current state:** `_escape_field` and `classify_failure` already prove at
Level 3 via the LLM oracle — the oracle generates Coq proofs that treat
string ops as axioms. This is acceptable for now.

**Files:** `coq/Imp.v` (aexp), `coq/Wp.v` (wp cases), `imp_ir.py`
(node + to_coq), `py_to_imp.py` (lowering)

---

## Phase 3 — `list()` constructor in body context

**Problem:** `get_callers` and `get_callees` use `list(node.callers)` on an
attribute. The IMP body translator rejects `list()` constructor calls.

**Fix:** In `py_to_imp.py` `_lower_call_as_assign`, add `list()` handling.
When `expr.func == "list"` with a single arg, lower to the arg directly
(the IMP model already stores lists as heap objects — `list()` is just
an identity in the flattened representation).

**Files:** `py_to_imp.py` `_lower_call_as_assign` (line ~815)

**Expected:** `get_callers`/`get_callees` prove at Level 3.

---

## Phase 4 — Loop invariant for `get_transitive_callers`

**Problem:** `get_transitive_callers` has a `while stack:` loop that pops
from a list and appends to a set. The IMP model supports `CWhile` with
invariants, but the invariant must be explicit.

**Fix:** Add a loop invariant to the function body:
```python
# inv: visited is the set of nodes reachable from name via
#      callers, excluding nodes still on the stack.
# inv: len(stack) decreasing relative to unvisited nodes.
```
Or: produce a scalar encoding where the set difference is encoded as
integer flags — already done in the scalar `get_transitive_callers`
standin.

**Current state:** The scalar standin proves at Level 3.

---

## Phase 5 — Recursive function support

**Problem:** `flat_fields(shape, prefix, visited)` is recursive. IMP
has no function calls.

**Fix:** Two options:
  1. Inline the recursive call (bounded depth) — works for shallow
     nesting, fails for deep shapes.
  2. Use Coq's `Fixpoint` with a decreasing argument — Level 3 territory,
     LLM oracle generates the induction.

**Current state:** Not verifiable in IMP. The function's correctness is
structural (prefix consistency, cycle detection) — these are better
proven as Coq lemmas than as IMP contracts.

---

## Priority order

| Phase | Impact | Effort | What it unlocks |
|---|---|---|---|
| 1 — reduced field expansion | Very high | Low | `is_proved()` at Level 1 |
| 2 — string ops in IMP | High | High | 4 functions (or keep Level 3) |
| 3 — `list()` in body | Medium | Low | `get_callers`/`get_callees` |
| 4 — loop invariant | Medium | Medium | `get_transitive_callers` |
| 5 — recursion | Low | Very high | `flat_fields` (or keep as Coq lemma) |

Phases 1 and 3 are the low-effort, high-impact items that should be
done immediately. Phase 2 can be deferred — the LLM oracle already
proves string-using functions at Level 3. Phases 4 and 5 require
the most design work.

---

## Success criteria

- `GoalStatus.is_proved()` proves at Level 1
- `classify_failure()` proves at Level 1 or 3 (already does at 3)
- `get_callers()` / `get_callees()` prove at Level 3
- `get_transitive_callers()` proves at Level 3 with loop invariant
- `_escape_field()` proves at Level 3 (already does)
- `build_report()` real proves at Level 3 (object construction)
- `CoqVar.to_coq()` proves at Level 3 (string concatenation)
- `flat_fields()` remains as a Coq-level lemma (not IMP-verifiable)
