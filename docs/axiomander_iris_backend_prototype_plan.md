# Axiomander Iris Backend Prototype Plan

## Purpose

This document specifies a small prototype experiment to test whether Axiomander can, in principle, use an Iris-style separation logic backend while preserving the existing contract language and lowering pipeline.

This is not a plan to make Iris the default backend. The goal is narrower: prove that a trivial separation-logic example can pass through Axiomander's existing first IR lowering, be classified as resource-aware, and then be lowered into an Iris-shaped proof obligation.

The prototype should answer one question:

> Can Axiomander lower a simple Python contract into its existing IR, identify a separation-logic resource footprint, split pure obligations from resource obligations, and discharge the pure side conditions using the existing SMT/axiom-import approach while leaving the heap/resource part to an Iris-style model?

## Constraints

1. The contract language must remain backward compatible.
2. Existing pure contracts must continue to lower and prove as they currently do.
3. No user-facing Iris syntax should be required.
4. The prototype should use one deliberately trivial separation-logic example.
5. The first lowering pass should remain the current Axiomander lowering as far as possible.
6. The second lowering pass may branch into an experimental `resource_wp` or `iris_wp` representation.
7. SMT may continue to prove pure facts by checking unsatisfiability of the negated goal and importing the resulting fact as an axiom or trusted lemma.

## Prototype Example

Use a tiny mutable cell or object field example. Prefer an object field if it fits the current Axiomander frontend better.

### Candidate Python Example

```python
class Box:
    value: int


def bump(box: Box) -> int:
    """
    axiomander:
        requires:
            owns(box)
            box.value >= 0
        modifies:
            box.value
        ensures:
            owns(box)
            box.value == old(box.value) + 1
            result == box.value
    """
    box.value = box.value + 1
    return box.value
```

This example is intentionally simple. The point is not to prove anything impressive. The point is to test whether the resource layer can be threaded through the existing pipeline.

## Expected Informal Separation-Logic Meaning

The contract should be interpreted approximately as:

```text
Pre:
  box owns a heap cell/field containing n
  n >= 0

Command:
  load box.value
  store box.value := n + 1
  load box.value
  return n + 1

Post:
  box still owns the same field
  field value is n + 1
  result is n + 1
```

In separation-logic notation:

```text
{ box.value ↦ n * pure(n >= 0) }
  box.value := box.value + 1; return box.value
{ r. box.value ↦ n + 1 * pure(r = n + 1) }
```

The user should not write this notation. It is the backend interpretation of `owns(box)` plus `modifies: box.value` plus the existing pre/post conditions.

## Success Criteria

The prototype succeeds if it can produce and inspect the following stages:

1. The existing frontend accepts the example contract.
2. The existing first IR lowering runs.
3. The contract classifier identifies the function as `mixed_pure_resource` rather than pure-only.
4. The resource footprint is extracted from `owns(box)` and `modifies: box.value`.
5. The lowered core command sequence is recognized as load/store/load/return over the owned field.
6. Pure side conditions are split out and sent to the existing SMT pathway.
7. The resource obligation is emitted in a small Iris-shaped intermediate form.
8. The generated proof skeleton is syntax-directed.
9. The prototype produces a final diagnostic saying either:
   - resource proof skeleton generated successfully; pure side conditions discharged, or
   - resource proof failed at a named step with an Axiomander-level explanation.

## Non-Goals

Do not implement full Iris integration yet.

Do not attempt concurrency, invariants, masks, fancy updates, prophecy variables, saved propositions, or logical relations.

Do not expose separating conjunction, Iris namespaces, masks, or proof-mode tactics to the user.

Do not replace the existing SMT/Rocq path.

Do not attempt to verify arbitrary Python heap behavior.

Do not require all object fields to be modeled as resources. Resource interpretation is opt-in via `owns(...)`.

## Phase 1: Add Resource Predicate Recognition

Add parser/classifier recognition for a tiny set of reserved predicate names:

```text
owns(x)
```

For the prototype, only `owns(x)` is required.

Do not change the meaning of existing contracts.

### Internal Classification

Add a contract classification result:

```text
pure_only
resource_only
mixed_pure_resource
unsupported_resource
```

The `bump` example should classify as:

```text
mixed_pure_resource
```

because it contains:

```text
Resource:
  owns(box)

Pure:
  box.value >= 0
  box.value == old(box.value) + 1
  result == box.value
```

### Acceptance Tests

Existing contract without `owns`:

```python
requires: x >= 0
ensures: result >= x
```

must still classify as:

```text
pure_only
```

New contract with `owns(box)` must classify as:

```text
mixed_pure_resource
```

## Phase 2: Introduce a Tiny Resource IR

Add a minimal internal resource assertion layer. For the prototype, keep it very small.

```python
@dataclass
class ROwn:
    var: str

@dataclass
class RField:
    obj: str
    field: str
    value: str | Expr

@dataclass
class RPure:
    expr: Expr

@dataclass
class RSep:
    left: RAssert
    right: RAssert
```

For the prototype, do not require users to write `RField` explicitly.

Infer it from:

```text
owns(box)
modifies: box.value
old(box.value)
```

The inferred precondition for `bump` should be something like:

```text
RSep(
  RField("box", "value", "old_box_value"),
  RPure(old_box_value >= 0)
)
```

The inferred postcondition should be:

```text
RSep(
  RField("box", "value", old_box_value + 1),
  RPure(result == old_box_value + 1)
)
```

Keep `ROwn(box)` as a user-level ownership marker, but lower it into concrete field ownership only when paired with `modifies: box.value`.

## Phase 3: Preserve the First IR Lowering

The first lowering pass should remain close to the current Axiomander path:

```text
Python AST + contract docstring
  -> Axiomander contract AST
  -> current lowered IR / IMP-style representation
```

For the example function, the lowered command sequence should be inspectable as approximately:

```text
t0 := load_field box value
t1 := t0 + 1
store_field box value t1
t2 := load_field box value
return t2
```

If the current IR does not distinguish field load/store explicitly, add a temporary annotation pass after lowering:

```text
Assign(Field(box, value), Add(Read(Field(box, value)), Const(1)))
Return(Read(Field(box, value)))
```

This annotation pass should be prototype-only and should not disturb the existing pure pipeline.

## Phase 4: Add a Second Lowering Decision

After first IR lowering, route the function by contract classification:

```text
pure_only:
  existing pipeline

mixed_pure_resource:
  existing first IR
  -> resource footprint extraction
  -> pure side-condition extraction
  -> resource WP skeleton

resource_only:
  resource WP skeleton

unsupported_resource:
  fail with clear diagnostic
```

For `bump`, the second lowering should choose:

```text
mixed_pure_resource -> resource_wp_experimental
```

## Phase 5: Resource Footprint Extraction

Given:

```text
requires owns(box)
modifies box.value
```

infer:

```text
owned footprint = box.value
```

For the prototype, reject ambiguous cases:

```text
owns(box)
modifies box.value, box.other
```

unless multiple fields are explicitly supported.

Reject:

```text
modifies box.value
```

with no ownership when using the resource backend.

Reject:

```text
owns(box)
```

with no relevant `modifies` if the function performs a field store.

Diagnostics should be phrased in Axiomander terms, not Iris terms:

```text
Cannot use resource backend: function writes box.value but contract does not establish ownership of box.
```

## Phase 6: Split Pure Side Conditions

The resource proof should generate pure obligations such as:

```text
old_box_value >= 0 -> old_box_value + 1 >= 1
result = old_box_value + 1
```

For the minimal example, the most important pure obligations are:

```text
t1 = old_box_value + 1
result = t1
result = old_box_value + 1
```

Continue using the existing SMT strategy:

1. Generate the pure goal.
2. Ask SMT whether the negation is unsatisfiable.
3. If unsat, import the pure fact as a trusted axiom/lemma into the Rocq/Iris-side proof context.

For the prototype, make trust explicit in the generated artifact:

```coq
Axiom smt_pure_step_1 : t1 = old_box_value + 1.
```

or, preferably:

```coq
Lemma smt_pure_step_1 : t1 = old_box_value + 1.
Proof. (* imported from SMT unsat certificate/trusted oracle *) Admitted.
```

The prototype may use `Admitted` or `Axiom`, but it must tag the source as SMT-trusted.

## Phase 7: Emit an Iris-Shaped Obligation Format

Before generating real Rocq/Iris code, emit a simple textual or JSON intermediate representation.

Example JSON-like shape:

```json
{
  "kind": "resource_wp_obligation",
  "function": "bump",
  "resource_model": "owned_field_v0",
  "pre": {
    "field": ["box", "value", "old_box_value"],
    "pure": ["old_box_value >= 0"]
  },
  "program": [
    {"load_field": ["t0", "box", "value"]},
    {"assign": ["t1", "t0 + 1"]},
    {"store_field": ["box", "value", "t1"]},
    {"load_field": ["t2", "box", "value"]},
    {"return": "t2"}
  ],
  "post": {
    "field": ["box", "value", "old_box_value + 1"],
    "pure": ["result == box.value"]
  },
  "pure_side_conditions": [
    "t0 == old_box_value",
    "t1 == old_box_value + 1",
    "t2 == t1"
  ]
}
```

This is the main prototype artifact. It lets the team decide whether the second lowering is sensible before committing to a full Iris development.

## Phase 8: Generate a Proof Skeleton

Generate an Iris-like proof skeleton, even if it is not yet executable.

Example skeleton:

```coq
Lemma bump_spec box old_box_value :
  {{{ box_value_points_to box old_box_value ∗ ⌜old_box_value >= 0⌝ }}}
    bump_core box
  {{{ result, RET result;
      box_value_points_to box (old_box_value + 1) ∗
      ⌜result = old_box_value + 1⌝ }}}.
Proof.
  iIntros (Φ) "(Hfield & %Hnonneg) HΦ".
  wp_load_field.
  wp_pures.
  (* SMT imported: t1 = old_box_value + 1 *)
  wp_store_field.
  wp_load_field.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  exact smt_result_fact.
Qed.
```

This skeleton does not need to compile in the first prototype. The useful output is that the proof shape is syntax-directed:

```text
load -> wp_load_field
pure arithmetic -> SMT side condition
store -> wp_store_field
load -> wp_load_field
return -> postcondition
```

## Phase 9: Optional Executable Rocq/Iris Stub

If the team wants one executable artifact, avoid modeling all of Python. Define a tiny core language directly in Rocq/Iris or use an Iris heap-language encoding.

The tiny core needs only:

```text
field load
field store
integer addition
return
```

The field can be represented as a single heap location:

```text
box.value ≈ l ↦ #n
```

Then the example reduces to the canonical heap update:

```coq
{{{ l ↦ #n ∗ ⌜0 <= n⌝ }}}
  let: "x" := ! #l in
  #l <- ("x" + #1);;
  ! #l
{{{ r, RET r; l ↦ #(n + 1) ∗ ⌜r = #(n + 1)⌝ }}}
```

This is not yet a faithful Python model. That is acceptable. The prototype is testing the backend route, not the full language semantics.

## Phase 10: Diagnostics and Reporting

The prototype command should produce a report like:

```text
Function: bump
Classification: mixed_pure_resource
First lowering: succeeded
Resource footprint: box.value
Resource model: owned_field_v0
Pure side conditions: 3
SMT discharged: 3/3
Resource proof skeleton: generated
Iris/Rocq executable proof: not attempted / attempted / succeeded / failed
```

If something fails, the report should say where:

```text
Failed during resource footprint extraction:
  function writes box.value, but no owns(box) predicate is present.
```

or:

```text
Failed during pure side-condition discharge:
  could not prove t1 = old_box_value + 1 from lowered arithmetic expression.
```

## Suggested File Layout

```text
axiomander/
  resources/
    __init__.py
    classify.py
    resource_ir.py
    footprint.py
    split.py
    emit_obligation.py
    emit_iris_skeleton.py

examples/
  resource_backend/
    box_bump.py
    expected_obligation.json
    expected_skeleton.v

tests/
  test_resource_classification.py
  test_resource_footprint.py
  test_box_bump_obligation.py
  test_legacy_contracts_still_pure.py
```

## Minimal Implementation Checklist

- [ ] Add recognition of `owns(x)` in contract parsing.
- [ ] Add `pure_only` / `mixed_pure_resource` classifier.
- [ ] Ensure all old contracts classify as `pure_only`.
- [ ] Add tiny resource IR.
- [ ] Extract `box.value` footprint from `owns(box)` plus `modifies: box.value`.
- [ ] Preserve existing first IR lowering.
- [ ] Add second lowering decision after first IR.
- [ ] Emit resource WP obligation JSON.
- [ ] Split pure side conditions.
- [ ] Route pure side conditions to existing SMT unsat-negation pathway.
- [ ] Mark imported SMT results explicitly as trusted.
- [ ] Generate Iris-like proof skeleton.
- [ ] Add one regression test proving legacy contracts remain unchanged.

## Key Design Decision After Prototype

After this prototype, decide between three second-lowering strategies:

### Option A: Direct Iris heap-language encoding

Lower the tiny resource core into Iris heap_lang.

Pros:
- Fastest path to a working Iris proof.
- Reuses existing Iris proof rules.

Cons:
- May not match Axiomander's eventual core semantics.
- Risk of proving the encoding rather than the actual Axiomander IR.

### Option B: Define Axiomander Core semantics in Iris

Define the Axiomander core language and its WP inside Iris.

Pros:
- Semantically clean.
- Best long-term route.
- Avoids ad hoc proof scripts.

Cons:
- More initial work.

### Option C: Emit abstract separation-logic obligations only

Emit obligations in an intermediate resource logic, then later choose Iris or another backend.

Pros:
- Keeps backend independence.
- Useful for debugging and design iteration.

Cons:
- Does not prove backend viability as strongly.

## Recommendation

For the prototype, use a hybrid:

```text
Axiomander first IR
  -> resource obligation JSON
  -> Iris-like skeleton
  -> optional heap_lang proof for the single-cell version
```

This shows that:

1. The current Axiomander pipeline can reach a resource-aware obligation.
2. The pure SMT pathway can continue to operate.
3. The separation-logic part has a plausible Iris interpretation.
4. Backward compatibility is preserved.

Do not start by building a full Iris backend. First demonstrate the smallest convincing path from an ordinary Axiomander contract to a resource proof skeleton.

## Final Prototype Definition of Done

The experiment is complete when the repository contains one command or test that takes:

```text
examples/resource_backend/box_bump.py
```

and produces:

```text
expected_obligation.json
expected_skeleton.v
```

with a report showing:

```text
legacy pipeline preserved: yes
resource classification: mixed_pure_resource
resource footprint: box.value
pure SMT side conditions discharged: yes
Iris-shaped proof skeleton generated: yes
```

At that point, Axiomander has evidence that an Iris backend could, in principle, be used for opt-in separation-logic contracts without replacing the existing contract language or prover strategy.
