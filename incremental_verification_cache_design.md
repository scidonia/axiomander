# Incremental Verification and Cache Design for Assert-Driven Python Vericoding

## Overview

The goal of the vericoding MCP is to make verification practical for large,
real-world Python codebases.

A naïve verification system rechecks every function after every edit. This
becomes prohibitively expensive once verification includes:

- weakest precondition generation
- SMT proving
- Coq proof reconstruction
- invariant synthesis
- proof-directed repair

Instead, the verifier should behave more like an incremental build system.

The core principle is:

> Function contracts are interfaces.  
> Proofs are cached build artifacts.

---

# Architectural Principle

The critical distinction is between:

- implementation details
- exported verification summaries

A function body may change without affecting callers if its externally visible
contract remains stable.

Therefore:

> Bodies invalidate local proofs.  
> Contracts invalidate callers.

---

# Verification Pipeline

```text
Python source
  ↓
Assert extraction / normalization
  ↓
Verification IR
  ↓
Weakest precondition generation
  ↓
Proof obligations
  ↓
SMT proving
  ↓
Coq escalation (optional)
```

The incremental cache lives between:

- IR generation
- obligation generation
- proof discharge

---

# Function Cache Structure

Each verified function should have a cache entry.

```text
FunctionCache(f):
  source_hash
  normalized_ir_hash
  contract_signature_hash
  callees
  callee_contract_hashes
  obligations_hash
  proof_results
```

---

# Important Hash Categories

## 1. Body Hash

```text
body_hash(f)
```

Represents the normalized implementation body.

Should ignore:

- formatting
- comments
- whitespace

Changing the body hash invalidates only local proofs.

---

## 2. Contract Hash

```text
contract_hash(f)
```

Represents externally visible verification behavior.

Examples:

- preconditions
- postconditions
- effects/frame conditions
- exceptions
- mutability guarantees

Callers depend on this hash.

Changing this hash invalidates callers.

---

## 3. Local Assertion Hash

```text
local_assert_hash(f)
```

Represents assertions used only internally:

- loop invariants
- local proof hints
- strengthening assertions

Changes invalidate only the current function.

---

## 4. Summary Hash

```text
summary_hash(f)
```

The exported semantic summary used by callers.

Example:

```text
summary_hash =
  hash(
    preconditions,
    postconditions,
    effects,
    exceptions
  )
```

Callers should depend only on this summary.

Not on implementation details.

---

# Dependency Graph

The verifier should maintain a dependency graph.

```text
f -> g
```

means:

```text
f depends on g's contract summary
```

NOT:

```text
f depends on g's implementation
```

This distinction is essential for scalability.

---

# Cache Invalidation Rules

## Case 1: Function Body Changed

```text
withdraw() implementation changed
contract unchanged
```

Action:

```text
Reverify:
  withdraw()

Do NOT reverify:
  transfer()
  payment_pipeline()
```

---

## Case 2: Local Assertions Changed

```text
loop invariant modified
```

Action:

```text
Reverify:
  current function only
```

---

## Case 3: Contract Changed

```text
postcondition strengthened/weakened
```

Action:

```text
Reverify:
  current function
  direct callers
  transitive callers
```

---

## Case 4: Callee Contract Changed

If:

```text
f calls g
```

and:

```text
summary_hash(g) changes
```

then:

```text
f must be reverified
```

---

## Case 5: Specification Predicate Changed

If a logical helper changes:

```python
is_sorted(xs)
```

then all obligations depending on it must be invalidated.

---

## Case 6: Prover or IR Version Changed

Changes to:

- SMT solver version
- Coq version
- WP engine
- IR semantics

should invalidate proofs globally or within a version namespace.

---

# Effect and Frame Tracking

Real Python verification requires tracking effects.

Otherwise hidden mutations break soundness.

Each exported summary should include:

```text
reads:
writes:
mutates:
raises:
calls:
```

Example:

```text
ContractSummary(withdraw):
  pre:
    balance >= amount

  post:
    balance' = balance - amount

  writes:
    self.balance

  raises:
    InsufficientFunds
```

---

# Verification Granularity

Proof caching should occur at the obligation level.

Cache key:

```text
hash(
  normalized_obligation,
  imported_contract_summaries,
  logical_environment,
  prover_config,
  tool_version
)
```

This enables:

- partial proof reuse
- fine-grained invalidation
- scalable verification

---

# MCP-Oriented Commands

The MCP should expose cache-aware operations.

## Verify Only Changed Components

```text
verify.changed()
```

---

## Verify Single Function

```text
verify.function(name)
```

---

## Show Impacted Functions

```text
verify.impacted()
```

Example output:

```text
Changed:
  insert_sorted postcondition

Will reverify:
  insert_sorted
  insertion_sort
  sort_properties
```

---

## Explain Cache Usage

```text
verify.explain_cache(function)
```

Example:

```text
transfer():
  reused obligations: 14
  regenerated obligations: 2

Reason:
  withdraw() body changed
  withdraw() contract unchanged
```

---

# Contract Evolution Optimizations

A later optimization can classify contract changes semantically.

## Safe-ish Changes

### Weaker Preconditions

```text
requires x > 5
→
requires x > 0
```

Usually callers remain valid.

---

### Stronger Postconditions

```text
ensures sorted(xs)
→
ensures sorted(xs) and unique(xs)
```

Usually callers remain valid.

---

## Dangerous Changes

### Stronger Preconditions

```text
requires x > 0
→
requires x > 10
```

May invalidate callers.

---

### Weaker Postconditions

```text
ensures sorted(xs)
→
ensures partially_sorted(xs)
```

May invalidate callers.

---

# Recommended Initial Strategy

Version 1 should use simple hash invalidation.

Reason:

- predictable
- easy to reason about
- sound
- implementation simplicity

Semantic contract-diff reasoning can be added later.

---

# Long-Term Goal

The system should support:

- incremental verification
- proof-directed repair
- LLM-guided invariant generation
- counterexample-driven development
- proof-carrying Python

without requiring full-project reverification after every edit.

The verifier becomes:

```text
a build system for correctness
```

rather than:

```text
a batch theorem proving pipeline
```
