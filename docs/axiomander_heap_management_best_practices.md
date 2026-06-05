# Heap Management Best Practices for Axiomander

## Purpose

This document describes best practices for managing heap effects in Axiomander while keeping the source language as close as possible to ordinary Python.

The design goal is:

> Verified heap reasoning for real Python code with zero required runtime library.

Axiomander should extract verification meaning from normal Python features:

- `assert`
- `if __debug__:` blocks
- comments
- docstrings
- type annotations

There should be no required decorators, base classes, runtime ghost objects, or imported verification library.

---

# 1. Core Principle

Heap management should be based on **logical regions**, not raw Python variables.

A variable such as `xs` is only a reference. Mutating `xs.append(x)` does not mutate the local variable `xs`; it mutates the heap region reachable through `xs`.

So avoid thinking in terms of:

```text
writes xs
```

Prefer:

```text
writes list_contents(xs)
```

or more generally:

```text
writes heap(xs)
```

---

# 2. Recommended Region Model

Use an abstract `RegionId` model.

```text
RegionId ::=
    local(var)
  | heap(obj)
  | field(obj, name)
  | dict(obj)
  | list_contents(obj)
  | db(conn, table)
  | db_row(conn, table, key)
  | file(path)
  | socket(endpoint)
  | unknown
```

These regions are logical verification regions, not concrete runtime objects.

---

# 3. Effect Summaries

Every command and function should have a conservative effect summary.

```text
Effect = {
    reads  : Set RegionId,
    writes : Set RegionId,
    allocs : Set RegionId
}
```

The most important field is `writes`, because it controls framing.

A command may read many regions, but any region not in its `writes` set should be provably unchanged.

---

# 4. Basic Region Assignment Rules

## Local Assignment

```python
x = 1
```

Effect:

```text
writes local(x)
```

---

## Object Field Mutation

```python
acct.balance = n
```

Effect:

```text
writes field(acct, "balance")
```

---

## Dictionary Mutation

```python
d[k] = v
```

Effect:

```text
writes dict(d)
```

Initially, do not try to reason per-key unless absolutely necessary.

---

## List Mutation

```python
xs.append(x)
```

Effect:

```text
writes list_contents(xs)
```

---

## Object Method Call

```python
obj.method(x)
```

If the method is known, use its effect summary.

If unknown, conservatively assign:

```text
reads unknown
writes unknown
```

Unknown effects should block strong framing claims until the user supplies a stub or annotation.

---

# 5. Zero-Library Annotation Style

Axiomander should not require users to import a verification library.

Use comments and docstrings instead.

Example:

```python
def push(xs, x):
    # axiomander: reads list_contents(xs)
    # axiomander: writes list_contents(xs)

    old_len = len(xs) if __debug__ else None

    xs.append(x)

    assert len(xs) == old_len + 1
```

The Python runtime sees ordinary Python.

The Axiomander extractor sees:

```text
reads list_contents(xs)
writes list_contents(xs)
ghost old_len = len(xs)
postcondition len(xs) == old_len + 1
```

---

# 6. Ghost State Without a Library

Ghost state should be represented using ordinary Python patterns.

Preferred pattern:

```python
old_total = sum(accounts.values()) if __debug__ else None
```

This means:

```text
ghost old_total := sum(accounts.values())
```

The value exists only when assertions/debugging are enabled. The verifier can treat it as a ghost snapshot.

---

# 7. Ghost Snapshot Best Practice

Use ghost snapshots before mutation.

Example:

```python
def transfer(accounts, src, dst, amount):
    assert amount >= 0
    assert accounts[src] >= amount

    # axiomander: reads dict(accounts)
    # axiomander: writes dict(accounts)

    old_total = sum(accounts.values()) if __debug__ else None

    accounts[src] -= amount
    accounts[dst] += amount

    assert sum(accounts.values()) == old_total
```

The snapshot is logical evidence that a global invariant was preserved.

---

# 8. Frame Rule

The central heap-management theorem should be:

```text
If r is not in writes(command), then region r is unchanged by command.
```

In Coq-like form:

```coq
r ∉ writes(c) -> region_state_after r = region_state_before r
```

This is the basis for compositional verification.

---

# 9. Unknown Effects Must Be Poisonous

For real Python, unknown code is unavoidable.

Best practice:

```text
unknown call -> writes unknown
```

This is deliberately conservative.

It prevents Axiomander from proving false frame claims about code it does not understand.

Users can recover precision by adding:

- comments
- docstring summaries
- stubs
- contracts

---

# 10. External APIs and Databases

External systems should be modeled as regions.

Start coarse.

For databases, begin with table-level regions:

```text
db(conn, "accounts")
db(conn, "ledger")
```

Example:

```python
def transfer_db(conn, src, dst, amount):
    """
    axiomander:
      reads:
        db(conn, "accounts")
      writes:
        db(conn, "accounts")
      preserves:
        db_total(conn, "accounts", "balance")
    """

    old_total = db_total(conn, "accounts", "balance") if __debug__ else None

    debit(conn, src, amount)
    credit(conn, dst, amount)

    assert db_total(conn, "accounts", "balance") == old_total
```

The functions like `db_total` do not need to exist in production if they are parsed as ghost/spec expressions or kept in debug/test-only code.

---

# 11. Do Not Start With Fine-Grained Regions

Avoid starting with row-level or field-level database regions unless needed.

Start with:

```text
db(conn, "accounts")
```

Later refine to:

```text
db_row(conn, "accounts", account_id)
```

Only introduce fine-grained regions when coarse regions cause too many false conflicts.

---

# 12. Aliasing Policy

Initially, be conservative about aliases.

Example:

```python
a = xs
b = xs
b.append(1)
```

The mutation through `b` affects `list_contents(xs)` as well.

Axiomander should either:

1. track simple aliases syntactically, or
2. collapse aliases to a shared heap region, or
3. fall back to `heap(unknown)` when aliasing is unclear.

Soundness is more important than precision.

---

# 13. Recommended Alias Strategy

Use simple alias normalization first.

```python
a = xs
```

Record:

```text
a aliases xs
```

Then:

```python
a.append(1)
```

becomes:

```text
writes list_contents(xs)
```

If alias tracking becomes uncertain, widen to:

```text
writes heap(unknown)
```

---

# 14. Ownership and Borrowing Discipline

Even without a formal ownership type system, encourage a lightweight discipline:

- functions should declare what heap regions they write
- callers should rely only on regions outside that write set being preserved
- mutable arguments should be treated as borrowed regions
- newly allocated objects should get fresh regions

Example:

```python
def make_list(x):
    ys = []
    ys.append(x)
    return ys
```

Effect:

```text
allocs list_contents(ys)
writes list_contents(ys)
```

---

# 15. Stubs for Library Calls

Real Python depends heavily on libraries.

Do not attempt to inline or fully model every library function.

Use stubs.

Example stub:

```text
list.append(xs, x):
  reads  list_contents(xs)
  writes list_contents(xs)
  ensures len(xs) = old(len(xs)) + 1
```

Stub summaries are part of the trusted base until proved or tested.

---

# 16. Best Practice for Containers

Treat container contents as separate from the variable holding the container.

```python
xs = []
```

writes:

```text
local(xs)
allocs list_contents(xs)
```

```python
xs.append(1)
```

writes:

```text
list_contents(xs)
```

```python
xs = ys
```

writes:

```text
local(xs)
```

This distinction is essential.

---

# 17. Best Practice for Object Fields

For object-oriented code, prefer field regions.

```python
user.name = "Alice"
```

writes:

```text
field(user, "name")
```

If field sensitivity is too difficult initially, widen to:

```text
heap(user)
```

Field-sensitive reasoning can be added later.

---

# 18. Best Practice for Assertions

Assertions should describe observable properties, not internal proof machinery.

Good:

```python
assert len(xs) == old_len + 1
assert sum(accounts.values()) == old_total
assert acct.balance >= 0
```

Avoid exposing verifier internals in ordinary assertions.

Use comments/docstrings for region metadata.

---

# 19. Best Practice for Invariants

Use ghost snapshots for preservation properties.

Use ordinary asserts for final claims.

Example:

```python
old_keys = set(d.keys()) if __debug__ else None

update_values(d)

assert set(d.keys()) == old_keys
```

This expresses that values may change but keys are preserved.

Effect:

```text
writes dict(d)
preserves keys(d)
```

---

# 20. Best Practice for Incremental Adoption

Axiomander should support gradual precision.

Recommended precision ladder:

1. `writes unknown`
2. `writes heap(obj)`
3. `writes dict(obj)` / `list_contents(obj)`
4. `writes field(obj, name)`
5. `writes db(conn, table)`
6. `writes db_row(conn, table, key)`
7. verified stubs and library models

Users should be able to start coarse and refine only when necessary.

---

# 21. Verification Workflow

Recommended agent workflow:

1. Parse Python normally.
2. Extract assertions.
3. Extract region annotations from comments/docstrings.
4. Infer obvious heap regions syntactically.
5. Assign unknown effects for unresolved calls.
6. Generate effect summaries.
7. Generate frame obligations.
8. Generate weakest preconditions.
9. Try SMT first.
10. Escalate hard obligations to Coq or an LLM proof oracle.
11. Report missing annotations or unknown writes.

---

# 22. What the Agent Should Prioritize

The agent should prefer soundness over precision.

When unsure, widen effects.

Examples:

```text
maybe writes field(x, "a")
```

If uncertain, use:

```text
writes heap(x)
```

If the target object is uncertain, use:

```text
writes unknown
```

A false positive is acceptable.

A false proof is not.

---

# 23. Minimal Annotation Syntax

Implement these first:

```python
# axiomander: reads REGION
# axiomander: writes REGION
# axiomander: preserves EXPR
# axiomander: ghost NAME = EXPR
```

Docstring block form:

```python
def f(x):
    """
    axiomander:
      reads:
        heap(x)
      writes:
        field(x, "value")
      preserves:
        invariant(x)
    """
```

---

# 24. Minimal Ghost Pattern

Recognize this Python idiom:

```python
name = expr if __debug__ else None
```

as:

```text
ghost name = expr
```

This is the key zero-library ghost-state mechanism.

---

# 25. Final Rule of Thumb

The best heap-management strategy for Axiomander is:

> Infer simple regions automatically, require annotations for external effects, model unknown code conservatively, and use ghost snapshots to express preservation properties.

This gives Axiomander a path from ordinary Python asserts to serious heap-aware verification without requiring users to adopt a new runtime library.
