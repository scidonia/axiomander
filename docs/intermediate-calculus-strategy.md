# Intermediate Calculus Strategy

## Why a Strategy Document

We hit a tension: `pop([x])` should be trivial — we know the list has one element, `pop` returns it. But our pipeline models `pop` as an opaque CCall with a `True` postcondition, generating frame conditions that `wp_prove` can't discharge. The result: 3 frame tests that should pass, but can't.

The root cause is not CCall frame tactics. It's that we're doing too much at the Coq level that could be done at the Python→IMP translation level with **partial evaluation**.

## The Principle

> Compute everything you can at translate time. Leave only what you *must* as symbolic IMP.

But with a critical constraint: **type annotations are hypotheses, not axioms.** The translator must not assume a variable is `int` just because the annotation says so. Contracts (explicit `assert` statements) provide the knowledge base. Driving is only safe when:

1. **Structural knowledge is available** — a list literal `[x]` has one element regardless of `x`'s type. `pop([x])` → `x`. Safe.
2. **Type knowledge is guarded** — `x + x` could be arithmetic (int) or concatenation (str/list). Only resolve when a contract (`assert isinstance(x, int)` or `assert x >= 0`) guarantees the type.
3. **Contracts provide bottoms** — if a type guard fails, the assertion causes bottom (failure). This is Python's semantics: `assert isinstance(x, int)` crashes if `x` is not an int. The verifier must prove the guard holds.

### Type Annotations as Contracts

Type annotations become pre/post conditions:

```python
def foo(x: int) -> bool:
    assert isinstance(x, int)        # injected from annotation
    result = x > 0
    assert result == 1 or result == 0  # injected from -> bool
    return result
```

Once the `isinstance` guard is proven, the translator can unbox: `x` is known to be `VZ`, so `x > 0` is a `Z` comparison, not a string operation.

## Partial Evaluation (Driving)

Supercompilation / driving is the technique of executing a program given *partial* knowledge about its inputs. For Axiomander, the inputs are:

- **Concrete values:** list literals `[x]`, string literals `"hello"`, integer constants `5`
- **Concrete structure:** a list `[a, b]` with 2 elements (values unknown)
- **Type information:** `x: int` means `x` is a `VZ` value
- **Contracts:** `assert x >= 0` means `x` is non-negative at that point

### Current State

```
Python:     v = pop([x])
            ↓
IMP:        CSeq (CListNew ...) (CCall "pop" ... (fun s => True) ...)
            ↓
Coq:        wp (CCall "pop") Q s = True /\ (forall r, True -> Q(clobber ...) /\ frame)
```

The translator sees `pop([x])` as a CCall to an opaque stub. It generates list construction code (`CListNew`, `CListAppend`), then a CCall with `True` pre/post. The Coq proof must handle frame conditions through a generic CCall mechanism.

### Target State

```
Python:     v = pop([x])
            ↓
IMP:        CAss "v" (AVar "x")
            ↓
Coq:        wp (CAss "v" (AVar "x")) Q s = Q (upd s "v" (VZ x))
```

The translator recognizes the list literal `[x]`, partially evaluates `pop`: the list has one element, `pop` removes and returns it. The list literal construction is eliminated entirely. No CCall, no stub, no frame. Just a direct assignment.

## What We Can Drive

### Structural (always safe)

Knowledge about *structure* doesn't depend on types. A list literal has a known shape regardless of element types.

| Expression | Knowledge | Drivable To |
|---|---|---|
| `pop([x])` | List literal `[x]` → 1 element | `CAss "v" (AVar "x")` |
| `len([x, y])` | List literal `[x, y]` → 2 elements | `(ANum 2)` |
| `sum([])` | Empty list literal | `(ANum 0)` |
| `len("hello")` | String literal → 5 chars | `(ANum 5)` |
| `"hello"[0]` | String literal + index 0 | `(ANum 104)` (ord('h')) |

### Type-Guarded (requires contract)

Knowledge about *types* requires a contract. The contract acts as a guard — after the guard is proven, unboxing is safe.

| Expression | Guard Required | Then Drivable To |
|---|---|---|
| `x + x` | `assert isinstance(x, int)` or `assert x >= 0` | `(APlus (AVar "x") (AVar "x"))` |
| `x + x` | `assert isinstance(x, str)` | Concat loop (CListNew/CListAppend) |
| `x + x` | No guard | **Defer** — leave as symbolic `+` in IMP, let Coq handle both cases |
| `len(s)` | `assert isinstance(s, str)` or annotation `s: str` | `ALen "s"` |
| `d[key]` | `assert isinstance(d, dict)` | `CDictGet` |

### Contract-Guided Driving

| Context | Knowledge | Drivable To |
|---|---|---|
| `x` after `assert x >= 0` | `x` is non-negative `Z` | `x` is `VZ`, `>=` operation is Z comparison |
| `i` after `while i < n` with `invariant i <= n` | Exit: `i = n` | Post-loop assertions can use `i = n` |

## Architecture

The driving pass sits between the Python AST and the IMP translator:

```
Python AST
    │
    ▼
  Contract Linter (asserts → IR, contracts)
    │
    ▼
  Partial Evaluator (drive known expressions)    ← NEW
    │
    ▼
  IMP Translator (ast → IMP commands)
    │
    ▼
  Coq Generator (IMP + contracts → Coq theorem)
```

The partial evaluator is an AST-to-AST transformer. It walks the function body and replaces driven expressions with their computed forms:

```python
def drive_expr(node, context):
    if is_list_literal(node) and context.is_pop_call:
        # pop([x]) → return the element
        return node.elts[-1]
    if is_list_literal(node) and context.is_len_call:
        # len([...]) → return the count
        return ast.Constant(value=len(node.elts))
    # ... more driving rules ...
    return node  # not drivable, leave as-is
```

## What This Unblocks

### frame_stub_pop

```
v = pop([x])
```
Drives to: `v = x`. The postcondition `result >= x` becomes `x >= x` — trivial.

### frame_stub_disjoint

```
a = pop([x])        → a = x
b = len([x, x+1])   → b = 2
result = a + b      → result = x + 2
assert result >= 2  → x + 2 >= 2 → x >= 0 (from precondition)
```

Both drivable. No CCall, no stub, no frame. Pure arithmetic.

### frame_triple_compose

```
a = plus_one(n)     → CCall (cross-function, can't drive)
b = times_two(n)    → CCall (cross-function, can't drive)
result = a + b      → arithmetic (already direct)
```

The CCall chain remains, but the `+` is direct arithmetic. The CCall frame lemma (`clobber_upd_commute`) handles the composition.

## Relation to Supercompilation

Driving is a form of supercompilation restricted to known values. A full supercompiler would:

1. **Inline function bodies** — replace CCall with the callee's IMP body
2. **Specialize loops** — unroll loops for known iteration counts
3. **Residualize** — leave unknown parts as IMP, compute known parts as values

For Axiomander, we start with the simplest driver: concrete list/string literals. This alone unblocks the 3 failing frame tests. Full supercompilation (function inlining, loop specialization) is a longer-term goal.

## Priority

1. **List literal driver** — `pop([x])`, `len([x, y])`, `sum([])`. Unblocks frame tests.
2. **String literal driver** — `len("hello")`, string indexing.
3. **CCall frame lemma** — `clobber_upd_commute`. Unblocks CCall chain tests.
4. **Supercompilation** — function inlining, loop specialization.
