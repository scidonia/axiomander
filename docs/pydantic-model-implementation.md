# Shape IR + Field Predicates — Implementation Plan

*Revised per review of `Axiomander Pydantic Architecture.pdf`.  Core
principle: **split shape (compile-time structure) from validation
(runtime predicate).  Shapes are derived automatically from Pydantic
models and type annotations.  Contracts reason about field values,
not about validity.***

---

## Design Principles (from the review)

1. **Pydantic is the frontend, not the proof language.**  Models are
   lowered into an Axiomander Shape IR that is independent of Pydantic.
   The verifier reasons about the Shape IR, not Pydantic directly.

2. **Split shape from validation.**  Shape = what fields exist and what
   types they have (compile-time, structural).  Validation = whether
   the data satisfies the shape (runtime predicate).  The verifier knows
   shapes automatically from type annotations; contracts do not need to
   assert them.

3. **Constraint lowering.**  Pydantic constraints (`Field(gt=0)`,
   `Field(min_length=3)`, `Literal["a","b","c"]`) are lowered to
   logical predicates in the Shape IR.  They become implicit
   preconditions/postconditions — no user annotation needed.

4. **Shape logic as the contract language.**  The user-facing
   predicates are `field_value(obj, "name") = v` for value reasoning.
   `has_field` and `field_type` are structural and known to the
   verifier automatically; they do not appear in user contracts.

---

## Pydantic v2 runtime semantics (the verifier must match these)

Empirically verified on pydantic ≥ 2.0:

| Operation | Default | `validate_assignment=True` |
|---|---|---|
| `Account(balance=-5)` | **Raises** `ValidationError` | Same |
| `Account(balance="100")` | **Coerces** `"100"` → `100` | Same |
| `account.balance = -5` | **Silently succeeds** | **Raises** `ValidationError` |
| `account.balance = "hello"` | **Silently succeeds** (`str` type) | **Raises** (type mismatch) |

Construction validates types + constraints.  Attribute mutation does not,
unless the model opts in with `model_config = ConfigDict(validate_assignment=True)`.

**Consequence for the verifier:**

- **Default mode:** after `account.balance = expr`, the object may be
  invalid.  The verifier cannot assume constraints hold.  The user may
  explicitly re-assert `is_valid(account, Account)` (which corresponds
  to calling `model_validate` at runtime).

- **`validate_assignment=True`:** the verifier must prove that every
  `account.balance = expr` satisfies the field's type and constraints,
  because Pydantic *will* check at runtime.  The verifier proves the
  program does not trigger a `ValidationError`.

- **`is_valid(obj, ModelType)`** is a verifier-tracked predicate:
  - True after construction (`__init__` / `BaseModel(...)`)
  - True on function entry if the caller guarantees it (contract precondition)
  - Must be re-proven after each mutation when `validate_assignment=True`
  - Can be broken by mutation in default mode; user re-asserts it

## Shape/validation predicate decomposition

Only two predicates.  `is_shape` is **never written by the user** — it is
auto-generated from type annotations.  `is_valid` is the user-visible
contract predicate.

| Predicate | Who writes it | Where | Coq expansion |
|---|---|---|---|
| `is_shape(obj, Type)` | **Verifier** (auto-injected from `obj: Type` annotation) | Every function's precondition; every CCall caller obligation | `isVZ (s "obj_f1"%string) = true /\ ...` |
| `is_valid(obj, Type)` | **User** (contract predicate) | `assert is_valid(...)` or docstring `requires:` / `ensures:` | `is_shape(obj, Type) /\ balance >= 0 /\ ...` |

`is_shape` serves two critical roles:

1. **Soundness:** `asZ (s "obj_balance"%string)` is only safe when the
   state key holds a `VZ`.  `is_shape` proves this.  Without it, Coq
   silently returns 0 for non-`VZ` values — unsound.

2. **CCall type contract:** when `deposit(account, 100)` appears as a
   CCall, the caller must prove `is_shape(account, Account)`.  The
   callee receives it in its precondition.  Type safety propagates
   across function boundaries.

Field constraints are expressed with ordinary comparisons — the existing
`account.balance >= 0` compiles to `asZ (s "account_balance"%string) >= 0`
via `visit_Attribute`.  No `field_value` predicate needed.

---

## Current state

Today a class parameter `account: Account` is structurally flattened:
`balance: int, overdraft_limit: int` → Coq state keys
`"account_balance"%string`, `"account_overdraft_limit"%string`.
`Field(ge=0)` is injected as a precondition.  The user writes
`account.balance` in contracts which compiles to
`asZ (s "account_balance"%string)`, so they must know the flat key
names implicitly.

There is no Shape IR.  There is no verifier-level concept of "this
object has these fields."  Everything is ad-hoc flat state.

---

## Target state

### Mode 1: `validate_assignment=True` — verifier lifts constraints automatically

The verifier discovers `validate_assignment=True` from the model's
`model_config`.  It tracks `is_valid` implicitly — no user contract needed.

`is_shape` is auto-injected from the `account: Account` type annotation.
Field values use ordinary Python attribute syntax.

```python
class Account(BaseModel):
    model_config = ConfigDict(validate_assignment=True)
    balance: int = Field(ge=0)

def withdraw(account: Account, amount: int) -> int:
    """
    axiomander:
        requires:
            account.balance >= amount
            amount >= 0
        modifies:
            account
        ensures:
            account.balance == old(account.balance) - amount
            result == old(account.balance) - amount
    """
    account.balance -= amount    # verifier proves: new balance >= 0
    return account.balance
```

Nothing new here — `account.balance >= amount` compiles via the existing
`visit_Attribute` path.  The constraint obligation `balance - amount >= 0`
is generated automatically from the Shape IR at the mutation point.

### Mode 2: Default (no `validate_assignment`) — conservative

No auto-enforced constraints on mutation.  `is_valid` is explicit:

```python
class Record(BaseModel):
    value: int = Field(ge=0)

def guarded_mutation(r: Record, n: int) -> None:
    """
    axiomander:
        requires:
            is_valid(r, Record)
            r.value == n
        ensures:
            is_valid(r, Record)
            r.value == abs(n)
    """
    r.value = abs(n)   # user must prove abs(n) >= 0
```

### CCall type contract

When `deposit(account, 100)` appears as a function call:

```
Caller obligation:   prove is_shape(account, Account) at the call site
Callee precondition: is_shape(account, Account) is auto-injected
```

This ensures `asZ (s "account_balance"%string)` is safe at the callee —
the state key is proven to hold a `VZ`.  The user never writes `is_shape`;
the verifier generates it from the `account: Account` annotation.

---

## Implementation steps

### Step 1 — Shape IR (`py/oracle/shape_ir.py`, new file)

```python
class ShapeField(BaseModel):
    name: str              # e.g. "balance"
    coq_type: str          # "Z", "string", "bool"
    constraints: list[str] = Field(default_factory=list)  # e.g. "0 <= {flat_key}"

class Shape(BaseModel):
    name: str              # e.g. "Account"
    fields: list[ShapeField]
    validate_assignment: bool = False   # from model_config
    flat_key_for: dict[str, str] = Field(default_factory=dict)
```

`validate_assignment=True` is detected from the model's `model_config`.
It controls whether the verifier generates constraint obligations on
mutation.

#### Shape registry + constraint injection

```python
def shape_preconditions(shape: Shape, obj_prefix: str) -> list[str]:
    """Return Coq preconditions from a shape.
    
    Always emits: isVZ type guards for every field.
    Only emits constraint checks (Field(ge=0) etc.) when the 'is_valid'
    predicate is active in the current verification context.
    """

---

### Step 2 — Contract IR predicates (`contract_ir.py`)

Two new nodes.  Both expand via the Shape registry:

```python
class IsShape(BaseModel):
    """is_shape(obj, Type) → isVZ type guards for every field.
    
    Auto-injected into every function's precondition from the parameter
    type annotation.  Never written by the user.  Also generated as the
    caller obligation for every CCall with a typed parameter.
    """
    kind: Literal["is_shape"] = "is_shape"
    obj: str
    model_type: str


class IsValid(BaseModel):
    """is_valid(obj, Type) → is_shape + all Field constraints.
    
    User-visible contract predicate.  Explicit in default mode;
    auto-tracked (implicit) when validate_assignment=True.
    """
    kind: Literal["is_valid"] = "is_valid"
    obj: str
    model_type: str
```

---

### Step 3 — Linter (`contract_linter.py`)

#### 3a — `is_shape` and `is_valid` as recognised special forms

```python
if name in ("is_shape", "is_valid"):
    if len(node.args) == 2:
        obj = self._extract_name(node.args[0])
        type_name = self._extract_name(node.args[1])
        if obj and type_name:
            cls = IsShape if name == "is_shape" else IsValid
            return cls(obj=obj, model_type=type_name)
    return None
```

#### 3b — Field access is unchanged

`account.balance >= 0` compiles via the existing `visit_Attribute` path
→ `asZ (s "account_balance"%string) >= 0`.  No new expression syntax,
no `field_value` predicate.

#### 3c — `is_shape` auto-injection

The linter does not auto-inject `is_shape`.  That happens at the IMP
translation / codegen layer, where parameter type annotations are
inspected and `is_shape` preconditions are generated.  The linter only
validates what the user writes.

---

### Step 4 — Automatic constraint obligations (`mcp_server.py`)

#### 4a — Build the Shape registry

In `_verify_function`, after `tree = ast.parse(source)`:

```python
from oracle.shape_ir import build_shape_registry
build_shape_registry(tree)
```

Populates `_shape_registry` with a `Shape` for every `BaseModel` subclass.

#### 4b — `validate_assignment=True` → implicit invariant

When the verifier encounters `account: Account` and the shape has
`validate_assignment=True`, it automatically:

1. Injects type guards (`isVZ`) as always-true preconditions
2. Tracks constraint obligations at every `CAss "account_balance" ...`
3. Generates the proof goal that the new value satisfies each constraint

No `is_valid` in the user contract.  The verifier knows the shape and
mode and acts accordingly.

#### 4c — Default mode → `is_valid` is explicit

The user writes `is_valid(r, Record)` in contracts.  The verifier
expands it to the constraint conjunction at codegen time.  Without
`is_valid` in the contracts, no constraint obligations are generated.

#### 4d — Replace ad-hoc `_scan_pydantic_fields`

`_scan_pydantic_fields` currently injects `Field(ge=0)` constraints as
unconditional preconditions.  This is wrong for default-mode models
(where constraints aren't enforced after mutation) and redundant for
`validate_assignment=True` models (where the Shape IR handles it).
Replace with Shape-IR-driven logic.

---

### Step 5 — User syntax

Field values use ordinary Python attribute syntax — `account.balance >= 0`,
`r.value == abs(n)`.  Already compiled by the existing `visit_Attribute`
path in the linter.  No new expression syntax needed.

`is_valid` is the only user-visible predicate:

```python
def guarded_mutation(r: Record, n: int) -> None:
    """
    axiomander:
        requires:
            is_valid(r, Record)
            r.value == n
        ensures:
            is_valid(r, Record)
            r.value == abs(n)
    """
    r.value = abs(n)
```

`is_shape` is never written by the user — the verifier injects it from
the `r: Record` type annotation.

---

### Step 6 — Tests

#### Positive

1. **`withdraw_validated`** — Account with `validate_assignment=True`,
   `is_valid` + `field_value` in requires/ensures.  Mutates
   `account.balance` with a provably-safe amount.  Proves at Level 1.

2. **`withdraw_bare_shape`** — Default-mode Account (no
   `validate_assignment`).  Only `field_value` in contracts — no
   `is_valid`.  Mutation silently sets arbitrary value.  Proves.
   Verifier does not check constraints.

#### Negative

3. **`withdraw_constraint_fail`** — `validate_assignment=True` model.
   Withdraws more than the balance.  The verifier must prove the
   constraint `b - amount >= 0` but cannot.  Rejected.

4. **`is_valid_broken`** — Default-mode model.  `is_valid` in
   precondition, but body sets a field to a violating value.  Ensures
   claims `is_valid` still holds.  Rejected.

---

## What is deferred

| Feature | Reason |
|---|---|
| `has_field`, `field_type` as user-visible predicates | Shape is compile-time; structural facts are never written by the user |
| `is_valid` auto-derivation from Pydantic construction | The verifier could recognise `Account(balance=100, ...)` as a validation point and automatically emit `is_valid` in the postcondition. For now, the user writes it explicitly. |
| Nested models (Address inside User) | Recursive shape expansion — Phase 2 of PDF plan |
| Collection shapes (list[int], dict[str, int]) | Phase 2 of PDF plan |
| Validator lowering (pure, complex, effectful categories) | Phase 3 of PDF plan |
| Heap regions, database regions, ownership | Phase 4 of PDF plan |
| `raises ExcType as e:` bound variable | Deferred until structured exception objects |

## In scope for this phase

| Feature | Status |
|---|---|
| Shape IR from Pydantic BaseModel definitions | Parses fields, types, Field constraints, `validate_assignment` mode |
| `field_value(obj, "name") = value` | User-visible predicate for field value reasoning |
| `is_valid(obj, ModelType)` | User-visible predicate; expands to constraint conjunction |
| `validate_assignment=True` → constraint obligations on mutation | Verifier proves constraints are preserved |
| Default mode → silent mutation, `is_valid` can break | No constraint obligations; user re-asserts validity |

---

## Files changed

| File | Change |
|---|---|
| `py/oracle/shape_ir.py` | **New.** `Shape`, `ShapeField`. `build_shape_registry()`, `shape_preconditions()`, `lookup_shape()`. Detects `validate_assignment` from `model_config`. |
| `py/oracle/contract_ir.py` | Add `IsShape`, `IsValid` nodes; update `Expr` union. |
| `py/oracle/contract_linter.py` | Recognise `is_shape(obj, Type)`, `is_valid(obj, Type)` in `visit_Call`. Add `_extract_name()` helper. |
| `py/oracle/docstring_contracts.py` | No changes — both predicates are expressions inside requires/ensures lines. |
| `py/oracle/mcp_server.py` | Call `build_shape_registry()` at verification start.  Use Shape IR for constraint injection when `is_valid` is in scope.  Generate constraint obligations on mutation for `validate_assignment=True` models. |
| `py/tests/test_pipeline.py` | 4 tests: 2 positive (one for each mode), 2 negative. |

---

## Risk assessment

| Risk | Mitigation |
|---|---|
| `_scan_pydantic_fields` currently injects unconditional constraints — replacing it changes behaviour for default-mode models | Default-mode models should never have had auto-injected constraints (Pydantic doesn't enforce them). This is a bug fix, not a regression. |
| `validate_assignment=True` must be detected from `model_config` | Parse `ConfigDict(validate_assignment=True)` in the class body AST. Fall back to `False` if not found. |
| Shape registry must be populated before linter runs | Call `build_shape_registry()` first thing in `_verify_function` |
| `field_value(obj, "name")` with a string literal for the field name is unusual Python | Syntactically valid; the linter intercepts it before any runtime eval |
| Constraint obligations add proof overhead for `validate_assignment=True` | They are linear arithmetic — `wp_prove` / `lia` handle them |
| Multiple models in scope could conflict on field names | The `obj_` prefix disambiguates — same as current flat state keys |
