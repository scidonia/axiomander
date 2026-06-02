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

### Mode 1: `validate_assignment=True` (constraints enforced by Pydantic)

The verifier must prove constraints hold at every mutation, matching
Pydantic's runtime behaviour:

```python
class Account(BaseModel):
    model_config = ConfigDict(validate_assignment=True)
    balance: int = Field(ge=0)
    overdraft: int

def withdraw(account: Account, amount: int) -> int:
    """
    axiomander:
        where:
            b: int
        requires:
            is_valid(account, Account)
            field_value(account, "balance") = b
            amount >= 0
            b >= amount
        modifies:
            account
        ensures:
            is_valid(account, Account)
            field_value(account, "balance") = b - amount
            result == b - amount
    """
    account.balance -= amount    # verifier proves: b - amount >= 0
    return account.balance
```

The verifier knows from the shape that `balance: int = Field(ge=0)`, so
it generates the proof obligation `b - amount >= 0` at the mutation.
If `amount > b`, verification fails — matching the `ValidationError`
that Pydantic would raise at runtime.

### Mode 2: Default (no `validate_assignment`)

Constraints are NOT enforced on mutation.  The verifier tracks
`is_valid` as a predicate that can break:

```python
class Record(BaseModel):
    value: int = Field(ge=0)

def maybe_break(r: Record, n: int) -> int:
    """
    axiomander:
        requires:
            is_valid(r, Record)
            field_value(r, "value") = n
        ensures:
            field_value(r, "value") = -n    # constraint is violated but
            result == -n                    # no ValidationError at runtime
    """
    r.value = -n    # silently succeeds — is_valid is now false
    return r.value
```

The verifier does NOT generate a constraint obligation for `r.value = -n`.
It notes that `is_valid(r, Record)` is false after the mutation.
The user can explicitly re-validate:

```python
def fix(r: Record) -> None:
    """
    axiomander:
        ensures:
            is_valid(r, Record)
    """
    r.value = abs(r.value)   # re-establish validity
```

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

Two new predicates:

```python
class FieldValue(BaseModel):
    """field_value(obj, "field_name") = value.

    Always available — structural, regardless of validity.
    Compiles to: asZ (s "obj_field"%string) = value_coq
    """
    kind: Literal["field_value"] = "field_value"
    obj: str
    field_name: str
    value: Expr


class IsValid(BaseModel):
    """is_valid(obj, ModelType) — the object satisfies all declared constraints.

    True after construction.  The verifier tracks this predicate.
    With validate_assignment=True, must be re-proven after every mutation.
    In default mode, can be broken by mutation; user re-asserts it.
    
    Compiles to the conjunction of all Field constraints for the model:
      (asZ (s "obj_balance"%string) >= 0) /\ ...
    """
    kind: Literal["is_valid"] = "is_valid"
    obj: str
    model_type: str
```

`IsValid` expansion depends on the Shape registry.  At linter time, if
the Shape is known, expand to the constraint conjunction.  If the
Shape is not yet in the registry (rare), emit a placeholder that is
resolved at codegen time.

---

### Step 3 — Linter (`contract_linter.py`)

#### 3a — `field_value(obj, "name") = value` in comparisons

`visit_Compare` recognises `field_value(...)` as the left side of `==`:

```python
def visit_Compare(self, node: ast.Compare) -> Optional[Expr]:
    if len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq):
        left = node.left
        right = self.visit(node.comparators[0])
        if isinstance(left, ast.Call) and self._get_call_name(left) == "field_value":
            if len(left.args) == 2 and right:
                obj = self._extract_name(left.args[0])
                fname = self._extract_string_literal(left.args[1])
                if obj and fname:
                    return FieldValue(obj=obj, field_name=fname, value=right)
    # ... existing compare logic
```

#### 3b — `is_valid(obj, ModelType)` as a special form

Added to `visit_Call` alongside `implies` and `raises`:

```python
if name == "is_valid":
    if len(node.args) == 2:
        obj = self._extract_name(node.args[0])
        type_name = self._extract_name(node.args[1])
        if obj and type_name:
            return IsValid(obj=obj, model_type=type_name)
    return None
```

#### 3c — No `source_tree` required

Both `field_value` and `is_valid` carry all information in their
arguments.  The Shape registry is consulted at codegen time, not at
lint time.  No change to `ContractLinter.__init__`.

---

### Step 4 — Automatic shape injection (`mcp_server.py`)

#### 4a — Build the Shape registry at verification time

In `_verify_function`, after `tree = ast.parse(source)`:

```python
from oracle.shape_ir import build_shape_registry
build_shape_registry(tree)
```

This populates the global `_shape_registry` with a `Shape` for every
`BaseModel` subclass in the source.

#### 4b — Inject shape preconditions automatically

When building the precondition list, scan function parameters:

```python
for arg, annot in _func_params(func_node):
    shape = lookup_shape(annot)  # e.g. "Account" → Shape(Account)
    if shape:
        prefix = arg  # e.g. "account"
        guards = shape_preconditions(shape, prefix)
        implicit_pres.extend(guards)
```

This replaces the manual `_scan_pydantic_fields` call.  The Shape IR
is the single source of truth for what a model implies.

#### 4c — Frame conditions from shapes

When analysing `modifies: account`, the Shape IR tells the verifier
which fields are affected (`account_balance`, `account_overdraft_limit`).
Frame lemmas for CCall can use this directly.

---

### Step 5 — User syntax

**Docstring (the only user-facing form for `field_value`):**

```python
def withdraw(account: Account, amount: int) -> int:
    """
    axiomander:
        where:
            b: int
        requires:
            field_value(account, "balance") = b
            amount >= 0
            b >= amount
        modifies:
            account
        ensures:
            field_value(account, "balance") = b - amount
            result == b - amount
    """
    account.balance -= amount
    return account.balance
```

The Shape IR handles the rest:
- `balance: int → Field(ge=0)` → implicit `b >= 0` precondition
- `overdraft_limit: int` → implicit `isVZ (s "account_overdraft_limit"%string) = true`
- `account.balance -= amount` → state update on `"account_balance"%string`

`field_value` appears only when the user needs to name a field's value
for use in the contract.  If they don't need a named value, the shape's
automatic constraints are sufficient.

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
| `py/oracle/contract_ir.py` | Add `FieldValue`, `IsValid` nodes; update `Expr` union. |
| `py/oracle/contract_linter.py` | Recognise `field_value(obj, "name") = val` in `visit_Compare`. Recognise `is_valid(obj, Type)` in `visit_Call`. Add `_extract_name()`, `_extract_string_literal()` helpers. |
| `py/oracle/docstring_contracts.py` | No changes — both predicates are expressions inside requires/ensures lines. |
| `py/oracle/mcp_server.py` | Call `build_shape_registry()` at verification start.  Use Shape IR for constraint injection when `is_valid` is in scope.  Generate constraint obligations on mutation for `validate_assignment=True` models. |
| `py/tests/test_pipeline.py` | 4 tests: 2 positive (one for each mode), 2 negative. |

---

## Risk assessment

| Risk | Mitigation |
|---|---|
| Shape registry must be populated before linter runs | Call `build_shape_registry()` first thing in `_verify_function` |
| `FieldValue.to_coq()` needs Shape registry for key mapping | Fall back to `f"{obj}_{field}"` convention if registry has no entry |
| Existing `_scan_pydantic_fields` must not conflict with Shape IR injection | Replace `_scan_pydantic_fields` entirely — the Shape IR is the single source |
| `field_value(obj, "name")` with a string literal is unusual Python | Syntactically valid; the linter intercepts it before any runtime eval |
