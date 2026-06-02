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

### What the user writes

```python
class Account(BaseModel):
    balance: int = Field(ge=0)
    overdraft_limit: int

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

No `pydantic_model(account, Account)` contract is needed.  The
`account: Account` annotation tells the verifier the shape.
`field_value` is the only user-visible shape predicate.

### What the verifier knows automatically

From `account: Account` and the Account class definition, the verifier
derives:

```
Shape(Account):
  field(balance, int, constraints=[ge=0])
  field(overdraft_limit, int)
```

This Shape IR is lowered to:

```coq
(* Implicit from the type annotation -- not written by the user *)
(* balance >= 0  (from Field(ge=0)) *)
(* isVZ (s "account_balance"%string) = true *)
(* isVZ (s "account_overdraft_limit"%string) = true *)
```

The constraints and type guards are **automatically injected** as
preconditions, just as `_scan_pydantic_fields` does today.

### What `field_value(obj, "name") = v` compiles to

```coq
asZ (s "account_balance"%string) = v
```

Exactly the same state lookup as the existing `account.balance` →
`account_balance` flattening.  The predicate just makes the mapping
explicit in the contract language.

---

## Implementation steps

### Step 1 — Shape IR (`py/oracle/shape_ir.py`, new file)

A standalone module for the Shape IR.  This is **compiled from Pydantic
models at verifier startup**, not written by the user.

```python
class ShapeField(BaseModel):
    """A single field in a shape."""
    name: str              # e.g. "balance"
    coq_type: str          # e.g. "Z", "string", "bool"
    constraints: list[str] = Field(default_factory=list)  # Coq predicates, e.g. "0 <= {flat_key}"

class Shape(BaseModel):
    """The shape of a Pydantic model."""
    name: str              # e.g. "Account"
    fields: list[ShapeField]
    flat_key_for: dict[str, str] = Field(default_factory=dict)  # "balance" → "obj_balance"
```

`flat_key_for` maps the user-visible field name to the Coq state key,
incorporating the object prefix.  For `account: Account`:
- `"balance"` → `"account_balance"`
- `"overdraft_limit"` → `"account_overdraft_limit"`

#### Shape registry

A module-level cache mapping qualified Python class names → `Shape`:

```python
_shape_registry: dict[str, Shape] = {}
```

Populated by `_build_shape_registry()` which walks the source AST,
finds all `ClassDef` nodes that inherit from `BaseModel`, and builds
a `Shape` for each.

#### Shape → Coq preconditions

```python
def shape_preconditions(shape: Shape, obj_prefix: str) -> list[str]:
    """Return Coq preconditions implied by a shape.
    
    For Account with prefix "account":
      - "isVZ (s \"account_balance\"%string) = true"
      - "isVZ (s \"account_overdraft_limit\"%string) = true"
      - "0 <= asZ (s \"account_balance\"%string)"  (from Field(ge=0))
    """
```

These are injected into the pre/post just like `_scan_pydantic_fields`
does today, but driven by the Shape IR rather than ad-hoc AST scanning.

---

### Step 2 — Contract IR predicate (`contract_ir.py`)

Only one new predicate node: `FieldValue`.  `has_field` and
`field_type` are handled automatically by the Shape IR and do not need
contract-level nodes.

```python
class FieldValue(BaseModel):
    """field_value(obj, "field_name") = value.

    Compiles to a state lookup on the flat key:
        asZ (s "obj_field"%string) = value_coq

    The obj → flat_key mapping comes from the Shape registry.
    """
    kind: Literal["field_value"] = "field_value"
    obj: str          # variable name, e.g. "account"
    field_name: str   # attribute name, e.g. "balance"
    value: Expr       # logical value expression

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        from .shape_ir import _shape_registry
        # Determine the flat key.  If we have a shape for this obj's type,
        # use its key map.  Otherwise fall back to obj_field naming.
        flat_key = f'{self.obj}_{self.field_name}'
        val_coq = self.value.to_coq(scoped, unbound)
        return f'(asZ (s "{flat_key}"%string) = {val_coq})'

    def to_smt(self) -> str:
        return f"(= {self.obj}_{self.field_name} {self.value.to_smt()})"
```

**No `ObjectModelPred` / `pydantic_model` node.**  Shape validation is
automatic from type annotations + the Shape registry.

---

### Step 3 — Linter (`contract_linter.py`)

#### 3a — Recognise `field_value(obj, "name") = value`

This is not a standalone call.  It appears inside a comparison: the
user writes `field_value(account, "balance") = b` which the Python AST
parses as:

```
Compare(
    left=Call(func=Name("field_value"), args=[Name("account"), Constant("balance")]),
    ops=[Eq()],
    comparators=[Name("b")]
)
```

The linter needs to recognise `field_value(...)` as the left side of a
comparison and extract the `value` expression from the right side.

In `visit_Compare` (contract_linter.py):

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
    # existing compare logic follows
    ...
```

#### 3b — No new source_tree dependency

The `visit_Compare` approach does **not** require the source tree,
because `field_value` has all the information in its arguments.  The
flat key mapping is handled by `FieldValue.to_coq()` consulting the
Shape registry at codegen time.

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

Add to `test_pipeline.py`:

#### Positive

1. **`withdraw_model`** — multi-field Account model with `Field(ge=0)`,
   `field_value` in requires/ensures.  Mutates `account.balance` via
   flat state assignment.  Shape IR injects the `ge=0` constraint
   automatically.  Proves at Level 1.

2. **`shape_implicit`** — function with `account: Account` parameter,
   no `field_value` calls, just bare assertions.  The Shape IR
   injects type guards and Field constraints automatically.
   Verifier proves the function without any object-specific contracts.

#### Negative

3. **`field_value_wrong`** — wrong value in ensures `field_value(...)`
   relative to the body.  Rejected.

4. **`shape_constraint_violated`** — body violates an auto-injected
   Field constraint (e.g. sets balance < 0 when Field(ge=0) is
   declared).  Rejected.

---

## What is deferred

| Feature | Reason |
|---|---|
| `has_field`, `field_type` as user-visible predicates | Shape is compile-time; these are never written by the user |
| `pydantic_model(obj, Type)` validation predicate | Validation is implicit from type annotations + Shape IR |
| `field_value` as a getter (no `= value`) | Always used in equality form; getter-only is YAGNI for now |
| Nested models (Address inside User) | Recursive shape expansion — Phase 2 of PDF plan |
| Collection shapes (list[int], dict[str, int]) | Phase 2 of PDF plan |
| Validator lowering | Phase 3 of PDF plan |
| Heap regions, database regions | Phase 4 of PDF plan |
| `raises ExcType as e:` bound variable | Deferred until structured exception objects |

---

## Files changed

| File | Change |
|---|---|
| `py/oracle/shape_ir.py` | **New.** Shape, ShapeField classes. `build_shape_registry()`, `shape_preconditions()`, `lookup_shape()`. |
| `py/oracle/contract_ir.py` | Add `FieldValue` node; update `Expr` union. |
| `py/oracle/contract_linter.py` | Recognise `field_value(obj, "name") = val` in `visit_Compare`. Add `_extract_name()`, `_extract_string_literal()` helpers. |
| `py/oracle/docstring_contracts.py` | No changes. `field_value(...)` is an expression inside requires/ensures lines. |
| `py/oracle/mcp_server.py` | Call `build_shape_registry()` at verification start.  Replace ad-hoc `_scan_pydantic_fields` with Shape-IR-driven precondition injection. |
| `py/tests/test_pipeline.py` | 4 tests (2 positive, 2 negative). |

No Coq files changed.  Shape constraints compile to existing `isVZ`/`asZ`
state predicates.

---

## Risk assessment

| Risk | Mitigation |
|---|---|
| Shape registry must be populated before linter runs | Call `build_shape_registry()` first thing in `_verify_function` |
| `FieldValue.to_coq()` needs Shape registry for key mapping | Fall back to `f"{obj}_{field}"` convention if registry has no entry |
| Existing `_scan_pydantic_fields` must not conflict with Shape IR injection | Replace `_scan_pydantic_fields` entirely — the Shape IR is the single source |
| `field_value(obj, "name")` with a string literal is unusual Python | Syntactically valid; the linter intercepts it before any runtime eval |
