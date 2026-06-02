# Pydantic Model Predicates — Implementation Plan

## Goal

Add two verifier-level predicates to the contract language so users can
reason about validated objects without knowing the flat state-key
encoding:

| Predicate | Meaning |
|---|---|
| `pydantic_model(obj, ModelType)` | `obj` is a validated instance of `ModelType` — all fields exist with correct types |
| `field(obj, "name", value)` | the field `obj.name` has logical value `value` |

Both are **pure predicates** (no ownership, no separation logic). They
compile to structural projections over the existing flat `obj_field` Coq
state representation. No new Coq definitions are required.

---

## Current state (pre-implementation)

Today, a class parameter `account: Account` is **structurally flattened** at
translation time: the fields `balance: int`, `overdraft_limit: int` become
separate Coq state keys `"account_balance"%string`, `"account_overdraft_limit"%string`.
The init state is built by `_expand_params` (mcp_server.py:2146) and
Pydantic `Field(ge=..., le=...)` constraints are injected as preconditions
by `_scan_pydantic_fields` (mcp_server.py:2281).

Contracts reference these flat keys indirectly: `account.balance` in a
contract compiles to `asZ (s "account_balance"%string) = ...`. The user
must mentally map `account.balance -> account_balance`. There is no
verifier-level concept of "this object is valid."

## Target state (post-implementation)

The user writes:

```python
def withdraw(account: Account, amount: int) -> int:
    """
    axiomander:
        where:
            b: int
        requires:
            pydantic_model(account, Account)
            field(account, "balance", b)
            amount >= 0
            b >= amount
        modifies:
            account
        ensures:
            field(account, "balance", b - amount)
            result == b - amount
    """
    account.balance -= amount
    return account.balance
```

The verifier compiles this to:

```coq
(* precondition *)
pydantic_model:  (isVZ (s "account_balance"%string) = true /\
                  isVZ (s "account_overdraft_limit"%string) = true)
field:           (asZ (s "account_balance"%string) = b)
amount >= 0:     (amount >= 0)
b >= amount:     (b >= amount)

(* postcondition *)
field:           (asZ (s "account_balance"%string) = b - amount)
result:          (asZ (s "result"%string) = b - amount)
```

---

## Implementation steps

### Step 1 — Contract IR nodes (`contract_ir.py`)

Add to the `Expr` union:

```python
class FieldPred(BaseModel):
    """field(obj, "name", value) — obj.name has logical value value.

    Compiles to a state lookup on the flat key "obj_field":
        asZ (s "account_balance"%string) = value_coq
    """
    kind: Literal["field"] = "field"
    obj: str          # Python variable name, e.g. "account"
    field_name: str   # attribute name, e.g. "balance"
    value: Expr       # logical value expression

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        flat_key = f'{self.obj}_{self.field_name}'
        val_coq = self.value.to_coq(scoped, unbound)
        return f'(asZ (s "{flat_key}"%string) = {val_coq})'

    def to_smt(self) -> str:
        return f"(= {self.obj}_{self.field_name} {self.value.to_smt()})"


class ObjectModelPred(BaseModel):
    """pydantic_model(obj, ModelType) — obj is a validated instance.

    Expands to the conjunction of type guards for all fields declared on
    ModelType.  Expansion requires knowledge of the class schema, which
    is provided at linter time (the linter looks up the class AST).

    For a model with fields balance: int, overdraft_limit: int:
        isVZ (s "obj_balance"%string) = true /\
        isVZ (s "obj_overdraft_limit"%string) = true
    """
    kind: Literal["object_model"] = "object_model"
    obj: str
    model_type: str

    def expand_to_coq(self, field_names: list[str], scoped: bool = False) -> str:
        guards = []
        for fname in field_names:
            flat_key = f'{self.obj}_{fname}'
            guards.append(f'(isVZ (s "{flat_key}"%string) = true)')
        return " /\\ ".join(guards) if guards else "True"

    def to_smt(self) -> str:
        return "true"  # type guards are Coq-level only; SMT sees the flat vars directly
```

#### Design decision: `ObjectModelPred` does not bind a logical data variable

The Nagini doc uses `pydantic_model(user, User, U)` with `U` as a logical
map that can be indexed (`U["id"]`, `U["name"]`). This requires:

1. A map/record type in the contract IR
2. Map indexing expressions (`MapGet(U, "id")`)
3. Map update expressions for postconditions

This is deferred. The first version treats `pydantic_model` as a **type
guard only** — it says "the fields exist and have the right types" but
does not bind a structured data value.

---

### Step 2 — Linter support (`contract_linter.py`)

#### 2a — Accept function call forms

Add `field` and `pydantic_model` as recognized names alongside `implies`
and `raises` in `visit_Call` (contract_linter.py:190):

```python
if name == "field":
    # field(obj, "field_name", value)
    if len(node.args) == 3:
        obj = self._extract_name(node.args[0])
        fname = self._extract_string_literal(node.args[1])
        val = self.visit(node.args[2])
        if obj and fname and val:
            return FieldPred(obj=obj, field_name=fname, value=val)
    return None

if name == "pydantic_model":
    # pydantic_model(obj, ModelType)
    if len(node.args) == 2:
        obj = self._extract_name(node.args[0])
        type_name = self._extract_name(node.args[1])
        if obj and type_name:
            return ObjectModelPred(obj=obj, model_type=type_name)
    return None
```

Helper methods needed:
- `_extract_name(node)` — returns `str` if node is `ast.Name`, else `None`
- `_extract_string_literal(node)` — returns `str` if node is `ast.Constant(value=str)`, else `None`

#### 2b — Linter needs access to the source tree

`ObjectModelPred` requires knowing which fields a class has. The
`ContractLinter` class already has `self.source_text` (the expanded
source) and `self.predicates`. We need to add `self.source_tree: ast.Module |
None` and look up `ast.ClassDef` nodes by name.

When creating the linter in `mcp_server.py`, pass the full source tree:

```python
linter = ContractLinter(expanded, "precondition",
                         predicates=predicates,
                         source_tree=tree)
```

#### 2c — Class schema lookup

In `ContractLinter`:

```python
def _get_model_fields(self, model_type: str) -> list[str]:
    """Return field names for a Pydantic model class."""
    if not self.source_tree:
        return []
    for node in ast.walk(self.source_tree):
        if isinstance(node, ast.ClassDef) and node.name == model_type:
            fields = []
            for stmt in node.body:
                if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                    fields.append(stmt.target.id)
            return fields
    return []
```

---

### Step 3 — Coq compilation of contract expressions

#### `FieldPred.to_coq()`

Flatten `obj.field_name` → `"obj_field_name"%string`.

Precondition (unscoped): the value var is bare:
```coq
asZ (s "account_balance"%string) = b
```

Postcondition (scoped): the state variable `s` is used:
```coq
asZ (s "account_balance"%string) = asZ (s "b"%string)
```

The value expression's own `to_coq(scoped=...)` handles its scoping.

#### `ObjectModelPred` → expansion

Because `ObjectModelPred` needs the class schema to compile, it cannot
emit Coq directly via `to_coq()`. Instead, the `ContractLinter`
expands it at lint time. Two approaches:

**Approach A (preferred):** Expand at lint time. When the linter
encounters `pydantic_model(account, Account)`, look up the Account
class definition and emit a `Logical` conjunction of `FieldPred`
guards (one per field). The IR never stores an unexpanded
`ObjectModelPred` node.

**Approach B:** Store the node unexpanded and expand at codegen time.

Approach A is simpler and avoids threading the source tree through the
entire pipeline. The `ContractLinter` already has the source tree; it
expands `pydantic_model` into the constituent `isVZ` guards immediately.

#### The `to_coq()` for `ObjectModelPred` still needs to exist

For the case where `contract_ir.Expr` is used standalone (e.g., SMT
export), `to_coq()` returns `"True"` since the guards are generated at
linter time. This is fine because the linter never produces a raw
`ObjectModelPred` in the output — it always expands it first.

---

### Step 4 — User syntax

Both docstring and assert forms are supported:

**Docstring (preferred):**

```python
def withdraw(account: Account, amount: int) -> int:
    """
    axiomander:
        where:
            b: int
        requires:
            pydantic_model(account, Account)
            field(account, "balance", b)
            amount >= 0
            b >= amount
        modifies:
            account
        ensures:
            field(account, "balance", b - amount)
            result == b - amount
    """
    account.balance -= amount
    return account.balance
```

**Assert form (internal / backward compat):**

```python
def withdraw(account: Account, amount: int) -> int:
    assert pydantic_model(account, Account)
    assert field(account, "balance", b)
    assert amount >= 0
    assert b >= amount
    account.balance -= amount
    assert field(account, "balance", b - amount)
    assert result == b - amount
    return result
```

The docstring form is the recommended path. The assert form works because
`pydantic_model` and `field` are recognized by the linter before any
runtime name resolution.

---

### Step 5 — Wire through mcp_server.py

#### 5a — Linter constructor

Pass the source tree when creating linters:

```python
# In _verify_function (mcp_server.py ~1082)
linter_pre = ContractLinter(expanded, "precondition",
                             predicates=predicates,
                             unbound=ghost_var_names,
                             source_tree=tree)
linter_post = ContractLinter(expanded, "postcondition",
                              predicates=predicates,
                              unbound=ghost_var_names,
                              source_tree=tree)
```

#### 5b — No changes to VCG, theorem generation, or Coq

Since `field` and `pydantic_model` compile to plain state predicates
(`asZ (s "key"%string) = ...` and `isVZ (s "key"%string) = true`),
existing `wp_reduce`, `wp_prove`, and SMT pipeline work without changes.
The predicates are just more conjunctions in the pre/post.

#### 5c — Frame conditions

`field(account, "balance", b)` implies that `account.balance` is
referenced. Frame analysis already handles this via the existing purity
analysis and `modifies` declarations. No new frame machinery needed.

---

### Step 6 — Tests

Add to `test_pipeline.py`:

#### Positive tests

1. **`withdraw_model`** — `pydantic_model` + `field` in requires/ensures.
   The function mutates `account.balance`. Proves at Level 1.

```python
def withdraw_model(balance: int, overdraft: int, amount: int) -> int:
    """
    axiomander:
        requires:
            balance >= 0
            amount >= 0
            balance >= amount
        ensures:
            result == balance - amount
    """
    result = balance - amount
    return result
```

   (Uses bare params since class flattening in tests is complex. A
   simpler version: just verify `field` compiles to the right state
   lookup.)

2. **`check_model`** — `pydantic_model` type guard test. Uses a
   multi-field class and verifies the type guard expands correctly.

#### Negative tests

3. **`field_wrong`** — wrong field value in ensures. Rejected.
4. **`model_missing_field`** — references a field not in the model. Rejected by linter.

---

## What is NOT included (deferred)

| Feature | Reason |
|---|---|
| `pydantic_model(obj, Type, data)` with logical data variable | Requires map/record types in the contract IR — complex. Deferred. |
| `owns(obj)` ownership predicate | Requires separation logic framing — Phase 4 of migration plan. |
| `acc(obj.field)` permission predicate | Requires separation logic + fractional permissions. |
| `list_model`, `dict_model`, `set_model` | Separate shape predicates. Pure, but large scope. |
| DB/transaction predicates | Phase 6 of migration plan — separate from object modeling. |
| `raises ExcType as e:` with bound variable | Deferred until we have structured exception objects. |

---

## Files changed

| File | Change |
|---|---|
| `py/oracle/contract_ir.py` | Add `FieldPred`, `ObjectModelPred` nodes; update `Expr` union |
| `py/oracle/contract_linter.py` | Add `field()`, `pydantic_model()` special forms; add `source_tree` parameter; add `_get_model_fields()`; add `_extract_name()`, `_extract_string_literal()` helpers |
| `py/oracle/docstring_contracts.py` | No changes needed — `field()` and `pydantic_model()` are parsed as regular function calls in expression context |
| `py/oracle/mcp_server.py` | Pass `source_tree` to linter constructors (~2 lines) |
| `py/tests/test_pipeline.py` | Add 4 tests (2 positive, 2 negative) |

No Coq files changed. No new Coq definitions. The predicates compile to
existing state lookups.

---

## Risk assessment

| Risk | Mitigation |
|---|---|
| `ObjectModelPred` expansion depends on class AST being available at lint time | The linter already receives the source tree; fall back to "True" if class not found |
| Field name → flat key mapping must match `_expand_params` | Use the same naming convention (`f"{obj}_{field}"`) consistently |
| Multiple models in scope could conflict on field names | The `obj_` prefix disambiguates — same as current flat state keys |
| `isVZ` guards add proof overhead | They are trivial linear arithmetic — `wp_prove` handles them |
