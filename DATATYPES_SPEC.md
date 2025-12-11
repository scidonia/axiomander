
# Datatype Encoding for `None` and Optional Values in Python → Z3  
### Specification for the Agent

This document describes how the agent should encode **Python `None`** and **optional values** using **Z3 datatypes**.  
The goal is to provide a clean, consistent logical model that works well with weakest preconditions and counterexample search.

---

## 1. High-Level Idea

Python uses `None` as a sentinel for “no value” or “optional value”.  
In SMT, we model this using **Option-style datatypes**:

- For a base type `T`, we create a datatype `OptionT` with two constructors:
  - `None` – represents Python `None`.
  - `Some(value: T)` – represents a present value of type `T`.

This avoids overloading `None` into unrelated sorts (e.g., using a magic integer) and keeps reasoning predictable.

---

## 2. Datatype Definition Pattern

For each base type `T` that can be `None`, the agent should:

1. **Define a datatype** in Z3:

   ```python
   from z3 import *

   OptionInt = Datatype('OptionInt')
   OptionInt.declare('None')                   # represents Python None
   OptionInt.declare('Some', ('value', IntSort()))
   OptionInt = OptionInt.create()

   NoneInt = OptionInt.None
   SomeInt = OptionInt.Some
   valInt  = OptionInt.value  # projector
   ```

2. Reuse these definitions for all variables of type “optional int”.

Repeat the pattern as needed:

- `OptionBool` for `bool` + `None`
- `OptionStr` for `str` + `None`
- etc.

---

## 3. Mapping Python Constructs to Datatypes

The agent must follow these mapping rules.

### 3.1 Literal `None`

- Python:

  ```python
  None
  ```

- SMT:

  ```python
  OptionT.None
  ```

Use the appropriate `OptionT` sort for the variable’s logical type.

---

### 3.2 Concrete values

- Python (for an `int`-like optional):

  ```python
  42
  ```

- SMT:

  ```python
  SomeInt(IntVal(42))
  ```

In general:

- `v : T` → `OptionT.Some(encode(v))`

Where `encode(v)` is the usual embedding of the base type `T` into SMT (e.g., `IntVal`, `StringVal`, etc.).

---

### 3.3 Equality and `is` checks

For optional values, treat Python `is` and `==` against `None` identically:

- Python:

  ```python
  x is None
  x == None
  ```

- SMT:

  ```python
  x == OptionT.None
  ```

Similarly:

- Python:

  ```python
  x is not None
  x != None
  ```

- SMT:

  ```python
  x != OptionT.None
  ```

We are **not** modeling full Python object identity here, only the `None` sentinel pattern.

---

### 3.4 Accessing the underlying value

When the code uses the underlying value stored inside an Option, the agent must:

1. Ensure it is under a guard that rules out `None`:

   - Python:

     ```python
     if x is not None:
         y = x + 1
     ```

   - SMT (schematic):

     ```smt2
     (and
       (x != NoneInt)
       (= y (+ (valInt x) 1)))
     ```

2. Use the datatype projector `value` to extract the underlying base-type value:

   ```python
   valInt(x)  # only safe under x != NoneInt
   ```

The WP rules over `if` statements already provide the necessary path-splitting.

---

## 4. Variable Sort Selection

The agent must pick the appropriate sort for each variable:

1. If a variable is known (from type hints or usage) to be:
   - Only `int` → use `IntSort()`.
   - Only `bool` → use `BoolSort()`.
   - Only `str` → use `StringSort()` (or custom).
2. If a variable can be **either** a base-type value or `None`, it must use the corresponding `OptionT` sort.

Examples:

- A function annotation:

  ```python
  def f(x: Optional[int]) -> Optional[int]:
      ...
  ```

  → `x` and `return` are modeled as `OptionInt`.

- If no type hints exist, the agent may infer “possibly None” from usage (e.g., `x = None`, or `if x is None`).

---

## 5. Alternative Lightweight Encoding (Optional)

For variables that:

- Never participate in arithmetic or ordering, and
- Are only compared to `None`,

the agent may use a simplified encoding:

1. Introduce an uninterpreted sort `Ref`.
2. Introduce a distinguished constant:

   ```smt2
   (declare-sort Ref 0)
   (declare-const Null Ref)
   ```

3. Encode:

   - `None` → `Null`
   - `x is None` / `x == None` → `x == Null`
   - `x is not None` / `x != None` → `x != Null`

This is sufficient when the tool only cares about *presence vs absence* and never needs the underlying value.

However, for “maybe int”, “maybe bool”, etc., the **Option datatype encoding is preferred**.

---

## 6. Interaction with WP and Contracts

The Option encoding integrates smoothly with weakest preconditions and contracts:

- Conditions like `x is not None` generate path splits in the WP:
  - On the branch `x != NoneT`, the agent is allowed to use the projector `value(x)`.
  - On the branch `x == NoneT`, any attempt to use `value(x)` should either:
    - Be avoided; or
    - Be treated as undefined / lead to a verification failure.

- Contracts can mention optional values directly:

  ```python
  @ensures(lambda x, r: (x is None) or (r is not None))
  ```

  which embeds as constraints over `OptionT` values with equality checks to `None`.

---

## 7. Summary of Rules for the Agent

1. Use **Option-style datatypes** for any Python value that can be `None`:
   - `OptionT = Datatype('OptionT')` with constructors `None` and `Some(value : T)`.
2. Map:
   - `None` → `OptionT.None`
   - Base value `v : T` → `OptionT.Some(encode(v))`
3. Translate sentinel checks:
   - `x is None` / `x == None` → `x == OptionT.None`
   - `x is not None` / `x != None` → `x != OptionT.None`
4. Only use the projector `OptionT.value(x)` under the guard `x != OptionT.None`.
5. For simple “presence-only” Vars, an alternative `Ref` + `Null` encoding is allowed, but **Option datatypes are preferred for typed optionals.**

This encoding keeps the SMT model for `None` and optional values:

- **Sound enough** for verification-assisted linting,
- **Structured enough** to work well with your WP and contract machinery, and
- **Simple enough** for the agent to implement systematically.
