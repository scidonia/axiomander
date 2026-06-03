# Axiomander Contract Language Reference

Axiomander contracts are written in a small sublanguage embedded in Python
docstrings.  The sublanguage is **verifier-only** — it never executes at
runtime, imposes no imports, and leaves the function body unchanged.

---

## 1. Contract Carriers

### 1.1 Body `assert` statements

`assert` is executable Python. Axiomander classifies body asserts by position:

| Position | Classification |
|---|---|
| First statements, before any non-assert code | Precondition |
| Inside a loop body, before any non-assert code | Loop invariant |
| After the main computation, before `return` | Postcondition |

```python
def clamp(val: int, lo: int, hi: int) -> int:
    assert lo <= hi           # precondition
    if val < lo:
        result = lo
    elif val > hi:
        result = hi
    else:
        result = val
    assert lo <= result <= hi  # postcondition
    return result
```

### 1.2 Docstring `axiomander:` blocks

Docstring contracts are parsed by Axiomander but **never evaluated at
runtime**.  They are the preferred carrier for ghost bindings, frame
declarations, exception contracts, and dimensional annotations.

```python
def inc(x: int) -> int:
    """
    axiomander:
        requires:
            x >= 0
        ensures:
            result == x + 1
    """
    result = x + 1
    return result
```

The block begins at `axiomander:` and ends at the next dedented line.
Section headers are `requires:`, `ensures:`, `where:`, `reads:`,
`modifies:`, `raises:`, and `units:`.

---

## 2. Sections

### 2.1 `requires:` — Preconditions

One expression per line. All lines are conjoined. Evaluated in the
pre-state (before the function body executes).

```
axiomander:
    requires:
        n >= 0
        len(items) > 0
        is_shape(account)
```

**Allowed operators in `requires:`** — see Section 3.

### 2.2 `ensures:` — Postconditions

One expression per line. All lines are conjoined. Evaluated in the
post-state. The special name `result` refers to the return value.

```
axiomander:
    ensures:
        result >= 0
        result <= len(items)
        result == old(n) + 1
```

`result.field` accesses a field of a structured return value.

### 2.3 `where:` — Ghost bindings

Binds a ghost name to an expression evaluated in the **pre-state**.
Used to snapshot values before the body modifies them.

```
axiomander:
    where:
        old_balance: int = account.balance
    ensures:
        account.balance == old_balance - amount
```

`old(x)` in `ensures:` is shorthand for `where: old_x = x` plus
using `old_x` in the postcondition.

```python
def withdraw(account, amount: int) -> int:
    """
    axiomander:
        ensures:
            result == old(account.balance) - amount
    """
```

### 2.4 `reads:` — Read frame

Declares which variables the function reads.  Currently informational;
used by the purity analyser.

```
axiomander:
    reads:
        account.balance
        config
```

### 2.5 `modifies:` — Write frame

Declares which variables the function may mutate.  Variables not listed
are guaranteed unchanged across a call (frame condition).

```
axiomander:
    modifies:
        none          # pure function
```

```
axiomander:
    modifies:
        account.balance
```

Callers prove that variables outside `target :: modifies` are preserved.

### 2.6 `raises:` — Exception postconditions

Declares what is true at the raise point for each exception type.

```
axiomander:
    requires:
        n >= 0
    ensures:
        result >= 0
    raises:
        ValueError: n < 0
        OverflowError: n > 1000000
```

Format: `ExcType: condition_expression`.  The condition is evaluated in
the state at the point the exception is raised.

Multiple exception types are each on their own line.

### 2.7 `units:` — Dimensional annotations

Declares the physical or semantic dimension of each parameter and the
return value.  The dimension checker verifies that all arithmetic
operations in the body are dimensionally consistent.

```
axiomander:
    units:
        revenue:  [USD]
        users:    [person]
        result:   [USD/person]
```

See Section 5 for the full dimensional analysis reference.

---

## 3. Expression Language

All `requires:` and `ensures:` expressions use the following constructs.

### 3.1 Arithmetic

| Operator | Meaning |
|---|---|
| `a + b` | addition |
| `a - b` | subtraction |
| `a * b` | multiplication |
| `a / b` | division |
| `a // b` | floor division |
| `a % b` | modulo |
| `a ** n` | power (integer exponent) |
| `-a` | negation |
| `abs(a)` | absolute value |
| `min(a, b)` | minimum |
| `max(a, b)` | maximum |

### 3.2 Comparison

| Operator | Meaning |
|---|---|
| `a == b` | equality |
| `a != b` | inequality |
| `a < b` | strictly less |
| `a <= b` | less or equal |
| `a > b` | strictly greater |
| `a >= b` | greater or equal |
| `a <= b <= c` | chained comparison |

### 3.3 Logic

| Operator | Meaning |
|---|---|
| `P and Q` | conjunction |
| `P or Q` | disjunction |
| `not P` | negation |
| `implies(P, Q)` | logical implication (P → Q) |

`implies(P, Q)` is the preferred idiom for conditional postconditions.
It is equivalent to `not P or Q` but clearer in verification contexts.

```python
assert implies(val < lo, result == lo)
assert implies(val > hi, result == hi)
```

### 3.4 Collections

| Expression | Meaning |
|---|---|
| `len(lst)` | length of a list, string, dict, or set |
| `lst[i]` | element at index `i` |
| `lst[i:j]` | slice (length only, not element equality) |
| `k in d` | key membership in dict |
| `k not in d` | key non-membership in dict |
| `x in s` | element membership in set |

### 3.5 Quantifiers

Universal and existential quantifiers over lists:

```python
assert all(result[j] == j for j in range(n))
assert all(x > 0 for x in result)
assert any(x > threshold for x in items)
```

Range-based forms:

```python
assert all(result[j] <= result[j+1] for j in range(len(result)-1))
```

### 3.6 Strings

| Expression | Meaning |
|---|---|
| `len(s)` | length |
| `s == "literal"` | equality to string literal |
| `s != "literal"` | inequality |
| `"substr" in s` | substring containment |
| `s.startswith("p")` | prefix check |
| `s.endswith("p")` | suffix check |
| `s.re_match("pattern")` | regex membership (see Section 4) |

### 3.7 Type predicates

| Expression | Meaning |
|---|---|
| `isinstance(x, T)` | runtime type check |
| `is_shape(x)` or `is_shape(x, T)` | structural shape check for Pydantic/dataclass |
| `is_valid(x)` or `is_valid(x, T)` | validation constraints satisfied |

`is_shape(x)` is auto-injected for class-typed parameters.
`is_valid(x)` is auto-injected for `validate_assignment=True` models.

### 3.8 Ghost state

| Expression | Meaning |
|---|---|
| `old(x)` | value of `x` in the pre-state |
| `old(x.field)` | pre-state field value |
| `result` | return value (postconditions only) |
| `result.field` | field of a structured return value |

### 3.9 Enum and class values

Enum members are resolved to their integer encodings at verification time:

```python
assert implies(self.level == ProofLevel.UNPROVED, result == False)
```

`ProofLevel.UNPROVED` is looked up in the AST and encoded as its integer
value. No import needed in the contract expression.

Class field access `obj.field` is normalised to the flat Coq parameter
`obj_field` using the `_escape_field` convention (literal underscores in
field names are doubled).

### 3.10 Floats

Floats are stored internally as `VFloat(z: Z)` scaled by `float_scale`
(100 by default — two decimal places).  Float literals in contracts
(`1.5`, `0.01`) are automatically scaled.

```python
assert implies(a > 0.0, result > 0.0)
```

### 3.11 Special values

| Expression | Coq encoding |
|---|---|
| `None` | `VNone` |
| `True` | `VZ 1` in comparison context; `True` as Prop |
| `False` | `VZ 0` in comparison context; `False` as Prop |
| `result is None` | `BIsNone "result"` |
| `result is not None` | `BNot (BIsNone "result")` |

---

## 4. Regex Contracts — `s.re_match(pattern)`

The method `s.re_match(pattern)` is a **verifier-only** predicate — it
does not execute at runtime and is not a real Python string method.  It
asserts that `s` matches the Python regex `pattern`.

```python
def accept_phone(phone: str) -> str:
    """
    axiomander:
        units:
            phone: [E164]       # optional: also dimensionally annotate
        requires:
            phone.re_match("[0-9]{3}-[0-9]{3}-[0-9]{4}")
        ensures:
            result.re_match("[0-9-]+")
    """
    result = phone
    return result
```

### How it is verified

The pattern is translated to a SMTLIB2 `RegLan` expression using Python's
`sre_parse` module — no hand-written regex parser.  The theory-SMT oracle
(Level 2b) verifies the constraint via Z3/CVC5 `str.in_re`.

Supported pattern constructs:

| Pattern | SMTLIB2 | Example |
|---|---|---|
| `[a-z]` | `re.range "a" "z"` | lowercase letter |
| `[^0-9]` | `re.comp (re.range "0" "9")` | non-digit |
| `.` | `re.allchar` | any single char |
| `p*` | `re.* p` | zero or more |
| `p+` | `re.+ p` | one or more |
| `p?` | `re.opt p` | zero or one |
| `p{n}` | `(_ re.^ n) p` | exactly n |
| `p{n,m}` | `(_ re.loop n m) p` | n to m |
| `p\|q` | `re.union p q` | alternation |
| `pq` | `re.++ p q` | concatenation |
| `\d` | `re.range "0" "9"` | digit |
| `\w` | word chars | letter, digit, `_` |
| `\s` | whitespace | space, tab, newline |
| `(group)` | transparent | grouping only |
| `^`, `$` | epsilon | anchors implicit in `str.in_re` |

Unsupported: backreferences (`\1`), lookahead/lookbehind.  These return
`None` from the translator and fall through to the LLM oracle.

### Subsumption and contradiction

When a **precondition** restricts the input to a strong pattern and the
**postcondition** claims a weaker pattern, the theory oracle verifies the
**subsumption** automatically:

```python
# Precondition: full phone [0-9]{3}-[0-9]{3}-[0-9]{4}
# Postcondition: digits and dashes [0-9-]+
# Every full phone number is also in [0-9-]+ → proved
```

When the postcondition is **disjoint** from the precondition's language,
the oracle returns a **concrete counterexample**:

```python
# Precondition: phone numbers (digits and dashes)
# Postcondition: letters only [A-Za-z]+
# Counterexample: phone = "000-000-0000" — valid phone, no letters
```

---

## 5. Dimensional Analysis — `units:`

The `units:` section declares the **physical or semantic dimension** of each
parameter and the return value.  Axiomander checks that all arithmetic
in the function body is dimensionally consistent before attempting the
Coq proof.

### 5.1 Base dimensions

Base dimensions are **arbitrary named strings**.  There is no hardcoded list.
You declare whatever dimensions your domain needs:

```
# Financial
USD  GBP  EUR  JPY          -- currency (incompatible siblings)

# Counts / cardinality
person  item  transaction   -- first-class dimensions

# Time (financial often uses calendar units)
day  month  year

# Physical (standard SI base dimensions)
m  kg  s  A  K  mol  cd
```

Different named dimensions are **never automatically compatible**.  `[USD]`
and `[GBP]` are distinct; `[USD] + [GBP]` is a dimension error.

### 5.2 Dimension expressions

The dimension expression grammar:

```
dim_expr  ::= base_dim
            | dim_expr * dim_expr   -- multiply (add exponents)
            | dim_expr / dim_expr   -- divide (subtract exponents)
            | dim_expr ^ integer    -- power (scale exponents)
            | 1                     -- dimensionless
            | ( dim_expr )
base_dim  ::= identifier
```

Examples:

| Expression | Meaning | Vector |
|---|---|---|
| `USD` | US dollars | `{USD: 1}` |
| `USD/person` | per-capita | `{USD: 1, person: -1}` |
| `GBP/USD` | exchange rate | `{GBP: 1, USD: -1}` |
| `USD/person/year` | annual per-capita | `{USD: 1, person: -1, year: -1}` |
| `USD/share` | price per share | `{USD: 1, share: -1}` |
| `kg*m^2/s^2` | Joules | `{kg: 1, m: 2, s: -2}` |
| `1` | dimensionless | `{}` |

### 5.3 Composition rules

| Operation | Dimension rule |
|---|---|
| `a * b` | `dim(a) + dim(b)` (vector add) |
| `a / b` | `dim(a) - dim(b)` (vector subtract) |
| `a + b` | requires `dim(a) == dim(b)` |
| `a - b` | requires `dim(a) == dim(b)` |
| `a ** n` | `n * dim(a)` (integer n only) |
| `abs(a)`, `round(a)`, `int(a)`, `float(a)` | preserves `dim(a)` |
| `len(x)` | always dimensionless `{}` |
| numeric literal | dimensionless `{}` |

### 5.4 Examples

**Per-capita income:**

```python
def gdp_per_capita(gdp: float, population: int) -> float:
    """
    axiomander:
        units:
            gdp:        [USD]
            population: [person]
            result:     [USD/person]
        requires:
            population > 0
        ensures:
            result >= 0
    """
    result = gdp / population
    return result
```

**Currency conversion (exchange rate has dimension):**

```python
def convert_to_usd(amount: float, rate: float) -> float:
    """
    axiomander:
        units:
            amount: [GBP]
            rate:   [USD/GBP]    # exchange rate is not dimensionless
            result: [USD]
        ensures:
            result == amount * rate
    """
    result = amount * rate
    return result
```

**Portfolio value (shares × price/share = currency):**

```python
def portfolio_value(shares: int, price: float) -> float:
    """
    axiomander:
        units:
            shares: [share]
            price:  [USD/share]
            result: [USD]
        requires:
            shares >= 0
            price >= 0
        ensures:
            result >= 0
    """
    result = shares * price
    return result
```

**Explicit currency conversion:**

```
axiomander:
    units:
        amount_gbp: [GBP]
        result:     [USD]
    convert GBP to USD: rate
```

The `convert X to Y: param` line declares that parameter `rate` has
dimension `[USD/GBP]` and is used for explicit conversion.

### 5.5 What the dimension check catches

- `revenue + headcount` where `revenue: [USD]` and `headcount: [person]`
  — adding incompatible dimensions
- `result = revenue + exchange_rate` — assigning wrong dimension
- `return revenue` where `result: [USD/person]` is declared — wrong
  return dimension
- `total += revenue_gbp` where `total` was initialised from `[USD]`
  — augmented assignment mixes currencies

### 5.6 What it does not catch

- Errors that require **value-level reasoning** (`revenue >= 0` is a WP
  postcondition, not a dimension property)
- **Fractional exponents** (`sqrt(variance)` — not supported, use `dim ** 2`
  and take the square root as a function with a declared signature)
- **Parametric dimensions** — when the dimension of a variable is
  unknown and must be inferred from constraints (e.g. elements of an
  untyped list)

### 5.7 When dimension errors are reported

The dimension check runs **before** the Coq WP proof.  A dimension
violation immediately returns `COUNTEREXAMPLE` and the function is not
sent to the proof pipeline.  This is intentional: there is no point
attempting to prove a function whose arithmetic is structurally wrong.

---

## 6. Pydantic and Dataclass Contracts

For Pydantic `BaseModel` and `@dataclass` class parameters, Axiomander
expands the fields into flat Coq parameters using the Shape IR.

```python
from pydantic import BaseModel, Field

class Account(BaseModel):
    balance: int = Field(ge=0)
    owner: str

def withdraw(account: Account, amount: int) -> int:
    """
    axiomander:
        requires:
            is_shape(account)
            account.balance >= amount
            amount >= 0
        ensures:
            result == account.balance - amount
    """
    result = account.balance - amount
    return result
```

`is_shape(account)` asserts that `account` has the declared field
structure.  `account.balance` is normalised to the flat key
`account_balance` in the Coq state.

For `validate_assignment=True` models, `is_valid(account)` is
auto-injected into the postcondition to assert that all field constraints
(`Field(ge=0)`) hold after any mutation.

---

## 7. Loop Predicates

A predicate function can be used in a contract to gate a postcondition:

```python
def is_positive(x: int) -> bool:
    return x > 0

def use_pred(n: int):
    assert is_positive(n)       # precondition via predicate
    result = 0
    return result
```

For predicates with loops, the verifier inlines the predicate's
postcondition at the call site.  The predicate must carry its own
`ensures:` contract using `implies(result == 1, ...)`:

```python
def geq_loop(x: int, n: int) -> bool:
    assert n >= 0
    r = x
    while r < n:
        r = r + 1
    result = (r >= n)
    assert implies(result == 1, x >= n)
    return result
```

---

## 8. Exception Contracts — Outcome Predicates

Axiomander models exceptions as **outcomes** in the WP calculus.  A
function produces either `OReturn(result)` or `ORaise(exception_value)`.

The full outcome predicate shape:

```coq
fun o =>
  match o with
  | OReturn s  => (* ensures conditions *)
  | ORaise (VString "ValueError") s => (* raises: ValueError condition *)
  | ORaise (VString "KeyError")   s => (* raises: KeyError condition *)
  | _ => True
  end
```

Multiple exception types with different conditions:

```python
def parse_int(s: str) -> int:
    """
    axiomander:
        requires:
            len(s) > 0
        ensures:
            result >= 0
        raises:
            ValueError: not s.re_match("[0-9]+")
            OverflowError: len(s) > 18
    """
    if not s.isdigit():
        raise ValueError
    n = int(s)
    if n > 10**18:
        raise OverflowError
    result = n
    return result
```

---

## 9. Summary: Complete Section Reference

```
axiomander:
    where:
        name: type = expr    # ghost pre-state binding (one per line)

    requires:
        expr                 # precondition (one per line, conjoined)

    reads:
        var1                 # variables read (one per line)
        var2

    modifies:
        none                 # or: var1, var2, ... (one per line)

    ensures:
        expr                 # postcondition (one per line, conjoined)

    raises:
        ExcType: condition   # exception postcondition (one per line)

    units:
        param:  [dim_expr]   # dimension declaration (one per line)
        result: [dim_expr]
        convert X to Y: p   # explicit conversion via parameter p
```

**Operator availability by section:**

| Operator | `requires:` | `ensures:` | loop `assert` |
|---|---|---|---|
| Arithmetic `+ - * / // %` | ✓ | ✓ | ✓ |
| Comparison `== != < <= > >=` | ✓ | ✓ | ✓ |
| Logic `and or not implies()` | ✓ | ✓ | ✓ |
| `len()` | ✓ | ✓ | ✓ |
| `all() any()` | ✓ | ✓ | ✓ |
| `in` / `not in` | ✓ | ✓ | ✓ |
| `old(x)` | — | ✓ | — |
| `result` | — | ✓ | — |
| `result.field` | — | ✓ | — |
| `is_shape()` | ✓ | ✓ | — |
| `s.re_match()` | ✓ | ✓ | ✓ |
| Enum members | ✓ | ✓ | ✓ |
| `None` / `True` / `False` | ✓ | ✓ | ✓ |
