# Examples

## Gold Standard Vision

Axiomander aims to let developers write business logic as plain Python `assert`
statements, with the verifier handling all algorithmic proof engineering
automatically. The target experience, inspired by [Cedar](https://github.com/cedar-policy), [Dafny](https://dafny.org), and the [Viper](https://www.pm.inf.ethz.ch/research/viper.html) ecosystem (Gobra for Go, Nagini for Python, Prusti for Rust):

> **The user writes *what* must hold. The verifier figures out *why* it holds.**
> Loop indices, array bounds, heap framing, and induction are the verifier's
> problem — never the user's.

---

## Progression

```
V1 (today)          V2 (near-term)         V3 (gold standard)
│                   │                       │
│ assert i <= n     │ assert all(prices)     │ assert balance >= 0
│ assert len==i     │   are positive         │ ensures no overdraft
│ manual invariant  │ inferred invariant     │ verifier infers frame,
│ manual bound      │ auto-bounds            │   invariant, termination
```

### V1: Working Today

Predicates, quantifiers, implication, loop predicates via postcondition
inlining. Simple invariants are wired into the WP. The verifier proves
arithmetic properties automatically; quantifiers go to SMT.

### V2: Near-Term

- **Body-preservation VCs** — invariant preservation checked automatically
  for every loop body. No more undetected invariant violations.
- **Auto-bounds** — list lengths, string lengths, and array indices get
  non-negativity preconditions inferred from type annotations.
- **Library stubs** — `sum()`, `max()`, `min()`, `len()` carry proper
  contracts so they can be used directly in assertions.

### V3: Gold Standard

- **Ghost state** — Dafny-style ghost variables separate the business model
  (a `balance: int` that always respects invariants) from the implementation
  (database queries, HTTP calls, caching).
- **Invariant inference** — given a postcondition like
  `all(result[j] == j*j for j in range(n))` and a body that does
  `result[i] = i*i; i++`, the verifier infers
  `all(result[j] == j*j for j in range(i))` as the loop invariant.
- **Separation logic** — Viper-style permission tracking for concurrent
  and mutable-state programs.
- **Lemmas** — reusable proof blocks that can be invoked across call sites.
- **Full frame automation** — `reads`/`writes` inferred from the callee's
  contracts, proven automatically at every call site.

---

## Business Logic Examples

Each example shows a contract (the *what*, dropped by `python -O`) and a
body (the *how*, runs in production). Contracts use only `assert` statements —
zero imports, zero decorators.

### Authorization (modeled on AWS Cedar)

Cedar proves *explicit permit* (only `permit` policies grant access) and
*forbid overrides permit*. This example captures the same semantics: a
request is allowed iff a matching permit exists and no forbid blocks it.

```python
def is_authorized(principal: str, action: str, resource: str,
                  permits: dict[str, list[str]], forbids: dict[str, list[str]]) -> int:
    """Returns 1 if authorized, 0 if denied.

    Cedar semantics: forbid overrides permit; explicit permit required.
    """
    assert len(permits) >= 0
    assert len(forbids) >= 0
    for resource_pattern, actions in forbids.items():
        if resource_pattern == resource or resource_pattern == "*":
            if action in actions or "*" in actions:
                result = 0
                assert result == 0
                return result
    for resource_pattern, actions in permits.items():
        if resource_pattern == resource or resource_pattern == "*":
            if action in actions or "*" in actions:
                result = 1
                assert result == 1
                return result
    result = 0
    assert result == 0
    return result
```

**V1 status:** loop body is verified. **V3 target:** auto-frame on dict
parameters; `action in actions` desugars to a quantifier with inferred bounds.

---

### Banking: Transfer

Conservation of money — the classic business invariant. Money is neither
created nor destroyed.

```python
def transfer(sender: str, receiver: str, amount: int,
             balances: dict[str, int]) -> int:
    """Transfer amount from sender to receiver. Returns 1 on success."""
    assert amount >= 0
    assert len(balances) >= 0
    if __debug__:
        old_sender = balances.get(sender, 0)
        old_receiver = balances.get(receiver, 0)
    if sender not in balances or balances[sender] < amount:
        result = 0
        assert result == 0
        return result
    if sender == receiver:
        result = 1
        assert result == 1
        return result
    balances[sender] = old_sender - amount
    balances[receiver] = old_receiver + amount
    result = 1
    assert balances[sender] >= 0                              # no overdraft
    assert balances[sender] + balances[receiver] ==           # conservation
           old_sender + old_receiver
    assert result == 1
    return result
```

**Key contract patterns:**
- **No negative balances** — `balances[sender] >= 0` (business rule)
- **Conservation** — `new_sender + new_receiver == old_sender + old_receiver`
- **Ghost snapshot** — `old_sender`, `old_receiver` capture pre-state
- **Branch-precise** — each return path asserts its result

**V3 target:** the `dict` reads (`balances.get`, `balances[sender]`) would
carry auto-derived frame conditions (`reads balances`). The verifier would
infer that `receiver` is untouched in the failure branch.

---

### E-commerce: Checkout

A running-total pattern — the loop maintains a partial-sum invariant, and
the postcondition ties the result to the final comparison.

```python
def is_affordable(cart: dict[str, int], prices: dict[str, int],
                  balance: int) -> bool:
    """Pure predicate: cart total is within balance."""
    return sum(prices.get(item, 0) * qty for item, qty in cart.items()) <= balance

def checkout(cart: dict[str, int], prices: dict[str, int],
             balance: int) -> int:
    """Returns 1 if the cart is affordable, 0 otherwise."""
    assert balance >= 0
    assert len(cart) >= 0
    total = 0
    for item, qty in cart.items():
        assert 0 <= total <= balance * 2                       # invariant: bounded total
        if item in prices:
            total += prices[item] * qty
    result = (total <= balance)
    assert implies(result == 1, total <= balance)              # semantic postcondition
    return result
```

**V2/V3 target:** the pure predicate `is_affordable` should be usable
directly as a postcondition — `assert is_affordable(cart, prices, balance)`
— inlined via the predicate expansion mechanism. The `sum()` generator
expression needs SMT-level quantifier support.

---

### Form Validation (web backend)

Business predicates compose to express complex validation rules.

```python
def is_valid_email(email: str) -> bool:
    """Loop predicate: email contains @ with non-empty local and domain parts."""
    at_pos = -1
    i = 0
    while i < len(email):
        if email[i] == 64:                                    # ord('@')
            at_pos = i
            break
        i += 1
    result = (at_pos > 0 and at_pos < len(email) - 1)
    assert implies(result == 1,
                   at_pos > 0 and at_pos < len(email) - 1)    # semantic postcondition
    return result

def validate_form(email: str, password: str, age: int) -> int:
    """Returns 1 if all fields are valid."""
    assert len(email) >= 0
    assert len(password) >= 0
    assert age >= 0
    if not is_valid_email(email):
        result = 0
        assert result == 0
        return result
    if len(password) < 8:
        result = 0
        assert result == 0
        return result
    if age < 18:
        result = 0
        assert result == 0
        return result
    result = 1
    assert implies(result == 1,                                # compositional postcondition
        is_valid_email(email) and len(password) >= 8 and age >= 18)
    return result
```

**Key pattern:** the loop predicate `is_valid_email` carries a semantic
postcondition (`implies(result == 1, property)`). At the call site in
`validate_form`, the linter expands it to the property with `result → 1`
substitution. The contract stays at the business-logic level.

---

### Rate Limiter

A sliding-window pattern: count requests in the trailing window, reject
if over the limit.

```python
def check_rate_limit(key: str, timestamps: list[int],
                     window: int, max_requests: int) -> int:
    """Returns 1 if within limit, 0 if exceeded."""
    assert window > 0
    assert max_requests > 0
    assert len(timestamps) >= 0
    now = timestamps[-1] if len(timestamps) > 0 else 0
    cutoff = now - window
    count = 0
    i = len(timestamps) - 1
    while i >= 0 and timestamps[i] > cutoff:
        assert 0 <= count <= max_requests                     # bounded invariant
        count += 1
        i -= 1
    result = (count < max_requests)
    assert implies(result == 1, count < max_requests)
    return result
```

**V3 target:** with invariant inference, the user writes only the
postcondition `assert result == 1 iff recent requests < max_requests`.
The verifier infers `0 <= count <= max_requests` and the loop bound.

---

### Pagination (Viper-style collection reasoning)

Viper's collection types (`seq`, `set`, `map`) are mathematical — they
describe *what* a collection contains, not *how* it's stored. The
postcondition expresses slice semantics; the body does the copying.

```python
def paginate(items: list[str], page: int, per_page: int) -> list[str]:
    """Return the requested page of items."""
    assert page >= 0
    assert per_page > 0
    assert len(items) >= 0
    start = page * per_page
    if start >= len(items):
        result = []
        assert len(result) == 0
        return result
    end = start + per_page
    i = start
    result = []
    while i < len(items) and i < end:
        assert len(result) == i - start                       # progress invariant
        result.append(items[i])
        i += 1
    assert len(result) <= per_page                            # size bound
    assert len(result) == min(per_page, len(items) - start)    # exact slice length
    assert all(result[j] == items[start + j]                   # content equality
               for j in range(len(result)))
    return result
```

**V3 target:** the `all(...)` content-equality postcondition is a structural
property — every element of the result matches the corresponding element of
the input slice. This is exactly what Viper's `seq` equality expresses:
`result == items[start..end]`.

---

### Database Write with Invariant

A ghost-state pattern: the business invariant ("total supply is constant")
holds regardless of how the database is sharded.

```python
class TokenLedger:
    """Business model: total supply of tokens is fixed at creation."""
    total_supply: int
    balances: dict[str, int]

def mint(ledger: TokenLedger, recipient: str, amount: int) -> int:
    """Mint tokens from the reserve to a recipient. Returns 1 on success."""
    assert amount >= 0
    assert ledger.total_supply >= 0
    reserve_balance = ledger.balances.get("_reserve", 0)
    if amount > reserve_balance:
        result = 0
        assert result == 0
        return result
    if __debug__:
        total_before = sum(ledger.balances.values())
    ledger.balances["_reserve"] = reserve_balance - amount
    if recipient not in ledger.balances:
        ledger.balances[recipient] = 0
    ledger.balances[recipient] += amount
    result = 1
    assert sum(ledger.balances.values()) == total_before       # supply invariant
    assert result == 1
    return result
```

**Key pattern:** `total_before` ghosts the aggregate before mutation. The
postcondition proves the supply invariant — no tokens created or destroyed.
This is the business-level guarantee: *total supply is constant*.

---

## Pattern Reference

Each example demonstrates reusable verification patterns. The column shows
the pattern's current verification tier.

| Pattern | Syntax | Example | Tier |
|---|---|---|---|
| **Pure predicate** | single `return` expression | `is_affordable` | V1 ✓ |
| **Loop predicate** | body with loop, `implies` postcondition | `is_valid_email` | V1 ✓ |
| **Conservation** | `old_sum == new_sum` | `transfer`, `mint` | V1 ✓ |
| **Ghost snapshot** | `old_x = x` before mutation | `transfer` | V1 ✓ |
| **Branch-precise** | `implies(guard, consequence)` | `validate_form` | V1 ✓ |
| **Bounded invariant** | `0 <= count <= max` in loop | `checkout`, `rate_limit` | V1 ✓ |
| **Quantified property** | `all(...)` in contract | `paginate` | V1* |
| **Progress invariant** | `len(result) == i - start` | `paginate` | V1 ✓ |
| **Inferred invariant** | verifier derives from postcondition | — | V3 |
| **Ghost state** | Dafny-style model fields | `TokenLedger` | V3 |
| **Auto-frame** | `reads`/`writes` from type annotations | — | V3 |
| **Separation logic** | permission-based disjointness | — | V3 |

\* Quantified properties verify at the VCG (SMT) level; WP body proofs filter
quantifier invariants to VCG-only.

---

## Design Principles

1. **Contracts are business logic.** `assert balance >= 0` is a domain
   invariant. `assert i <= n` is algorithmic noise. The verifier should
   handle the latter so the user writes only the former.

2. **Predicates are reusable specifications.** Dafny's `predicate` and
   Viper's `function` let you name a property once and use it everywhere.
   Our `_expand_predicate` mechanism does this: define `is_sorted(lst)`
   once, use `assert is_sorted(result)` in every function that produces
   a sorted list.

3. **Ghost state separates model from implementation.** The `TokenLedger`
   class is the business model. Database sharding, caching, and connection
   pooling are implementation details. Contracts reason about the model.

4. **Zero runtime overhead.** Python's `-O` flag strips all `assert`
   statements. Verification has no production cost. This is the same
   guarantee Dafny, Viper, and F\* provide: specifications are erased
   at compile time.

5. **The verifier does the work.** Cedar's Dafny model is verified once;
   the production Rust is differential-tested against it. Viper's
   verifiers handle separation logic so frontend languages don't have to.
   Our goal: the user writes `assert`; the pipeline handles Coq, SMT,
   and invariant inference automatically.

---

## Ghost State Without Keywords

Dafny requires `ghost var`, F\* requires `Ghost` effect annotations, Viper
requires special declaration syntax. Axiomander needs none of them. The
inference rule:

> **A local variable is ghost iff every read of that variable occurs inside
> an `assert` statement. Ghost variables are excluded from the IMP body,
> carry no frame conditions, and exist only for verification.**

The detection is a single AST pass:

```
For each local variable v in the function:
  Find all reads of v (Name nodes where id == v).
  If every read is inside an ast.Assert node → ghost.
  If any read is outside an assert → concrete (in IMP body).

Ghost variables assigned inside if __debug__: blocks are excluded from
the IMP body. Python's -O flag strips both the block and all asserts,
so the snapshot carries zero runtime cost.
```

**The verifier generates:**

```
Theorem mint_correct : forall ..., exists (old_total : Z),
  old_total = sum(balances) /\ ... -> wp body (sum(balances) == old_total) ...
```

**Example — `old_total` is detected as ghost:**

```python
def mint(ledger: TokenLedger, recipient: str, amount: int) -> int:
    assert amount >= 0
    if __debug__:
        old_total = sum(ledger.balances.values())   # ghost: stripped by python -O
    # ... mutations to ledger.balances ...
    result = 1
    assert sum(ledger.balances.values()) == old_total  # ONLY read of old_total → ghost
    return result
```

`if __debug__:` is built into Python — zero imports, zero keywords. Under
`python -O`, the bytecode compiler removes the entire block. The snapshot
never executes in production. The verifier sees it as a logical `let`
binding and never touches the Coq heap.

**What this enables:**

- All existing `old_x = x` snapshot patterns become ghost automatically — no
  code changes needed.
- The Coq theorem gets the snapshot as a logical variable, not a heap cell.
  No `clobber`, no `upd`, no frame condition overhead.
- `python -O` already strips the assert; the variable `old_sum` becomes dead
  code and the Python optimizer removes it.

**Limitation (current):** only local variables can be detected this way.
Class fields and dict entries used as ghost snapshots need the user to
manually structure the code so the snapshot is captured in a local before
the mutation — which is already the natural pattern.
