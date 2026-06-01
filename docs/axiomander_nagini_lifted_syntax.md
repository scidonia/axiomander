# Axiomander Contract Syntax: Nagini-Lifted, Library-Free Specification

## Purpose

This document specifies a proposed Axiomander contract syntax inspired by Nagini, Viper, JML, Dafny, and separation logic. The goal is to preserve the successful ideas from Nagini's specification vocabulary while avoiding a mandatory runtime Python contract library.

Axiomander should accept ordinary Python code and parse verifier-only specifications from docstrings, structured comments, or optional decorators. The Python runtime should not need to import `nagini_contracts` or any equivalent package.

The central design principle is:

> Axiomander contracts describe all exits of a function: normal return, exceptional return, resource transfer, and heap ownership preservation.

---

## 1. Design Goals

Axiomander's surface syntax should support:

1. Preconditions and postconditions.
2. Exceptional postconditions.
3. Separation-logic style ownership and permissions.
4. Object, list, dictionary, set, and Pydantic model shapes.
5. Database and external-resource regions.
6. Loop invariants and variants.
7. Function purity and ghost/specification-only helpers.
8. Explicit frame/modifies information.
9. Concurrency primitives such as locks and tokens.
10. A path toward Coq/SMT/Viper/Iris-style backends.

It should not require:

1. A mandatory runtime library.
2. Rewriting ordinary Python into a custom DSL.
3. Users to understand Coq, Viper, or Iris.

---

## 2. Relation to Nagini

Nagini specifications are written as Python function calls, typically using names such as:

```python
Requires(...)
Ensures(...)
Invariant(...)
Acc(...)
Result()
Old(...)
Assert(...)
Implies(...)
```

Axiomander should lift this vocabulary, but expose it in verifier-only contract blocks:

```python
def f(x: int) -> int:
    """
    axiomander:
        requires:
            x > 0

        ensures:
            result > x

        raises:
            none
    """
    return x + 1
```

The names `requires`, `ensures`, `raises`, `acc`, `old`, `result`, and `invariant` should be treated as logical syntax, not runtime functions.

---

## 3. Accepted Contract Carriers

Axiomander should support three carriers, in priority order.

### 3.1 Function docstring contracts

Preferred for zero-library use.

```python
def withdraw(account: Account, amount: int) -> None:
    """
    axiomander:
        requires:
            owns(account)
            * field(account, "balance", b)
            * amount > 0
            * b >= amount

        modifies:
            account

        ensures:
            owns(account)
            * field(account, "balance", b - amount)

        raises InsufficientFunds as e:
            owns(account)
            * field(account, "balance", b)
            * amount > b

        raises:
            no_runtime_errors
    """
    ...
```

### 3.2 Structured comments

Useful when docstrings are already used for documentation.

```python
#@ requires: x > 0
#@ ensures: result == x + 1
#@ raises: none
def inc(x: int) -> int:
    return x + 1
```

### 3.3 Optional decorator layer

Useful later for IDE support, but not required.

```python
@axiomander(
    requires="x > 0",
    ensures="result == x + 1",
    raises="none",
)
def inc(x: int) -> int:
    return x + 1
```

The docstring/comment syntax is the canonical form. Decorators should desugar to the same internal contract representation.

---

## 4. Core Function Contract Grammar

The minimum function-level grammar is:

```text
axiomander:
    requires:
        P

    reads:
        R1, R2, ...

    modifies:
        M1, M2, ...

    ensures:
        Q

    raises ExceptionType as e:
        E

    raises:
        none | no_runtime_errors | any | declared
```

Where:

- `requires` describes the initial state.
- `reads` lists resources or heap regions that may be inspected but not mutated.
- `modifies` lists resources or heap regions that may be mutated.
- `ensures` describes the normal-return state.
- `raises E as e` describes an exceptional exit with exception object `e`.
- `raises: none` forbids all exceptions.
- `raises: no_runtime_errors` forbids undeclared runtime crashes but permits declared domain exceptions.
- `raises: declared` means only explicitly declared exceptions are allowed.
- `raises: any` means the verifier should not attempt to prove exception freedom.

Recommended default:

```text
raises: no_runtime_errors
```

This matches the practical verification goal: ordinary runtime crashes should be bugs unless deliberately modelled.

---

## 5. Normal Return Syntax

Use `result` for the returned value.

```python
def abs_val(x: int) -> int:
    """
    axiomander:
        ensures:
            result >= 0
            * (result == x or result == -x)
        raises:
            none
    """
    return x if x >= 0 else -x
```

For functions returning `None`, `result` is either unavailable or equal to `None`. Prefer not using it.

---

## 6. Old-State Syntax

Use `old(expr)` to refer to the pre-state value of an expression.

```python
def push(xs: list[int], x: int) -> None:
    """
    axiomander:
        requires:
            owns(xs) * list_model(xs, Xs)

        modifies:
            xs

        ensures:
            owns(xs) * list_model(xs, old(Xs) + [x])

        raises:
            none
    """
    xs.append(x)
```

For ghost variables bound in the precondition, `old(Xs)` and `Xs` may be equivalent if `Xs` is immutable/logical. Axiomander should still accept `old(...)` because users expect it from JML/Dafny/Nagini-style specifications.

---

## 7. Logical Connectives

Axiomander should support a small expression language based on Python syntax plus separation-logic connectives.

### 7.1 Boolean connectives

```text
and
or
not
implies(P, Q)
iff(P, Q)
```

Optional ASCII aliases:

```text
P ==> Q
P <==> Q
```

### 7.2 Separation connectives

```text
P * Q
emp
```

Meaning:

- `emp` means the empty owned heap/resource fragment.
- `P * Q` means separating conjunction: the owned resource can be split into disjoint parts satisfying `P` and `Q`.

### 7.3 Quantifiers

Use Python-like binder syntax inside contract blocks:

```text
forall x: T :: P
exists x: T :: P
```

Examples:

```text
forall i: int :: 0 <= i < len(xs) implies xs[i] >= 0
exists row: Row :: row.id == user_id
```

---

## 8. Permission and Ownership Predicates

Nagini's key heap predicate is `Acc(...)`, derived from Viper-style permissions. Axiomander should support both Nagini-like and Python-friendly spellings.

### 8.1 Field permission

Canonical Axiomander form:

```text
field(obj, "name", value)
```

Meaning:

> The verifier owns permission to read/write `obj.name`, and its logical value is `value`.

Example:

```text
field(account, "balance", b)
```

Nagini-compatible alias:

```text
acc(account.balance)
```

Axiomander should internally desugar:

```text
acc(account.balance)
```

into a field permission predicate with an existential value unless a value is explicitly bound.

### 8.2 Fractional permission

```text
acc(account.balance, 1)
acc(account.balance, 1/2)
acc(account.balance, read)
acc(account.balance, write)
```

Suggested meanings:

- `1` or `write`: full permission, read/write allowed.
- `1/2` or `read`: fractional permission, read-only unless fractions are recombined.

For early Axiomander, full ownership is enough. Fractional permissions can be parsed but initially rejected with a clear unsupported-feature error.

### 8.3 Object ownership

```text
owns(obj)
```

Meaning:

> The current function owns the abstract mutable footprint of `obj`.

This is coarser than field-level permissions and useful for early implementation.

Recommended early desugaring:

```text
owns(obj)
```

means permission to the object's known mutable fields according to its type/shape model.

---

## 9. Built-in Shape Predicates

Axiomander should provide verifier-only predicates for common Python structures.

### 9.1 Lists

```text
list_model(xs, Xs)
```

Meaning:

> Python list object `xs` is represented by immutable logical sequence `Xs`.

Examples:

```text
list_model(xs, Xs) * len(Xs) > 0
list_model(xs, Xs + [x])
```

Nagini-compatible alias:

```text
list_pred(xs)
```

Recommended Axiomander approach:

```text
list_pred(xs)
```

denotes permission to the list contents, while:

```text
list_model(xs, Xs)
```

denotes permission plus abstract contents.

### 9.2 Dictionaries

```text
dict_model(d, D)
```

Meaning:

> Python dict `d` is represented by immutable logical map `D`.

Examples:

```text
dict_model(d, D) * key in D
dict_model(d, D[key := value])
```

Nagini-compatible alias:

```text
dict_pred(d)
```

### 9.3 Sets

```text
set_model(s, S)
```

Nagini-compatible alias:

```text
set_pred(s)
```

### 9.4 Tuples

Tuples may usually be treated as pure values:

```text
tuple_model(t, T)
```

This is optional unless mutable references are nested inside.

---

## 10. Pydantic and Object Shape Predicates

Because Axiomander wants to piggyback on Pydantic, add a predicate family for validated object shapes.

```text
pydantic_model(obj, ModelType, data)
```

Meaning:

> `obj` is an instance of `ModelType`, and its logical validated data is `data`.

Example:

```python
def save_user(db: DB, user: User) -> None:
    """
    axiomander:
        requires:
            pydantic_model(user, User, U)
            * U["id"] is not None
            * db_region(db, D)

        modifies:
            db

        ensures:
            db_region(db, D.users[U["id"] := U])

        raises ValidationError as e:
            db_region(db, D)
    """
    ...
```

For Pydantic models that are configured as frozen/immutable, `pydantic_model` may be pure rather than ownership-bearing. For mutable models, it should imply ownership or field permissions.

---

## 11. Exception Specification

Axiomander must model exceptional exits explicitly.

### 11.1 No exceptions

```text
raises:
    none
```

Meaning:

> The function cannot raise any exception.

### 11.2 No runtime errors

```text
raises:
    no_runtime_errors
```

Meaning:

> Runtime bugs such as `TypeError`, `AttributeError`, `IndexError`, `KeyError`, `ZeroDivisionError`, and uncaught assertion failures are forbidden unless explicitly declared.

### 11.3 Declared exceptions only

```text
raises:
    declared
```

Meaning:

> The function may raise only the exceptions named in `raises ExceptionType` blocks.

### 11.4 Explicit exceptional postconditions

```python
def get(d: dict[str, int], k: str) -> int:
    """
    axiomander:
        requires:
            dict_model(d, D)

        ensures:
            result == D[k]
            * dict_model(d, D)

        raises KeyError as e:
            k not in D
            * dict_model(d, D)

        raises:
            declared
    """
    return d[k]
```

### 11.5 Exception hierarchy matching

Axiomander should use Python exception subclassing:

```text
raises LookupError:
    ...
```

covers `KeyError` and `IndexError` unless a more specific block exists.

Specific handlers override general ones.

---

## 12. Assertion Syntax

Nagini uses `Assert(P)`. Axiomander should support ordinary Python `assert` as the primary source form.

```python
assert x > 0
```

Verifier meaning:

```text
prove x > 0 at this program point
```

Runtime meaning remains Python's normal assertion behavior.

Axiomander should also support ghost-only assertions inside comments:

```python
#@ assert: list_model(xs, Xs) * len(Xs) > 0
```

Use this when the assertion is not executable Python.

---

## 13. Assumption Syntax

Nagini has specification functions that can act like assumptions in limited contexts. Axiomander should make assumptions explicit and dangerous.

```python
#@ assume: P
```

Meaning:

> Add `P` to the current proof context without proof.

Axiomander should mark all downstream obligations as depending on an assumption.

Recommended CLI output:

```text
VERIFIED, assuming:
  - file.py:42: P
```

---

## 14. Loop Specifications

Use structured comments inside loops.

```python
while i < len(xs):
    #@ invariant: 0 <= i <= len(Xs)
    #@ invariant: list_model(xs, Xs)
    #@ invariant: total == sum(Xs[:i])
    #@ decreases: len(Xs) - i
    total += xs[i]
    i += 1
```

Grammar:

```text
invariant: P
decreases: term
```

`decreases` is optional if Axiomander is only proving partial correctness. It is required for total correctness / termination proofs.

---

## 15. Ghost Variables and Let Bindings

Allow local logical bindings in contracts.

```text
let Xs = old_contents(xs)
```

Preferred syntax inside contract blocks:

```text
where:
    Xs: Seq[int]
    b: int
```

Example:

```python
def pop(xs: list[int]) -> int:
    """
    axiomander:
        where:
            Xs: Seq[int]

        requires:
            owns(xs) * list_model(xs, Xs) * len(Xs) > 0

        modifies:
            xs

        ensures:
            owns(xs)
            * list_model(xs, Xs[:-1])
            * result == Xs[-1]

        raises:
            none
    """
    return xs.pop()
```

`where` variables are existentially bound in the precondition unless otherwise specified.

---

## 16. Predicates

Nagini and Viper support user-defined predicates that encapsulate ownership and shape.

Axiomander should support verifier-only predicate definitions.

### 16.1 Comment/docstring predicate definition

```python
class Account:
    balance: int

    """
    axiomander predicate account_state(self, b: int):
        owns(self)
        * field(self, "balance", b)
    """
```

### 16.2 Module-level predicate definition

```python
"""
axiomander:
    predicate account_state(a: Account, b: int):
        owns(a)
        * field(a, "balance", b)
"""
```

### 16.3 Fold/unfold policy

Early Axiomander should make predicates transparent by default.

Later, support explicit:

```text
fold account_state(a, b)
unfold account_state(a, b)
```

Comment syntax:

```python
#@ unfold: account_state(a, b)
#@ fold: account_state(a, b)
```

---

## 17. Pure Functions and Specification Functions

Axiomander needs pure logical helpers.

### 17.1 Pure function marker

```python
def is_sorted(xs: list[int]) -> bool:
    """
    axiomander:
        pure
        requires:
            list_model(xs, Xs)
        ensures:
            result == forall i: int :: 0 <= i < len(Xs)-1 implies Xs[i] <= Xs[i+1]
    """
    ...
```

But for most helpers, prefer verifier-only definitions:

```text
function sorted_seq(Xs: Seq[int]) -> bool:
    forall i: int :: 0 <= i < len(Xs)-1 implies Xs[i] <= Xs[i+1]
```

### 17.2 Ghost/spec-only function definitions

```python
"""
axiomander:
    function sorted_seq(Xs: Seq[int]) -> bool:
        forall i: int :: 0 <= i < len(Xs)-1 implies Xs[i] <= Xs[i+1]
"""
```

These functions do not exist at runtime.

---

## 18. Framing and Modifies

Axiomander should combine separation logic with explicit `modifies` clauses.

Example:

```python
def rename_user(user: User, new_name: str) -> None:
    """
    axiomander:
        requires:
            user_state(user, U)
            * new_name != ""

        modifies:
            user.name

        ensures:
            user_state(user, U["name" := new_name])

        raises:
            none
    """
    user.name = new_name
```

Rules:

1. Anything not in `modifies` must be preserved.
2. Anything in the separating frame but not touched by the function is automatically preserved.
3. If `modifies` is omitted, infer from ownership predicates where possible, but warn for external resources.

Recommended default:

```text
modifies: inferred
```

For serious verification, require explicit `modifies` for public functions.

---

## 19. Database Regions

Axiomander should treat databases as abstract heap regions.

```text
db_region(db, D)
```

Meaning:

> The database handle `db` is associated with logical database state `D`.

Example:

```python
def create_user(db: DB, user: User) -> None:
    """
    axiomander:
        requires:
            db_region(db, D)
            * pydantic_model(user, User, U)
            * U["id"] not in D.users

        modifies:
            db

        ensures:
            db_region(db, D.users[U["id"] := U])

        raises DuplicateUser as e:
            db_region(db, D)
            * U["id"] in D.users

        raises DatabaseError as e:
            exists D2: DBState :: db_region(db, D2) * db_failure_relation(D, D2, e)

        raises:
            declared
    """
    ...
```

For transactions:

```python
def transfer(db: DB, a: AccountId, b: AccountId, amount: int) -> None:
    """
    axiomander:
        requires:
            db_region(db, D)
            * D.accounts[a].balance >= amount
            * amount > 0

        modifies:
            db

        ensures:
            db_region(db, transfer_effect(D, a, b, amount))

        raises Exception as e:
            db_region(db, D)
            * transaction_rolled_back(e)
    """
    with transaction(db):
        ...
```

---

## 20. Context Managers

Context managers should be specified because they are Python's main resource-safety idiom.

```python
class LockGuard:
    def __enter__(self) -> None:
        """
        axiomander:
            requires:
                lock_state(self.lock, unlocked)
            ensures:
                lock_state(self.lock, locked_by(current_thread()))
            raises:
                none
        """

    def __exit__(self, exc_type, exc, tb) -> bool:
        """
        axiomander:
            requires:
                lock_state(self.lock, locked_by(current_thread()))
            ensures:
                lock_state(self.lock, unlocked)
                * result == False
            raises:
                none
        """
```

Axiomander should desugar:

```python
with cm:
    body
```

into:

```text
enter cm;
try body finally exit cm
```

and propagate exceptional postconditions through `__exit__`.

---

## 21. Concurrency Predicates

Axiomander should eventually support:

```text
lock_state(lock, state)
thread_token(t)
permission_token(name)
shared_inv(name, P)
atomic_update(P, Q)
```

Early examples:

```text
lock_state(l, unlocked)
lock_state(l, locked_by(current_thread()))
```

A lock-protected object can be modelled as:

```text
protected_by(obj, lock, invariant_name)
```

or:

```text
lock_inv(lock, P)
```

---

## 22. Class Invariants

Nagini-style systems often support invariants. Axiomander should support class invariants in docstrings.

```python
class Account:
    balance: int

    """
    axiomander:
        invariant:
            field(self, "balance", b) * b >= 0
    """
```

Rules:

1. Public methods must establish the class invariant on exit.
2. Public methods may assume the invariant on entry.
3. Private/internal methods may temporarily break it if marked.

Optional marker:

```text
may_break_invariant
```

---

## 23. Lemmas

Support ghost lemmas for proof help.

```python
def lemma_sorted_tail(Xs: Seq[int]) -> None:
    """
    axiomander:
        lemma
        requires:
            sorted_seq(Xs) * len(Xs) > 0
        ensures:
            sorted_seq(Xs[1:])
        raises:
            none
    """
    pass
```

The body may be empty, proof-script-like, or delegated to Coq/SMT/LLM proof search.

---

## 24. Result, Previous, and Iterator Support

Nagini uses helper concepts such as `Result()` and `Previous(...)` in loop reasoning. Axiomander should provide equivalents.

### 24.1 Result

Use:

```text
result
```

Alias accepted:

```text
Result()
```

### 24.2 Previous iterator elements

For loops:

```python
for x in xs:
    #@ invariant: processed == Previous(x)
    ...
```

Axiomander can support:

```text
previous(x)
```

or Nagini-compatible:

```text
Previous(x)
```

Meaning:

> The logical sequence of iterator elements already consumed before the current iteration.

---

## 25. Built-in Runtime-Safety Obligations

By default, Axiomander should generate obligations for:

1. No `IndexError` on list indexing.
2. No `KeyError` on dict indexing unless declared.
3. No `AttributeError` on attribute access.
4. No `TypeError` from invalid operations.
5. No `ZeroDivisionError`.
6. No assertion failure.
7. No uncaught exception escaping unless permitted by `raises`.
8. No mutation without ownership/permission.
9. No use-after-close for modelled resources.
10. No lock leak across exceptional paths.

This should be the default meaning of:

```text
raises: no_runtime_errors
```

---

## 26. Recommended Predicate Vocabulary

### Core

```text
emp
P * Q
old(e)
result
forall x: T :: P
exists x: T :: P
implies(P, Q)
```

### Permissions

```text
owns(x)
acc(x.f)
acc(x.f, fraction)
field(x, "f", v)
readonly(x)
mutable(x)
```

### Built-in containers

```text
list_model(xs, Xs)
dict_model(d, D)
set_model(s, S)
list_pred(xs)
dict_pred(d)
set_pred(s)
```

### Objects and Pydantic

```text
object_model(obj, Shape, Data)
pydantic_model(obj, ModelType, Data)
field(obj, name, value)
```

### External resources

```text
db_region(db, D)
file_region(f, F)
socket_region(s, S)
service_region(client, S)
```

### Transactions

```text
transaction_open(db, tx, D)
transaction_committed(tx)
transaction_rolled_back(e)
```

### Concurrency

```text
lock_state(lock, state)
locked_by(thread)
current_thread()
shared_inv(name, P)
token(name)
```

---

## 27. Example: Nagini-Like Source vs Axiomander Source

### Nagini-like style

```python
from nagini_contracts.contracts import *

class Cell:
    def __init__(self, value: int) -> None:
        Requires(Acc(self.value))
        Ensures(Acc(self.value) and self.value == value)
        self.value = value
```

### Axiomander library-free style

```python
class Cell:
    value: int

    def __init__(self, value: int) -> None:
        """
        axiomander:
            requires:
                acc(self.value)

            modifies:
                self.value

            ensures:
                acc(self.value)
                * field(self, "value", value)

            raises:
                none
        """
        self.value = value
```

Alternative Axiomander-native style:

```python
class Cell:
    value: int

    def __init__(self, value: int) -> None:
        """
        axiomander:
            requires:
                owns(self)

            modifies:
                self.value

            ensures:
                field(self, "value", value)

            raises:
                none
        """
        self.value = value
```

---

## 28. Example: Exceptional Contract

```python
def divide(n: int, d: int) -> int:
    """
    axiomander:
        requires:
            True

        ensures:
            d != 0
            * result == n // d

        raises ZeroDivisionError as e:
            d == 0

        raises:
            declared
    """
    return n // d
```

For safer application code, prefer forbidding the exception:

```python
def divide(n: int, d: int) -> int:
    """
    axiomander:
        requires:
            d != 0

        ensures:
            result == n // d

        raises:
            none
    """
    return n // d
```

---

## 29. Example: Object Mutation

```python
def deposit(account: Account, amount: int) -> None:
    """
    axiomander:
        where:
            b: int

        requires:
            account_state(account, b)
            * amount > 0

        modifies:
            account.balance

        ensures:
            account_state(account, b + amount)

        raises ValueError as e:
            account_state(account, b)
            * amount <= 0

        raises:
            declared
    """
    if amount <= 0:
        raise ValueError("amount must be positive")
    account.balance += amount
```

---

## 30. Example: List Mutation

```python
def pop_nonempty(xs: list[int]) -> int:
    """
    axiomander:
        where:
            Xs: Seq[int]

        requires:
            list_model(xs, Xs)
            * len(Xs) > 0

        modifies:
            xs

        ensures:
            list_model(xs, Xs[:-1])
            * result == Xs[-1]

        raises:
            none
    """
    return xs.pop()
```

If empty pop is allowed:

```python
def pop_maybe(xs: list[int]) -> int:
    """
    axiomander:
        where:
            Xs: Seq[int]

        requires:
            list_model(xs, Xs)

        modifies:
            xs

        ensures:
            len(Xs) > 0
            * list_model(xs, Xs[:-1])
            * result == Xs[-1]

        raises IndexError as e:
            len(Xs) == 0
            * list_model(xs, Xs)

        raises:
            declared
    """
    return xs.pop()
```

---

## 31. Example: Database Transaction

```python
def reserve_item(db: DB, item_id: str, n: int) -> None:
    """
    axiomander:
        where:
            D: DBState

        requires:
            db_region(db, D)
            * n > 0

        modifies:
            db

        ensures:
            stock(D, item_id) >= n
            * db_region(db, update_stock(D, item_id, stock(D, item_id) - n))

        raises OutOfStock as e:
            stock(D, item_id) < n
            * db_region(db, D)

        raises DatabaseError as e:
            db_region(db, D)
            * transaction_rolled_back(e)

        raises:
            declared
    """
    with transaction(db):
        ...
```

---

## 32. Parsing Rules

Axiomander should parse contracts using an indentation-sensitive grammar close to YAML but not full YAML.

Rules:

1. Contract blocks begin with `axiomander:`.
2. Section headers end with `:`.
3. Section bodies are logical expressions over one or more indented lines.
4. Blank lines are ignored.
5. `*` is separating conjunction, not multiplication, inside predicate position.
6. Arithmetic multiplication should use normal Python expression context; ambiguity can be resolved by requiring spaces around separating conjunction or by parser precedence.
7. Names introduced in `where` are logical variables.
8. Python parameters, class fields, and local variables are in scope where appropriate.

Recommended precedence:

```text
highest: attribute/index/function application
         arithmetic
         comparisons
         not
         and
         or
         implies
lowest:  separating conjunction (*)
```

However, because `*` is also arithmetic multiplication, Axiomander should encourage parentheses in mixed arithmetic/separation formulas.

---

## 33. Internal Representation

Each function should elaborate to:

```python
FunctionContract(
    pre=Predicate,
    reads=[Resource],
    modifies=[Resource],
    normal_post=Predicate,
    exceptional_posts={ExceptionType: Predicate},
    exception_policy=ExceptionPolicy,
    ghost_vars=[GhostVar],
)
```

Each command should verify against a multi-exit judgement:

```text
Γ ⊢ {P} command { normal: Q; raises: EMap }
```

Weakest precondition should be continuation-based:

```text
wp(command, normal_continuation, exception_continuations)
```

This is essential for `try`, `except`, `finally`, `with`, and function calls.

---

## 34. Migration Strategy

### Phase 1: Contract parser

Implement:

```text
requires
ensures
raises
where
modifies
```

with ordinary pure expressions and no heap ownership.

### Phase 2: Runtime-error obligations

Generate checks for:

```text
IndexError
KeyError
AttributeError
TypeError
ZeroDivisionError
AssertionError
```

### Phase 3: Basic heap predicates

Implement:

```text
owns
field
list_model
dict_model
```

### Phase 4: Separation logic framing

Implement:

```text
emp
P * Q
frame rule
modifies preservation
```

### Phase 5: Pydantic shape integration

Implement:

```text
pydantic_model(obj, Model, Data)
```

using Pydantic model schemas as shape sources.

### Phase 6: Database regions and transactions

Implement:

```text
db_region
transaction_rolled_back
transaction effects
```

### Phase 7: Concurrency

Implement:

```text
lock_state
tokens
shared invariants
fractional permissions
```

---

## 35. Summary Recommendation

Axiomander should adopt a Nagini-inspired vocabulary but not Nagini's mandatory import-based syntax.

Use this as the canonical style:

```python
def f(x: T) -> U:
    """
    axiomander:
        where:
            G: GhostType

        requires:
            P

        reads:
            R

        modifies:
            M

        ensures:
            Q(result)

        raises SomeException as e:
            E(e)

        raises:
            declared | none | no_runtime_errors | any
    """
    ...
```

This gives Axiomander:

1. A familiar pre/postcondition style.
2. Explicit exceptional exits.
3. A natural path to separation logic.
4. Compatibility with Nagini/Viper concepts.
5. A zero-runtime-library source format.
6. Enough structure for realistic Python contracts involving objects, Pydantic models, databases, transactions, and concurrency.

