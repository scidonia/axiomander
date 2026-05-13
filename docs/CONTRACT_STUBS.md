# Modular Verification with Contract Stubs

## The Problem

When analyzing `caller()` which calls `callee(x)`, we need:
1. What must be true before the call? (callee's precondition)
2. What becomes true after the call? (callee's postcondition)

Without this, every function call is a black hole with no recovery assertion.

## The Mechanism: `.pyi` Contract Stubs

Like TypeScript's `.d.ts` files for types, we use `.pyi` files for contracts:

```python
# math_contracts.pyi

def sqrt(x: float) -> float:
    """Returns the square root of x."""
    assert x >= 0                           # precondition
    assert result * result - x < 1e-10     # postcondition (within epsilon)

def isqrt(n: int) -> int:
    """Integer square root."""
    assert n >= 0                           # precondition
    assert result * result <= n             # postcondition
    assert (result + 1) * (result + 1) > n  # tight bound
```

## How It Composes

### Caller Analysis

```python
def distance(x: int, y: int) -> float:
    assert x >= 0 and y >= 0       # caller precondition
    
    xx = x * x
    yy = y * y
    sum_sq = xx + yy
    
    result = sqrt(sum_sq)          # function call
    
    assert result >= 0             # caller postcondition
    return result
```

The MCP processes this as:

```
Step 1: sum_sq >= 0 must hold at call site
        → Verify: xx + yy >= 0 (always true since x,y >= 0)

Step 2: The call is a black hole with affected set {result}

Step 3: Recovery assertion from sqrt.pyi:
        result * result - sum_sq < 1e-10

Step 4: Caller uses recovery assertion to prove its own postcondition:
        result >= 0 follows from result * result ≈ sum_sq >= 0
```

### Coq Encoding

The black hole for `sqrt(sum_sq)` becomes:

```coq
(* Call site: result = sqrt(sum_sq) *)
CHavoc ["result"%string]

(* Recovery: the postcondition from sqrt's contract stub *)
(* After the havoc, the caller re-asserts: *)
(*   result * result - sum_sq < 1e-10 *)
```

And the caller's proof obligation includes:

```coq
(* Caller must prove sqrt's precondition at the call site *)
Theorem caller_pre_satisfies_sqrt_pre : forall x y, 
  x >= 0 /\ y >= 0 -> x*x + y*y >= 0.   (* sqrt requires argument >= 0 *)
Proof. intros. nia. Qed.
```

## Contract Stub Discovery

The MCP looks for contract stubs in this order:

1. **Inline** — the function's own file has `assert` contracts
2. **`.pyi` files** — companion stubs next to the library (e.g. `math_contracts.pyi`)
3. **Project contracts dir** — `contracts/<module>/<function>.pyi`
4. **Contract registry** — online database (future)

### Example: using a third-party library

```python
# my_app.py
import requests

def get_api_data(url: str) -> dict:
    assert url.startswith("https://")
    response = requests.get(url)       # external call — black hole
    assert response.status_code == 200
    return response.json()
```

```
contracts/requests/api.pyi:

def get(url: str) -> Response:
    assert url.startswith("http")      # precondition
    assert result is not None          # postcondition
```

## Certification vs Trust

Contracts from:
- **Your code** → verified by the MCP
- **Library `.pyi` stubs** → trusted (assumed correct)
- **No stubs** → black hole with no recovery assertion (verification is partial)

This is the same trust model as TypeScript's `@types` packages.

## Implementation Plan

1. Add `.pyi` parsing to `contract_linter.py`
2. `check-file` scans for `.pyi` files in the project and dependencies
3. `check-function` resolves function calls against contract stubs
4. Generated Coq includes the callee's postcondition as a recovery assertion
5. Generated Coq includes the callee's precondition as an additional caller obligation

## Relationship to Black Hole Theory

This integrates directly with our Axiomander-inspired black hole theory:

```
Function call             → CHavoc {result}
Callee's postcondition    → Recovery assertion (Q_drop that we re-assert)
Callee's precondition     → New caller obligation (must be proved at call site)
```

The black hole has affected set `{result}` (and any mutated fields).
The recovery assertion is the callee's postcondition, instantiated with
the caller's arguments.
