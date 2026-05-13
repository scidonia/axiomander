# Standalone MCP Tool — Revised Design

## Key Insight

**Vanilla Python. Zero imports.** The user writes standard `assert` statements.
Axiomander's `assertion_finder.py` discovers and classifies them by position:

```python
def add(a: int, b: int) -> int:
    assert True              # → precondition (first statement)
    result = a + b
    assert result == a + b   # → postcondition (before return)
    return result
```

No `@requires`, no `@ensures`, no `from verify_contracts import ...`.
Just Python `assert`, which every developer already knows.

## Architecture

```
User's Python (zero deps)
        │  assert P  ...  assert Q
        ▼
┌──────────────────────────────────────────┐
│  Axiomander frontend (reused)            │
│  ├─ assertion_finder.py  → classify      │
│  ├─ purity_analyzer.py   → pure/impure   │
│  └─ weakest_precondition.py → compute WP │
└──────────────────┬───────────────────────┘
                   │  WP result (Python ast.expr)
                   ▼
┌──────────────────────────────────────────┐
│  Our Coq pipeline                        │
│  ├─ translate WP → Coq theorem           │
│  ├─ Level 1: wp_reduce (Ltac)            │
│  ├─ Level 2: hammer (cvc4/eprover)       │
│  └─ Level 3: LLM oracle                  │
└──────────────────┬───────────────────────┘
                   │  VerificationReport
                   ▼
┌──────────────────────────────────────────┐
│  MCP server                              │
│  Tool: verify-contracts                  │
│  Returns: per-goal status + guidance     │
└──────────────────────────────────────────┘
```

## What we reuse from Axiomander

| Module | What it does | How we use it |
|--------|-------------|---------------|
| `assertion_finder.py` | Finds `assert` in AST, classifies as pre/post/invariant by position | Contract discovery — replaces our `@requires`/`@ensures` decorators |
| `purity_analyzer.py` | Whitelist-based pure/impure classification | Determines which statements are safe for IMP extraction |
| `weakest_precondition.py` | Backward WP through assignments, ifs, asserts | Computes the WP condition; we translate it to Coq |
| `smt_translator.py` | Python AST → Z3 formulas | Architecture pattern for our Python→Coq translator |

## What we replace from Axiomander

| Axiomander | Our replacement |
|------------|----------------|
| Z3 backend (direct SAT/UNSAT check) | Coq + hammer + LLM pipeline |
| LSP server (editor-facing) | MCP server (agent-facing) |
| `--backend z3` (default) | `--backend coq` (our pipeline) |

## Assertion classification rules

Axiomander classifies `assert` statements by position:

| Position | Classification | Example |
|----------|---------------|---------|
| First statement in function (after docstring) | `PRECONDITION` | `assert x > 0` |
| Before `return` (no intervening non-assert code) | `POSTCONDITION` | `assert result > 0` |
| First statement in `for`/`while` body | `LOOP_INVARIANT` | `assert acc == i*(i+1)//2` |
| Heuristic: comparison with function param | `TERMINATION` | `assert n - i >= 0` |
| Everything else | `GENERAL` | — |

## User workflow in an opencode session

```
1. User writes Python with assert-based contracts
       ↓
2. Agent calls MCP tool: verify-contracts
       ↓
3. Server returns:
     ✓ add       — proved (level1)
     ✗ sum_to    — add_loop_invariant
       ↓
4. Agent adds invariant:
       while i < n:
           assert acc == i * (i + 1) // 2   ← added
           i += 1; acc += i
       ↓
5. Agent calls verify-contracts again
       ↓
6. Server returns:
     ✓ sum_to    — proved (level1)
```

## Implementation plan

1. Add Axiomander as a dependency of refactoring-robots (it's pip-installable)
2. Write a Python→Coq translator that takes Axiomander's WP output (`ast.expr`) and produces Coq theorem statements
3. Wire up the 3-tier pipeline to consume Axiomander's results
4. The MCP server calls `axiomander.verification.orchestrator` for contract discovery, then routes WP to our Coq pipeline
5. Zero changes to Axiomander itself (we consume it as a library)
