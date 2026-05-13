# Strategy: Incremental Correctness for Python via Assert Proof

## Philosophy

You don't need to prove everything. You don't need decorators. You don't need
new tooling in your editor. You just need to start adding `assert` statements,
and the tool will tell you what's missing, what's wrong, and how to fix it.

This is the "TypeScript for correctness" approach: TypeScript brought types to
JavaScript incrementally — add a `.d.ts` here, a type annotation there.
We bring **proofs** to Python incrementally — add an `assert` here, an
invariant there.

## The Assert Contract Language

Contracts are standard Python `assert` statements. Their position in the code
determines their role:

| Position | Classification | Example |
|----------|---------------|---------|
| First statement in function | `precondition` | `assert x >= 0` |
| First statement in loop body | `invariant` | `assert acc == i * (i+1) // 2` |
| Immediately before `return` | `postcondition` | `assert result >= 0` |

No imports. No decorators. No language changes. Just `assert`.

## The Incremental Loop

```
1. Write code        ─── any Python, no contracts needed
2. check-file        ─── MCP suggests where to add asserts
3. Add asserts       ─── the user or an LLM agent adds them
4. check-function    ─── verify one function
        │
        ├─ ✓ Proved (level1)     ─── done, move on
        ├─ ✗ Missing contracts   ─── add suggested assertions
        ├─ ✗ Hammer/LLM needed   ─── tool tries SMT, then LLM oracle
        └─ ✗ Property may be false ─── fix the code or the contract
5. Repeat            ─── until all critical functions are verified
```

## What You Prove vs. What You Trust

```
Verified (the tool proves):
  - Precondition ⇒ postcondition for your own functions
  - Loop invariants are preserved
  - Conditional branches satisfy their contracts

Trusted (you assume it's correct):
  - Library function contracts (from .pyi stubs or docstrings)
  - Python interpreter behavior
  - Pydantic model validation
  - The IMP→Coq translation

Untrusted (the tool doesn't verify — black holes):
  - External API calls (LLM, database, network)
  - Unannotated library functions
  - File I/O, side effects
```

The black hole theory from Axiomander handles untrusted code: it identifies
which variables may be affected, preserves what it can, and tells you what
assertions you need to add to recover full verification.

## The 3-Tier Proof Pipeline

```
Goal
  │
  ├─ Level 1: wp_reduce (Ltac)
  │     Handles: structural WP, state simplification, simple arithmetic
  │     Success rate: ~80% of goals
  │
  ├─ Level 2: coq-hammer (cvc4 + eprover)
  │     Handles: pure Z arithmetic, first-order logic
  │     Success rate: ~15% of remaining goals
  │
  └─ Level 3: LLM oracle (DeepSeek)
        Handles: complex arithmetic, invariants, inductive reasoning
        Success rate: model-dependent
```

## What Works Today (May 2026)

| Feature | Status |
|---------|--------|
| Scalar arithmetic (`add`, `max_of_two`) | ✓ Verified |
| Conditionals (`if/elif/else`, `clamp`) | ✓ Verified |
| Loop invariants (detection + guard) | ✓ Detected, VCG Admitted |
| Record types (`class Account: balance: int`) | ✓ Generated |
| Record field access (`account.balance`) | ✓ Scoped correctly |
| Modular contracts (call-site analysis) | Design complete |
| Library contract stubs (`.pyi` / docstrings) | Design complete |
| Arrays, strings, collections | Not yet |
| Type inference from annotations | Not yet |

## Comparison to Related Work

| Tool | Approach | User code changes |
|------|----------|-------------------|
| Refactoring Robots | assert contracts → Coq proofs | Zero (just asserts) |
| Axiomander | assert contracts → Z3 SMT | Zero (just asserts) |
| Dafny | Annotation language → Boogie | New language |
| F* | Dependent types → SMT | New language |
| Why3 | Annotation language → multiple provers | New language |
| Nagini | Python + annotations → Viper | Decorators + imports |

Our advantage: zero imports, zero decorators, standard Python. You can run
the code as-is in production — the `assert` statements ARE the runtime checks.

## Production vs Verification Mode

Python's `-O` flag strips all `assert` statements from compiled bytecode.
This is standard Python behavior since 1.x:

```bash
python script.py         # verification mode — asserts active, contracts checked
python -O script.py      # production mode — all asserts stripped, zero overhead
PYTHONOPTIMIZE=1 gunicorn myapp   # production deployment
```

No pre-processor, no conditional imports, no code changes. The same `.py` file
serves both purposes. The verification tool reads the source; production runs
without the checks.

## Next Milestones

1. **Close the VCG gap** — prove while-exit obligations (blocking loop verification)
2. **Collections** — arrays, strings, `len()`, `all()/any()`
3. **Library stubs** — `.pyi` contract stubs for modular verification
4. **Call-site composition** — verify callers using callee contracts
5. **Production deployment** — the paper-review pipeline end-to-end
