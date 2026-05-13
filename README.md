# Refactoring Robots

A Hoare-logic verification pipeline for Python. Write pre/post contracts and loop invariants as Python decorators. The pipeline translates them into weakest-precondition proof obligations, formalised in Coq. SMT solvers clear the easy goals; an LLM oracle tackles the rest.

## Pipeline

```
Python source + @requires / @ensures / @invariant
              │
              ▼
     [WP Transformer]  (Python AST → proof obligations)
              │
              ▼
     Coq theory: IMP language + WP calculus + soundness
              │
              ▼
     [SMT hammer]  (coq-hammer / SMTCoq / Z3)
              │
              ▼ (remaining goals)
     [LLM oracle]  →  Coq proof script  →  coqc  →  Qed / ✗
```

## Why This Works

| Concern | Solution |
|---|---|
| LLM ecosystem is Python-native | Contracts live in Python, LLM speaks Python |
| Python has no static verifier | We build one, backed by Coq |
| Full verification is hard | SMT solves the easy stuff, LLM the hard stuff |
| Soundness is paramount | WP calculus formalised and proven sound in Coq |

## Project Structure

```
docs/                       Design documents
  ARCHITECTURE.md           Full architecture spec
  WP_CALCULUS.md            Hoare/WP theory

coq/                        Coq formalisation
  Imp.v                     IMP language syntax + semantics
  Wp.v                      Weakest precondition calculus
  Soundness.v               Soundness proof: {P} c {Q} ↔ P ⇒ wp(c,Q)
  VcGen.v                   Verification condition generator

py/                         Python side
  contracts/                Decorator library
  wp_transformer/           AST → Coq proof obligations
  oracle/                   LLM proof oracle client

server/                     Dream web server (proof dashboard)
bin/                        CLI entry points
```

## Stack

| Layer | Technology |
|---|---|
| Contracts | Python decorators (`@requires`, `@ensures`, `@invariant`) |
| WP engine | Python `ast` module → Coq obligations |
| Proof kernel | Coq (Rocq), IMP formalisation, WP calculus |
| SMT bridge | coq-hammer / SMTCoq / SMT-LIB export |
| LLM oracle | Cohttp → LLM API → Coq proof script |
| Web UI | Dream (OCaml) — submit files, view proof status |

## The Hoare Triple Model

```
    {P}          precondition  — @requires(lambda args: ...)
    c            command       — the Python function body
    {Q}          postcondition — @ensures(lambda args, result: ...)
```

Loop invariants use `@invariant`:

```python
@requires(lambda n: n >= 0)
@ensures(lambda n, r: r == n * (n + 1) // 2)
@invariant(lambda i, acc: acc == i * (i + 1) // 2 and i <= n)
def sum_to(n):
    acc = 0
    for i in range(n + 1):
        acc += i
    return acc
```

## Proof Strategy

1. **WP transformer** generates `∀ args, P(args) → wp(body, Q(args, result))`
2. **SMT** attempts to prove the goal. If proved → done.
3. **Coq hammer** tries `sauto`, `smt`, `lia`, `nia`.
4. **LLM oracle** receives the remaining goal, generates a Coq proof script.
5. **coqc** verifies the script. If it passes → `Qed`. If not → back to LLM with error.

## Development Sequence

1. Coq formalisation of IMP + WP calculus + soundness proof
2. Python decorator library
3. Simple WP transformer (straight-line code, no loops)
4. SMT integration via coq-hammer
5. LLM oracle client
6. Loop invariant support
7. Web dashboard
