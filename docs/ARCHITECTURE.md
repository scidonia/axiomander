# Architecture

## Overview

Axiomander is a verification pipeline for Python. Users annotate Python functions with Hoare-logic contracts using decorators. The pipeline translates these into proof obligations formalised in Coq, dispatches them through SMT solvers, and falls back to an LLM oracle for the hard cases.

## Pipeline Stages

### Stage 1: Annotation (Python)

The user writes Python with three decorator types:

```python
@requires(lambda x: x > 0)           # precondition
@ensures(lambda x, result: result > 0)  # postcondition
@invariant(lambda i, acc: acc == i * (i+1)//2)  # loop invariant
def my_function(...):
    ...
```

These decorators are purely metadata at runtime — they don't enforce anything. They store the contracts for the WP transformer to read.

### Stage 2: WP Transformer (Python)

Python's `ast` module parses the annotated source. The WP transformer:

1. Walks the AST of each decorated function
2. Extracts the contracts from the decorator AST nodes
3. Computes the weakest precondition of the function body with respect to the postcondition
4. Generates the proof obligation: `∀ args. P(args) → wp(body, Q(args, result))`
5. Emits a Coq `.v` file with the obligation as a theorem

For a function `f(x)` with `@requires P` and `@ensures Q` and body `c`:

```coq
Theorem f_correct : forall x, P x -> wp c (fun y => Q x y).
Proof.
  (* proof to be filled *)
Admitted.
```

### Stage 3: SMT Hammering (Coq)

The generated Coq file is processed by:

1. **coq-hammer** — tries external ATPs (Z3, CVC5, Eprover) via `sauto` or the hammer tactic
2. **SMTCoq** — direct Z3/CVC4 integration for arithmetic, bitvectors
3. **lia / nia** — Presburger / non-linear integer arithmetic tactics

If any of these close the goal, the theorem is `Qed`-ed. Remaining goals advance to Stage 4.

### Stage 4: LLM Oracle

Unproven goals are sent to an LLM (via HTTP API). The prompt includes:

- The Coq goal statement
- The definitions of all relevant functions and predicates
- The current proof context (hypotheses available)
- Examples of similar proofs from the codebase

The LLM returns a Coq proof script. The pipeline:

1. Writes the script into the `.v` file
2. Runs `coqc` on it
3. If it compiles → `Qed`. If not → extracts the error, feeds it back to the LLM with a retry prompt
4. Retries up to N times (configurable)

## IMP Language

We verify a subset of Python that maps cleanly to a simple imperative language (IMP):

```
e ::= n | x | e1 + e2 | e1 - e2 | e1 * e2 | e1 == e2 | e1 < e2 | not e | ...
c ::= skip
    | x := e
    | c1 ; c2
    | if e then c1 else c2
    | while e with invariant I do c
    | assert P
```

State is a map from variable names to integer values. All variables are integers (for now).

The WP transformer maps Python to IMP:
- Python `if/else` → IMP `if`
- Python `while` → IMP `while` (invariant extracted from `@invariant`)
- Python assignments → IMP `:=`
- Python `for i in range(n)` → IMP `while` with counter variable
- Python `return e` → `result := e`

## Coq Theory Structure

```
Imp.v          Syntax, state, big-step semantics
Wp.v           Weakest precondition definition, wp laws
Soundness.v    {P} c {Q} ↔ (∀ s. P s → wp c Q s)
VcGen.v        Verification condition generator, automation tactics
```

## SMT Integration

Two paths:

### Path A: coq-hammer

```coq
From Hammer Require Import Hammer.
Goal wp (Seq (Assign "x" (Plus (Var "x") (Const 1))) (Assign "y" (Var "x"))) 
        (fun s => s "y" = 42).
Proof.
  hammer.
Qed.
```

coq-hammer calls external provers (Z3, CVC5, Eprover) and reconstructs proofs.

### Path B: SMT-LIB export

Export the proof obligation to SMT-LIB format, call Z3 directly, then trust the result as an axiom in Coq. Faster but adds a trust boundary.

## LLM Oracle Protocol

```
INPUT:
  goal: "∀ s, s "x" = 5 → wp (Assign "y" (Var "x")) (fun s => s "y" = 5) s"
  context: [definition of wp, definition of Assign, upd syntax]
  examples: [similar proved theorems]

→ LLM generates Coq proof script

OUTPUT:
  success: "Proof. intros s H. unfold wp. simpl. rewrite H. reflexivity. Qed."
  failure: error message from coqc → retry
```

## Web Dashboard (Dream)

The OCaml Dream server provides:

- `POST /verify` — submit a Python file, get back proof status per function
- `GET /status/:id` — poll for proof progress
- `GET /` — web UI for file upload and result display

## Future: Coq Extraction of the Pipeline

Once the WP calculus is proven sound in Coq, the pipeline itself can be extracted to OCaml:

- The WP transformer becomes verified Coq → extracted OCaml
- The VCG becomes verified Coq → extracted OCaml
- The trust boundary shrinks to: the Python→IMP translator and the SMT/LLM results
