# AGENTS.md

## Project

Axiomander is a Hoare-logic verification pipeline for Python.

Users annotate Python functions with `@requires`, `@ensures`, `@invariant` decorators.
The pipeline translates these into weakest-precondition proof obligations in Coq.
SMT solvers clear the easy goals; an LLM oracle generates proofs for the rest.

## Design Philosophy

Axiomander aims to be **the gold standard for verification systems**.
Every architectural decision must be *the right way* from the ground up.
No half-baked approaches. No shortcuts that paper over a fundamental mismatch.
If a feature requires two representations, unify them. If a type system is
incomplete, extend it fully rather than encoding around the gaps.
The goal is not to pass tests — it's to build a sound, composable,
and extensible verification stack that holds up under real-world use.

**Ground rules:**
- Python's runtime type system must be reflected in the `value` type.
  Coercion rules must follow Python's semantics (float+int→float, etc.).
- Contracts are plain `assert` statements — zero imports, zero decorators.
- The WP calculus is the single source of truth, proven sound in Coq.
- Frame conditions are explicit, enforced, and derive from the callee's
  declared `reads`/`writes`, not from implementation details.
- `simpl`/`cbn` reduction is controlled — Fixpoint reduction must not
  expand structural comparisons (`In`, `clobber`) before lemmas fire.
- Immutable values (VList, VTuple, VDict) are structural, like Dafny's
  `seq` and F*'s `list`. Mutable operations (append, pop) work on a
  separate heap representation that parallels the value.
- Every new type or operation must have negative tests that demonstrate
  the verifier catches violations, not just passes trivially. Negative
  tests prove the system isn't "proving everything."

## Directory Layout

```
coq/          Coq formalisation (IMP language, WP calculus, soundness, VCG)
py/           Python side (contract decorators, WP transformer, LLM oracle)
server/       Dream web dashboard
docs/         Architecture and theory documents
```

## Build Commands

```bash
# OCaml + Coq
eval $(opam env)
dune build

# Python side (when present)
eval $(opam env); PYTHONPATH=py .venv/bin/python -m pytest py/tests/ -v

# Web server (needs libssl-dev, libev-dev, then `opam install dream`)
dune exec server/server.exe

# Full verification pipeline
eval $(opam env)
cd /path/to/axiomander
PYTHONPATH=. python3 -m py.oracle.pipeline py/examples/demo.py

# Set LLM API key for Level 3 oracle
export DEEPSEEK_API_KEY="sk-..."
# or
export ORACLE_API_KEY="sk-..."
export ORACLE_API_URL="https://api.deepseek.com/v1/chat/completions"
export ORACLE_MODEL="deepseek-chat"
```

## Code Conventions

### Coq
- Use `From Stdlib Require Import` prefix (Rocq 9.x)
- File names: PascalCase.v (matching module name)
- Proof style: short, structured proofs using stdlib tactics
- `Admitted` for WIP lemmas, never leave stray `Admitted` in committed proofs

### OCaml
- Library modules: `snake_case.ml` with `snake_case.mli` interface
- Use dune `(library ...)` for shared code, `(executable ...)` for entry points
- Warning 32 suppression allowed in library modules: `[@@@warning "-32"]`

### Python (when present)
- Decorators in `py/contracts/`
- Use `ast` module for WP transformation (no third-party parsers)
- Type hints on all public functions
- **Never use regex on parse-tree strings.** When you need to extract names or analyze structure, walk the AST or IR tree — it has the grammar's semantics built in. Regex on Coq/IMP strings is fragile: `re.findall(r'\b(\w+)\b', "asZ (s x)")` extracts `asZ` as a "variable". The IR's `Var(name='x')` node tells you `x` is a variable without false positives.

## Key Design Decisions

1. **IMP as intermediate language**: We don't prove properties about arbitrary Python. We map a verified subset (assignments, conditionals, loops) to IMP and prove at that level.
2. **WP over VC**: We use weakest-precondition calculus (Dijkstra-style), not forward VCG. Simpler, more compositional.
3. **SMT then LLM**: SMT handles what it can handle (linear arithmetic, bitvectors). LLM is the fallback, not the first choice.
4. **Coq is the trust base**: The WP calculus is proven sound in Coq. The Python→IMP translator is trusted (or extractable from Coq later).
5. **Vanilla Python contracts**: Contracts use Python `assert` statements (no decorators, no imports). Axiomander's assertion_finder classifies them by position. The user's code stays dependency-free; the MCP server does the heavy lifting.

## Proof Pipeline (3 Tiers)

```
Goal
  │
  ├─ Level 1: Ltac (wp_reduce, lia, reflexivity)
  │     Handles: structural WP unfolding, state simplification,
  │              simple arithmetic, string equality
  │     When to use: always run first; clears ~80% of goals
  │
  ├─ Level 2: SMT (coq-hammer → cvc4 / eprover)
  │     Handles: pure Z arithmetic, first-order logic,
  │              linear inequalities, boolean combinations
  │     When to use: after wp_reduce, on remaining arithmetic goals
  │     Limitations: Z.of_nat, nth, length are opaque to ATPs
  │
  └─ Level 3: LLM oracle
        Handles: loop invariants, inductive proofs,
                 non-linear arithmetic, complex data structure reasoning
        When to use: goals that need induction or deep lemma chains
```

## Hammer Usage (Level 2)

### Quick check
```coq
From Hammer Require Import Hammer.
Goal ...  hammer.
```

### When hammer times out
```coq
Set Hammer ATPLimit 60.       (* default: 20s *)
Set Hammer ReconstrLimit 30.   (* default: 5s *)
```

### When ATPs find a proof but reconstruction fails
Hammer prints the dependency list. Use it to write the manual proof:
```coq
(* Hammer says: CVC4 succeeded, dependencies: Z.sub_succ_l, Z.lt_succ_diag_r, IHn *)
Proof.
  induction n; rewrite Nat2Z.inj_succ; [lia | apply Z.lt_succ_diag_r].
Qed.
```

### Key pattern: case-split before hammering
Hammer never performs induction. Always `destruct`/`induction` first,
then rewrite opaque functions (`Z.of_nat`, `nth`, `length`) before `hammer`:
```coq
Goal forall n, Z.of_nat n - 1 < Z.of_nat n.
Proof.
  induction n.          (* hammer can't do this *)
  - hammer.             (* base case: pure Z, hammer handles it *)
  - rewrite Nat2Z.inj_succ. hammer.  (* convert to Z before hammer *)
Qed.
```

### Where hammer gets stuck
- `Z.of_nat`, `nth`, `length` — opaque to ATPs; rewrite away first
- Classical proofs — can't be reconstructed intuitionistically
- Goals needing induction — must be done manually
- `dependent destruction` / `inversion` on complex inductive types

### Provers available
```
eprover  ✓  — first-order logic (system package)
cvc4     ✓  — SMT arithmetic (apt install cvc4)
z3_tptp  ✗  — needs Z3 ≥ 4.12 built from source (optional)
vampire  ✗  — not installed (optional)
```

## Automation Tactics

### wp_reduce (Level 1 — structural)
```coq
Ltac wp_reduce :=
  unfold wp, upd; simpl; try reflexivity.
```
Clears: assignment WP, state lookups, string equality, trivial arithmetic.

### wp_reduce + lia (Level 1 — arithmetic)
```coq
Ltac wp_finish := wp_reduce; try lia.
```
Clears: linear arithmetic, inequalities, conditional branch goals.

### hammer (Level 2 — SMT)
```coq
From Hammer Require Import Hammer.
Set Hammer ATPLimit 60.
```
Dispatches to cvc4 (arithmetic) and eprover (first-order) in parallel.
Best used after wp_reduce has cleared the structural layer.

## Dependencies

- OCaml ≥ 5.2.0
- Coq (Rocq) ≥ 9.0
- dune ≥ 3.17
- Dream (for web server — optional, needs system deps)
- coq-hammer (for SMT integration)
- Python ≥ 3.10 (for py/ side)

## Session Rules

1. **Commit often.** After each meaningful unit of work (a feature, a bugfix, a test pass), create a commit. Long sessions accumulate changes that are easily lost. Commit messages should be concise and describe the "why."
2. **Never `git checkout --` on multiple files.** That reverts everything indiscriminately. Instead, use `git checkout -- <single-file>` or `git stash` to preserve context. If a file is corrupted by a bad edit, restore only that file.
3. **Verify tests pass after each change.** Run `uv run pytest py/tests/test_pipeline.py -q` before declaring a unit of work done.
4. **Check `git status` before destructive git operations.** Know what you're about to lose.
