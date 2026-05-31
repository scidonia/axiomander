# Dune / Rocq Build Investigation — RESOLVED

## Root Cause

Circular symlink in the rocq 9.1.0 standard library installation:

```
~/.opam/rocq-9/lib/coq/user-contrib/Stdlib/Bool/Bool
  -> /home/gavin/.opam/rocq-9/lib/coq/user-contrib/Stdlib/Bool
```

Dune's rocq integration scans the stdlib tree to build the dependency graph.
A symlink pointing to its own parent creates infinite recursion, consuming
unbounded memory during `dune rules` / `dune build`.

## Fix

1. **Recreate opam switch** — the corrupted stdlib was removed entirely.
2. **Add `(theories Stdlib)`** to `rocq.theory` — the rocq stdlib is a
   separate installed theory and is *never* added implicitly by dune.
3. **Update imports** to `From Stdlib Require Import ZArith.` (etc.) —
   the rocq 9.x stdlib uses the `Stdlib` namespace, not the old `Coq`/
   `Corelib` prefix for stdlib modules.

## Working Configuration

```lisp
;; dune-project
(lang dune 3.21)
(using rocq 0.11)
```

```lisp
;; coq/dune
(rocq.theory
  (name Imp)
  (package axiomander)
  (theories Stdlib)
  (modules Imp Wp Pydantic ...))
```

```coq
(* .v files *)
From Stdlib Require Import ZArith String List Bool.
From Stdlib Require Import micromega.Lia.
Import ListNotations.
```
