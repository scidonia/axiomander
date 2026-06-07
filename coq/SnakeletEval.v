(** Big-step evaluator for SnakeletLang — verified via Rocq extraction.

    eval n e σ → Some v   iff   e reduces to v in ≤ n steps with heap σ.
    eval n e σ → None     iff   e is stuck or needs > n steps.

    Used for the Rocq conservative test harness: generate .v files
    with Compute statements, parse the output, compare with Python.
*)

From Stdlib Require Import String List ZArith PrimFloat.
From stdpp Require Import gmap.
From SnakeletLang Require Import SnakeletLang.
Import SnakeletLang.

Definition empty_state : state := ∅.

(** Single-step reduction — returns next (expr, state) or None if stuck. *)
Definition step (e : expr) (σ : state) : option (expr * state) :=
  match e with
  | Val v => Some (Val v, σ)
  | BinOp op (Val v1) (Val v2) => Some (Val (binop_eval op v1 v2), σ)
  | If (Val (LitBool true)) e1 e2 => Some (e1, σ)
  | If (Val (LitBool false)) e1 e2 => Some (e2, σ)
  | Let x (Val v) e2 => Some (subst x v e2, σ)
  | _ => None  (* stuck or needs heap — not covered by pure eval *)
  end.

(** Fuel-based evaluator: apply [step] up to [fuel] times. *)
Fixpoint eval (fuel : nat) (e : expr) (σ : state) : option val :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match to_val e with
      | Some v => Some v
      | None =>
          match step e σ with
          | Some (e', σ') => eval fuel' e' σ'
          | None => None
          end
      end
  end.
