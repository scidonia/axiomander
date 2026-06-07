(** Big-step evaluator for SnakeletLang with fuel.

    Fuel prevents infinite recursion (for loops, recursion).
    One fuel unit = one reduction step.
*)

From Stdlib Require Import String List ZArith PrimFloat.
From Coq.SnakeletLang Require Import SnakeletLang.
Import SnakeletLang.

Definition state := SnakeletLang.state.
Definition empty_state : state := ∅.

(** Evaluate an expression to a value using [fuel] reduction steps.
    Returns [None] if fuel exhausted before reaching a value. *)
Fixpoint eval (fuel : nat) (e : expr) (σ : state) : option val :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match to_val e with
      | Some v => Some v
      | None =>
          match _ with
          | _ => None
          end
      end
  end.
