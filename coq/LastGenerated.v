(* Auto-generated from caller_ok *)
(* line 7: [precondition] (n >= 0) *)
(* line 9: [postcondition] (asZ (s "result"%string) >= 0) *)

From Hammer Require Import Hammer.

From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp Pydantic WpTactics.
Import ListNotations.
Open Scope Z_scope.


Definition caller_ok_body : com :=
  (CSeq (CAss "amount"%string (AVar "n"%string)) (CCall "inc"%string ((AVar "n"%string) :: nil) (fun s => ((asZ (s "amount"%string) >= 0) /\ isVZ (s "amount"%string) = true)) (fun s => (asZ (s "result"%string) >= 0)) nil "result"%string)).

Theorem caller_ok_correct : forall (n : Z), 
  (((n >= 0)) ->
  wp caller_ok_body
     (fun s => (asZ (s "result"%string) >= 0))
     ((upd empty_state "n"%string (VZ n)))).
Proof.
    intros.
  wp_prove.
Qed.
