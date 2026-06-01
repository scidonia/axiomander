From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

Definition inc_body : com :=
  CAss "result"%string (APlus (AVar "amount"%string) (ANum 1)).

Definition caller_ok_body : com :=
  (CSeq (CAss "amount"%string (AVar "n"%string)) (CCall "inc"%string ((AVar "n"%string) :: nil) (fun s => ((asZ (s "amount"%string) >= 0) /\ isVZ (s "amount"%string) = true)) (fun s => (asZ (s "result"%string) >= 0)) nil "result"%string)).

Theorem caller_ok_correct : forall (n : Z),
  n >= 0 ->
  wp caller_ok_body (wp_normal (fun s => asZ (s "result"%string) >= 0)) (updZ empty_state "n"%string n).
Proof.
  intros.
  wp_prove.
Qed.
