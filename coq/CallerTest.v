From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

Definition square_body : com :=
  CAss "result"%string (AMult (AVar "x"%string) (AVar "x"%string)).

Definition caller_body : com :=
  (CSeq (CSeq (CAss "x"%string (AVar "n"%string)) (CCall "square"%string ((AVar "n"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "total"%string) >= asZ (s "x"%string))) nil "total"%string)) (CAss "result"%string (AVar "total"%string))).

Theorem caller_correct : forall (n : Z),
  n >= 0 ->
  wp caller_body (fun s => asZ (s "total"%string) >= asZ (s "n"%string)) (updZ empty_state "n"%string n).
Proof.
  intros.
  wp_prove.
Qed.
