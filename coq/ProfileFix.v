Require Import Wp WpTactics ZArith String List Lia. Import ListNotations. Open Scope Z_scope.
Require Import Imp.

Definition frame_two_calls_body : com :=
  (CSeq (CSeq (CSeq (CIf (BNot (BEq (AVar "__debug__"%string) (ANum 0))) (CSeq (CAss "old_a"%string (AVar "a"%string)) (CAss "old_b"%string (AVar "b"%string))) CSkip) (CSeq (CAss "x"%string (AVar "a"%string)) (CCall "inc"%string ((AVar "a"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "a2"%string) = (asZ (s "x"%string) + 1))) nil "a2"%string))) (CSeq (CAss "x"%string (AVar "b"%string)) (CCall "inc"%string ((AVar "b"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "b2"%string) = (asZ (s "x"%string) + 1))) nil "b2"%string))) (CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string)))).

Theorem test : forall a b : Z, (a>=0) /\ (b>=0) -> wp frame_two_calls_body (fun _ => True) ((upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b))).
Proof.
  intros a b [Ha Hb].
  Time wp_reduce.
Time Qed.split.

