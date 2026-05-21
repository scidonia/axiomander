Require Import ZArith String List Lia. Import ListNotations. Open Scope Z_scope.
(* Auto-generated from frame_two_calls *)
(* line 8: [precondition] (a >= 0) *)
(* line 8: [precondition] (b >= 0) *)
(* line 12: [general] (asZ (s "a"%string) = asZ (s "old_a"%string)) *)
(* line 12: [general] (asZ (s "b"%string) = asZ (s "old_b"%string)) *)
(* line 14: [postcondition] (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)) *)

From Hammer Require Import Hammer.

Require Import ZArith String List Lia.
Require Import Imp Wp Pydantic WpTactics.
Import ListNotations.
Open Scope Z_scope.


Definition frame_two_calls_body : com :=
  (CSeq (CSeq (CSeq (CIf (BNot (BEq (AVar "__debug__"%string) (ANum 0))) (CSeq (CAss "old_a"%string (AVar "a"%string)) (CAss "old_b"%string (AVar "b"%string))) CSkip) (CSeq (CAss "x"%string (AVar "a"%string)) (CCall "inc"%string ((AVar "a"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "a2"%string) = (asZ (s "x"%string) + 1))) nil "a2"%string))) (CSeq (CAss "x"%string (AVar "b"%string)) (CCall "inc"%string ((AVar "b"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "b2"%string) = (asZ (s "x"%string) + 1))) nil "b2"%string))) (CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string)))).

Lemma inc_frame_a : forall (s : state) (r : Z),
  ~ In "a"%string ("a2"%string :: nil) ->
  lget s "a"%string = lget (clobber (lupd s "a2"%string (VZ r)) nil) "a"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "a2"%string nil r "a"%string).
  assumption.
Qed.

Lemma inc_frame_b : forall (s : state) (r : Z),
  ~ In "b"%string ("a2"%string :: nil) ->
  lget s "b"%string = lget (clobber (lupd s "a2"%string (VZ r)) nil) "b"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "a2"%string nil r "b"%string).
  assumption.
Qed.

Lemma inc_frame_old_a : forall (s : state) (r : Z),
  ~ In "old_a"%string ("a2"%string :: nil) ->
  lget s "old_a"%string = lget (clobber (lupd s "a2"%string (VZ r)) nil) "old_a"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "a2"%string nil r "old_a"%string).
  assumption.
Qed.

Lemma inc_frame_old_b : forall (s : state) (r : Z),
  ~ In "old_b"%string ("a2"%string :: nil) ->
  lget s "old_b"%string = lget (clobber (lupd s "a2"%string (VZ r)) nil) "old_b"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "a2"%string nil r "old_b"%string).
  assumption.
Qed.


Theorem frame_two_calls_correct : forall (a : Z) (b : Z), 
(exists (old_a : Z), ((old_a = a) /\
   (exists (old_b : Z), ((old_b = b) /\
     (((a >= 0) /\ (b >= 0)) ->
   wp frame_two_calls_body
      (fun s => (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)))
      ((upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b)))))))).
Proof.
    intros.
  exists a.
  split.
  - reflexivity.
  - 
  exists b.
  split.
  -- reflexivity.
  -- 

  wp_prove.
Qed.
