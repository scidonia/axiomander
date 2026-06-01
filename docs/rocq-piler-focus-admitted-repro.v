(* Auto-generated from ftc12 -- per-obligation mode *)
(* line 9: [precondition] (a >= 0) *)
(* line 9: [precondition] (b >= 0) *)
(* line 13: [general] (asZ (s "a"%string) = old_a) *)
(* line 14: [general] (asZ (s "b"%string) = old_b) *)
(* line 16: [postcondition] (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)) *)

From Hammer Require Import Hammer Tactics.

Require Import ZArith String List Lia.
Require Import Imp Wp Pydantic WpTactics.
Import ListNotations.
Open Scope Z_scope.


Definition ftc12_body : com :=
  (CSeq (CSeq (CSeq (CIf BTrue (CSeq (CAss "old_a"%string (AVar "a"%string)) (CAss "old_b"%string (AVar "b"%string))) CSkip) (CSeq (CAss "x"%string (AVar "a"%string)) (CCall "inc12"%string ((AVar "a"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "a2"%string) = (asZ (s "x"%string) + 1))) nil "a2"%string))) (CSeq (CAss "x"%string (AVar "b"%string)) (CCall "inc12"%string ((AVar "b"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "b2"%string) = (asZ (s "x"%string) + 1))) nil "b2"%string))) (CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string)))).

(* Suggested staged proof strategy:
   - use wp_seq_decompose to split each CSeq stage
   - apply stage lemmas: ftc12_stage_1_correct, ftc12_stage_2_correct
   - finish with post lemma: ftc12_post
   - if stuck, focus on one stage theorem at a time before the main theorem
*)


Definition s1 : com := (CSeq (CAss "x"%string (AVar "a"%string)) (CCall "inc12"%string ((AVar "a"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "a2"%string) = (asZ (s "x"%string) + 1))) nil "a2"%string)).
Definition s2 : com := (CSeq (CAss "x"%string (AVar "b"%string)) (CCall "inc12"%string ((AVar "b"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "b2"%string) = (asZ (s "x"%string) + 1))) nil "b2"%string)).

Definition Q_ftc12_1 (a b old_a old_b : Z) : assertion :=
  fun s => ((a >= 0) /\ (b >= 0)) /\ (asZ (s "a2"%string) = (a + 1)) /\ (isVZ (s "a2"%string) = true) /\ (asZ (s "a"%string) = a) /\ (isVZ (s "a"%string) = true) /\ (asZ (s "b"%string) = b) /\ (isVZ (s "b"%string) = true) /\ (asZ (s "old_a"%string) = a) /\ (isVZ (s "old_a"%string) = true) /\ (asZ (s "old_b"%string) = b) /\ (isVZ (s "old_b"%string) = true).

Definition Q_ftc12_2 (a b old_a old_b : Z) : assertion :=
  fun s => ((a >= 0) /\ (b >= 0)) /\ (asZ (s "b2"%string) = (b + 1)) /\ (isVZ (s "b2"%string) = true) /\ (asZ (s "a2"%string) = (a + 1)) /\ (isVZ (s "a2"%string) = true) /\ (asZ (s "a"%string) = a) /\ (isVZ (s "a"%string) = true) /\ (asZ (s "b"%string) = b) /\ (isVZ (s "b"%string) = true) /\ (asZ (s "old_a"%string) = a) /\ (isVZ (s "old_a"%string) = true) /\ (asZ (s "old_b"%string) = b) /\ (isVZ (s "old_b"%string) = true).


Lemma inc12_frame_a_a2 : forall (s : state) (r : Z),
  ~ In "a"%string ("a2"%string :: nil) ->
  lget s "a"%string = lget (clobber (lupd s "a2"%string (VZ r)) nil) "a"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "a2"%string nil r "a"%string).
  assumption.
Qed.

Lemma inc12_frame_b_a2 : forall (s : state) (r : Z),
  ~ In "b"%string ("a2"%string :: nil) ->
  lget s "b"%string = lget (clobber (lupd s "a2"%string (VZ r)) nil) "b"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "a2"%string nil r "b"%string).
  assumption.
Qed.

Lemma inc12_frame_old_a_a2 : forall (s : state) (r : Z),
  ~ In "old_a"%string ("a2"%string :: nil) ->
  lget s "old_a"%string = lget (clobber (lupd s "a2"%string (VZ r)) nil) "old_a"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "a2"%string nil r "old_a"%string).
  assumption.
Qed.

Lemma inc12_frame_old_b_a2 : forall (s : state) (r : Z),
  ~ In "old_b"%string ("a2"%string :: nil) ->
  lget s "old_b"%string = lget (clobber (lupd s "a2"%string (VZ r)) nil) "old_b"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "a2"%string nil r "old_b"%string).
  assumption.
Qed.

Lemma inc12_frame_a_b2 : forall (s : state) (r : Z),
  ~ In "a"%string ("b2"%string :: nil) ->
  lget s "a"%string = lget (clobber (lupd s "b2"%string (VZ r)) nil) "a"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "b2"%string nil r "a"%string).
  assumption.
Qed.

Lemma inc12_frame_b_b2 : forall (s : state) (r : Z),
  ~ In "b"%string ("b2"%string :: nil) ->
  lget s "b"%string = lget (clobber (lupd s "b2"%string (VZ r)) nil) "b"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "b2"%string nil r "b"%string).
  assumption.
Qed.

Lemma inc12_frame_old_a_b2 : forall (s : state) (r : Z),
  ~ In "old_a"%string ("b2"%string :: nil) ->
  lget s "old_a"%string = lget (clobber (lupd s "b2"%string (VZ r)) nil) "old_a"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "b2"%string nil r "old_a"%string).
  assumption.
Qed.

Lemma inc12_frame_old_b_b2 : forall (s : state) (r : Z),
  ~ In "old_b"%string ("b2"%string :: nil) ->
  lget s "old_b"%string = lget (clobber (lupd s "b2"%string (VZ r)) nil) "old_b"%string.
Proof.
  intros s r H.
  apply (wp_ccall_frame s "b2"%string nil r "old_b"%string).
  assumption.
Qed.


Lemma ftc12_stage_1_correct : forall (a : Z) (b : Z) (old_a : Z) (old_b : Z),
  (a >= 0) /\ (b >= 0) ->
  wp s1
     (Q_ftc12_1 a b old_a old_b)
     ((upd (upd (upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b)) "old_a"%string (VZ a)) "old_b"%string (VZ b))).
Proof.
  intros a b old_a old_b Hpre.
  destruct Hpre as [H0 H1].
  wp_reduce. solve [sauto | hammer].
Qed.

Lemma ftc12_stage_2_correct : forall (a : Z) (b : Z) (old_a : Z) (old_b : Z) (s : state),
  (b >= 0)%Z ->
  ((a >= 0) /\ (b >= 0)) ->
  (asZ (s "a2"%string) = (a + 1)) ->
  (isVZ (s "a2"%string) = true) ->
  (asZ (s "a"%string) = a) ->
  (isVZ (s "a"%string) = true) ->
  (asZ (s "b"%string) = b) ->
  (isVZ (s "b"%string) = true) ->
  (asZ (s "old_a"%string) = old_a) ->
  (isVZ (s "old_a"%string) = true) ->
  (asZ (s "old_b"%string) = old_b) ->
  (isVZ (s "old_b"%string) = true) ->
  wp s2
     (Q_ftc12_2 a b old_a old_b)
     s.
Proof.
Admitted.


Lemma ftc12_post : forall (a : Z) (b : Z) (old_a : Z) (old_b : Z) (s : state),
  wp (CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string)))
     (fun s => (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)))
     s.
Proof.
Admitted.


Theorem ftc12_correct : forall (a : Z) (b : Z),
  (exists (old_a : Z), ((old_a = a) /\
  (exists (old_b : Z), ((old_b = b) /\  (((a >= 0) /\ (b >= 0)) ->
  wp (CSeq s1 (CSeq s2 (CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string)))))
     (fun s => (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)))
     ((upd (upd (upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b)) "old_a"%string (VZ a)) "old_b"%string (VZ b)))))))
Proof.
Admitted.


