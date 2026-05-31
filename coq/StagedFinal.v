From Stdlib Require Import ZArith String List micromega.Lia. Import ListNotations. Open Scope Z_scope.
Require Import Imp Wp Pydantic WpTactics.

Definition s1 := (CSeq (CAss "x"%string (AVar "a"%string)) (CCall "inc"%string ((AVar "a"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "a2"%string) = (asZ (s "x"%string) + 1))) nil "a2"%string)).
Definition s2 := (CSeq (CAss "x"%string (AVar "b"%string)) (CCall "inc"%string ((AVar "b"%string) :: nil) (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true)) (fun s => (asZ (s "b2"%string) = (asZ (s "x"%string) + 1))) nil "b2"%string)).

Definition Q1 (a b : Z) : assertion :=
  fun s => (asZ (s "a2"%string) = (a + 1)%Z) /\ (isVZ (s "a2"%string) = true)
        /\ (asZ (s "a"%string) = a) /\ (isVZ (s "a"%string) = true)
        /\ (asZ (s "b"%string) = b) /\ (isVZ (s "b"%string) = true).

Definition Q2 (a b : Z) : assertion :=
  fun s => (asZ (s "b2"%string) = (b + 1)%Z) /\ (isVZ (s "b2"%string) = true)
        /\ (asZ (s "a2"%string) = (a + 1)%Z) /\ (isVZ (s "a2"%string) = true)
        /\ (asZ (s "a"%string) = a) /\ (isVZ (s "a"%string) = true)
        /\ (asZ (s "b"%string) = b) /\ (isVZ (s "b"%string) = true).

Lemma stage_1_correct : forall (a b : Z),
  (a >= 0)%Z /\ (b >= 0)%Z ->
  wp s1 (Q1 a b) (upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b)).
Proof.
  intros a b [Ha Hb]. wp_reduce. split.
  - unfold lget, upd, updZ; cbn. split; [apply Ha | reflexivity].
  - intro r. intro Hr. split.
    + unfold Q1; cbn. rewrite Hr. repeat split; auto.
    + apply (wp_ccall_frame _ "a2"%string nil r).
Qed.

Lemma stage_2_correct : forall (a b : Z) (s : state),
  (b >= 0)%Z ->
  (asZ (s "a2"%string) = (a + 1)%Z) -> (isVZ (s "a2"%string) = true) ->
  (asZ (s "a"%string) = a) -> (isVZ (s "a"%string) = true) ->
  (asZ (s "b"%string) = b) -> (isVZ (s "b"%string) = true) ->
  wp s2 (Q2 a b) s.
Proof.
  intros a b s Hb Ha2_eq Ha2_v Ha_eq Ha_v Hb_eq Hb_v.
  wp_reduce. split.
  - unfold asZ, lget. unfold asZ in Hb_eq. rewrite Hb_eq. split; [apply Hb | assumption].
  - intro r. intro Hr. split.
    + unfold Q2; simpl. unfold lget, asZ in *.
      rewrite Hr, Ha2_eq, Ha_eq, Hb_eq. repeat split; auto.
    + apply (wp_ccall_frame _ "b2"%string nil r).
Qed.

Theorem frame_two_calls_staged : forall (a b : Z),
  (a >= 0)%Z /\ (b >= 0)%Z ->
  wp (CSeq (CSeq s1 s2) (CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string))))
     (fun s => (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)%Z))
     ((upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b))).
Proof.
  intros a b [Ha Hb].
  apply (wp_seq_decompose s1 (CSeq s2 (CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string)))) (Q1 a b) (fun s => (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)%Z)) _).
  { apply stage_1_correct. split; assumption. }
  { intros s1 Hq. unfold Q1 in Hq.
    destruct Hq as [Ha2_eq [Ha2_v [Ha_eq [Ha_v [Hb_eq Hb_v]]]]].
    apply (wp_seq_decompose s2 (CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string))) (Q2 a b) (fun s => (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)%Z)) _).
    { apply (stage_2_correct a b s1 Hb Ha2_eq Ha2_v Ha_eq Ha_v Hb_eq Hb_v). }
    { intros s2 Hq2. unfold Q2 in Hq2.
      destruct Hq2 as [Hb2_eq [Hb2_v [Ha22_eq [Ha22_v [Ha2_eq2 [Ha2_v2 [Hb2_eq2 Hb2_v2]]]]]]].
      simpl. unfold lget.
      destruct (s2 "a2"%string) as [za | | | | | | | | | |] eqn:Ea2; simpl;
        try (exfalso; simpl in Ha22_eq; lia).
      destruct (s2 "b2"%string) as [zb | | | | | | | | | |] eqn:Eb2; simpl;
        try (exfalso; simpl in Hb2_eq; lia).
      simpl in Ha22_eq, Hb2_eq, Ha2_eq2, Hb2_eq2.
      simpl. rewrite Ha22_eq, Hb2_eq, Ha2_eq2, Hb2_eq2. lia. }
  }
Qed.
