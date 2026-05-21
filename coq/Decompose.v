Require Import ZArith String List Lia. Import ListNotations. Open Scope Z_scope.
Require Import Imp Wp Pydantic WpTactics.

Lemma wp_monotone : forall c (Q1 Q2 : assertion) s,
  wp c Q1 s ->
  (forall s', Q1 s' -> Q2 s') ->
  wp c Q2 s.
Proof.
  induction c; intros Q1 Q2 s Hwp Himpl.
  - (* CSkip *) simpl in *; auto.
  - (* CAss *) simpl in *; auto.
  - (* CSeq *) simpl in *.
    eapply IHc1.
    + exact Hwp.
    + intros s' H. eapply IHc2; eassumption.
  - (* CIf *) simpl in *.
    destruct Hwp as [Ht Hf]; split.
    + intro H; eapply IHc1; eauto.
    + intro H; eapply IHc2; eauto.
  - (* CWhile *) simpl in *; assumption.
  - (* CHavoc *) simpl in *.
    intros s' H; apply Himpl; apply Hwp; auto.
  - (* CListNew *) simpl in *; auto.
  - (* CListAppend *) simpl in *; auto.
  - (* CListPop *) simpl in *; auto.
  - (* CListSet *) simpl in *; auto.
  - (* CDictSet *) simpl in *; auto.
  - (* CDictGet *) simpl in *; auto.
  - (* CDictEnsureList *) simpl in *; auto.
  - (* CDictAppend *) simpl in *; auto.
  - (* CDictAppendKv *) simpl in *; auto.
  - (* CCall *) simpl in *.
    destruct Hwp as [Hpre Hrest]; split; [assumption|].
    intros r Hp; destruct (Hrest r Hp); split; [apply Himpl|]; assumption.
  - (* CAssume *) simpl in *.
    intro; apply Himpl; apply Hwp; assumption.
Qed.

Lemma wp_seq_decompose : forall c1 c2 (Q1 Q2 : assertion) s,
  wp c1 Q1 s ->
  (forall s', Q1 s' -> wp c2 Q2 s') ->
  wp (CSeq c1 c2) Q2 s.
Proof.
  intros; unfold wp; simpl.
  apply (wp_monotone c1 Q1 (wp c2 Q2) s H); auto.
Qed.

(** ** Full decomposition of frame_two_calls using wp_seq_decompose *)

(* Each stage gets its own intermediate assertion *)

Definition Q_ghost (a b : Z) : assertion :=
  fun s => (asZ (s "old_a"%string) = a)
        /\ (asZ (s "old_b"%string) = b)
        /\ (asZ (s "a"%string) = a)
        /\ (asZ (s "b"%string) = b).

Definition Q_after_inc_a (a b : Z) : assertion :=
  fun s => (* a2 = a+1 *) (asZ (s "a2"%string) = (a + 1)%Z)
        /\ (* a unchanged *) (asZ (s "a"%string) = a)
        /\ (* b unchanged *) (asZ (s "b"%string) = b).

Definition Q_after_inc_b (a b : Z) : assertion :=
  fun s => (* b2 = b+1 *) (asZ (s "b2"%string) = (b + 1)%Z)
        /\ (* a2 retains a+1 *) (asZ (s "a2"%string) = (a + 1)%Z)
        /\ (* a unchanged *) (asZ (s "a"%string) = a)
        /\ (* b unchanged *) (asZ (s "b"%string) = b).

Definition Q_final (a b : Z) : assertion :=
  fun s => (asZ (s "result"%string) = ((asZ (s "a"%string) + asZ (s "b"%string)) + 2)%Z)
        /\ (asZ (s "a"%string) = a)
        /\ (asZ (s "b"%string) = b).

(* Sub-computations — each handles one logical stage *)

Definition ghost_init : com :=
  CSeq (CAss "old_a"%string (AVar "a"%string))
       (CAss "old_b"%string (AVar "b"%string)).

Definition call_inc_a : com :=
  CSeq (CAss "x"%string (AVar "a"%string))
       (CCall "inc"%string ((AVar "a"%string) :: nil)
         (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true))
         (fun s => (asZ (s "a2"%string) = (asZ (s "x"%string) + 1)))
         nil "a2"%string).

Definition call_inc_b : com :=
  CSeq (CAss "x"%string (AVar "b"%string))
       (CCall "inc"%string ((AVar "b"%string) :: nil)
         (fun s => ((asZ (s "x"%string) >= 0) /\ isVZ (s "x"%string) = true))
         (fun s => (asZ (s "b2"%string) = (asZ (s "x"%string) + 1)))
         nil "b2"%string).

Definition assign_result : com :=
  CAss "result"%string (APlus (AVar "a2"%string) (AVar "b2"%string)).

(** The decomposed theorem — each stage is an independent wp_prove call (~0.1s each) *)

Theorem frame_two_calls_decomposed : forall a b,
  (a >= 0)%Z -> (b >= 0)%Z ->
  wp (CSeq (CSeq (CSeq ghost_init call_inc_a) call_inc_b) assign_result)
     (Q_final a b)
     ((upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b))).
Proof.
  intros a b Ha Hb.

  (* Stage 1: ghost init → Q_ghost *)
  (* Stage 1: ghost init → Q_ghost *)
  assert (H_stage1 : wp ghost_init (Q_ghost a b)
      ((upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b)))).
  { wp_reduce. unfold Q_ghost. vm_compute; auto. }
  apply (wp_seq_decompose ghost_init (CSeq (CSeq call_inc_a call_inc_b) assign_result)
                          (Q_ghost a b) (Q_final a b) _ H_stage1).
   intros s' [Hold_a [Hold_b [Ha_eq Hb_eq]]].

    (* Stage 2: inc(a) → Q_after_inc_a *)
    Time assert (H_stage2 : wp call_inc_a (Q_after_inc_a a b) s').
    { wp_reduce.
      unfold lget, upd, updZ; cbn.
      rewrite Ha_eq, Hb_eq.
      split; [split; [lia | reflexivity] | idtac].
      intro r1. intro Hr1. split.
      { unfold Q_after_inc_a; cbn. rewrite Hr1. split; [reflexivity | split; reflexivity]. }
      { apply wp_ccall_frame. simpl. intro. contradiction. } }
    apply (wp_seq_decompose call_inc_a (CSeq call_inc_b assign_result)
                            (Q_after_inc_a a b) (Q_final a b) _ H_stage2).
    intros s'' [H_a2_val [H_a2_pres H_b2_pres]].

    (* Stage 3: inc(b) → Q_after_inc_b *)
    Time assert (H_stage3 : wp call_inc_b (Q_after_inc_b a b) s'').
    { wp_reduce.
      unfold lget, upd, updZ; cbn.
      rewrite H_b2_pres, H_a2_val, H_a2_pres.
      split; [split; [lia | reflexivity] | idtac].
      intro r2. intro Hr2. split.
      { unfold Q_after_inc_b, Q_after_inc_a; cbn.
        rewrite Hr2. split; [reflexivity | split; [reflexivity | split; reflexivity]]. }
      { apply wp_ccall_frame. simpl. intro. contradiction. } }
    apply (wp_seq_decompose call_inc_b assign_result
                            (Q_after_inc_b a b) (Q_final a b) _ H_stage3).
    intros s''' [H_b2_val [H_a2_val2 [H_a3 H_b3]]].

    (* Stage 4: assign result → Q_final *)
    wp_reduce.
    unfold Q_final, Q_after_inc_b, Q_after_inc_a, asZ.
    unfold lget, upd, updZ; cbn.
    rewrite H_a2_val2, H_b2_val.
    split; [lia | split; reflexivity]. }
  Time Qed.
