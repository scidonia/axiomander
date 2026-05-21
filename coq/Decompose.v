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
