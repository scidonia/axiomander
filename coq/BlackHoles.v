Require Import ZArith String List Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

(** * Black Hole Examples (Axiomander-style)

    Three theorems demonstrating the black hole theory:
    1. Unaffected properties survive a havoc
    2. Affected properties are lost across a havoc
    3. Re-asserting dropped properties restores verification *)

(** Shared definitions *)
Definition compute_and_havoc : com :=
  CSeq
    (CAss "x"%string (APlus (AVar "a"%string) (AVar "b"%string)))
    (CHavoc ["x"%string]).

Definition init_state_ab (a b : Z) : state :=
  updZ (updZ empty_state "a"%string a) "b"%string b.

(** * Theorem 1: Unaffected property survives a black hole *)
Theorem a_unchanged : forall (a b : Z),
  wp compute_and_havoc
     (fun s => asZ (s "a"%string) = a)
     (init_state_ab a b).
Proof.
  intros a b.
  unfold compute_and_havoc, init_state_ab, updZ.
  wp_reduce.
  intros s' Hagree.
  destruct (string_dec "a"%string "x"%string) as [Heq|Hne].
  - discriminate Heq.
  - assert (Hnotin : ~ In "a"%string ["x"%string]).
    { simpl. intro H. destruct H as [H' | []]. apply Hne. symmetry. exact H'. }
    apply Hagree in Hnotin.
    simpl in Hnotin.
    rewrite Hnotin. reflexivity.
Qed.

(** * Theorem 2: Affected property is lost across a black hole *)
Theorem x_lost : forall (a b : Z),
  a + b <> 0 ->
  ~ (wp compute_and_havoc
       (fun s => asZ (s "x"%string) = a + b)
       (init_state_ab a b)).
Proof.
  intros a b Hsum.
  unfold compute_and_havoc, wp, init_state_ab, updZ. simpl.
  intro H.
  set (S := upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b)).
  set (S' := upd S "x"%string (VZ (a + b))).
  set (s_bad := upd S "x"%string (VZ 0)).
  assert (Hagree : forall x0, ~ In x0 ["x"%string] -> s_bad x0 = S' x0).
  { intros x0 Hx0. unfold s_bad, S', S.
    assert (Hneq : "x"%string <> x0).
    { intro Heq. apply Hx0. rewrite Heq. left. reflexivity. }
    rewrite (upd_ne (upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b)) "x"%string x0 (VZ 0) Hneq).
    rewrite (upd_ne (upd (upd empty_state "a"%string (VZ a)) "b"%string (VZ b)) "x"%string x0 (VZ (a + b)) Hneq).
    reflexivity. }
  apply H in Hagree.
  unfold s_bad, S in Hagree.
  rewrite upd_eq in Hagree.
  apply Hsum. symmetry. exact Hagree.
Qed.

(** * Theorem 3: Re-asserting the dropped property restores verification *)
Theorem recovery : forall (a b : Z),
  let body := CSeq compute_and_havoc
                    (CAss "x"%string (APlus (AVar "a"%string) (AVar "b"%string))) in
  wp body (fun s => asZ (s "x"%string) = a + b) (init_state_ab a b).
Proof.
  intros a b body.
  unfold body, compute_and_havoc, init_state_ab, updZ.
  wp_reduce.
  intros s' Hagree.
  assert (Hnota : ~ In "a"%string ["x"%string]).
  { simpl. intro H. destruct H as [H' | []]. discriminate H'. }
  assert (Hnotb : ~ In "b"%string ["x"%string]).
  { simpl. intro H. destruct H as [H' | []]. discriminate H'. }
  apply Hagree in Hnota.
  apply Hagree in Hnotb.
  simpl in Hnota, Hnotb.
  rewrite Hnota, Hnotb.
  unfold upd. rewrite !String.eqb_refl. simpl.
  reflexivity.
Qed.
