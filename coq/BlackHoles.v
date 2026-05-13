Require Import ZArith String List Lia.
Require Import Imp Wp.
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
  upd (upd empty_state "a"%string a) "b"%string b.

(** * Theorem 1: Unaffected property survives a black hole *)
Theorem a_unchanged : forall (a b : Z),
  wp compute_and_havoc
     (fun s => s "a"%string = a)
     (init_state_ab a b).
Proof.
  intros a b.
  unfold compute_and_havoc, wp. simpl.
  intros s' Hagree.
  apply Hagree.
  simpl. destruct (string_dec "a"%string "x"%string) as [Heq|Hneq].
  - exfalso. discriminate.
  - intro H. destruct H as [H' | []]. apply Hneq. symmetry. exact H'.
Qed.

(** * Theorem 2: Affected property is lost across a black hole *)
Theorem x_lost : forall (a b : Z),
  a + b <> 0 ->
  ~ (wp compute_and_havoc
       (fun s => s "x"%string = a + b)
       (init_state_ab a b)).
Proof.
  intros a b Hsum.
  unfold compute_and_havoc, wp, init_state_ab. simpl.
  rewrite upd_eq. simpl.
  intro H.
  set (S := upd (upd empty_state "a"%string a) "b"%string b).
  set (S' := upd S "x"%string (a + b)).
  set (s_bad := upd S "x"%string 0).
  assert (Hagree : forall x0, ~ In x0 ["x"%string] -> s_bad x0 = S' x0).
  { intros x0 Hx0. unfold s_bad, S', S.
    assert (Hneq : "x"%string <> x0).
    { intro Heq. apply Hx0. rewrite Heq. left. reflexivity. }
    rewrite (upd_ne (upd (upd empty_state "a"%string a) "b"%string b) "x"%string x0 0 Hneq).
    rewrite (upd_ne (upd (upd empty_state "a"%string a) "b"%string b) "x"%string x0 (a + b) Hneq).
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
  wp body (fun s => s "x"%string = a + b) (init_state_ab a b).
Proof.
  intros a b body.
  unfold body, compute_and_havoc, wp. simpl.
  intros s' Hagree.
  simpl.
  assert (Ha : s' "a"%string = a).
  { apply Hagree. simpl. destruct (string_dec "a"%string "x"%string) as [H|H].
    - exfalso. discriminate.
    - intro H'. destruct H' as [H'' | []]. apply H. symmetry. exact H''. }
  assert (Hb : s' "b"%string = b).
  { apply Hagree. simpl. destruct (string_dec "b"%string "x"%string) as [H|H].
    - exfalso. discriminate.
    - intro H'. destruct H' as [H'' | []]. apply H. symmetry. exact H''. }
  rewrite Ha, Hb.
  reflexivity.
Qed.
