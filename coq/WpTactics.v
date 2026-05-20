Require Import ZArith String List Lia.
Require Import Imp Wp.
Import ListNotations.
Open Scope Z_scope.

(** * WP Proof Automation — Level 1 (Ltac)

    Reduces WP goals to simple arithmetic forms that can be
    dispatched by [lia], [reflexivity], or sent to the SMT hammer. *)

(** [wp_reduce] — unfold state, aeval, beval, asZ; simplify. *)

Ltac wp_reduce :=
  unfold wp, aeval, beval, asZ, asString, asFloat; cbn -[In clobber].

(** Frame condition lemmas for CCall writes enforcement. *)
Lemma upd_unchanged : forall s x y v, x <> y -> lget (upd s y v) x = lget s x.
Proof.
  intros s x y v H.
  unfold upd. apply lupd_ne. auto.
Qed.

Lemma clobber_nil : forall s, clobber s nil = s.
Proof.
  intros s. unfold clobber. reflexivity.
Qed.

Lemma clobber_unchanged : forall (s : state) (vars : list var) (x : var), ~ In x vars -> lget (clobber s vars) x = lget s x.
Proof.
  intros s vars. revert s.
  induction vars as [|v vars IH]; intros s x H; simpl.
  - auto.
  - destruct (string_dec x v) as [Heq|Hne].
    + exfalso. apply H. left. auto.
    + rewrite IH.
      * apply upd_unchanged. auto.
       * intro. apply H. right. auto.
Qed.

Lemma clobber_in : forall writes st x,
  In x writes -> lget (clobber st writes) x = VZ 0.
Proof.
  induction writes as [|w ws IH]; simpl; intros st x Hin.
  - inversion Hin.
  - destruct Hin as [Hx|Hin'].
    + subst x. destruct (in_dec string_dec w ws).
      * apply (IH (lupd st w (VZ 0)) w). auto.
      * rewrite clobber_unchanged by auto. apply lupd_eq.
    + destruct (in_dec string_dec w ws).
      * apply (IH (lupd st w (VZ 0)) x). auto.
      * apply (IH (lupd st w (VZ 0)) x). auto.
Qed.

(** Commute [upd] past [clobber] when the updated variable is not in writes.
    This normalises deeply-nested CCall states so [wp_ccall_frame] can match. *)
Lemma clobber_upd_commute : forall writes st x v,
  ~ In x writes ->
  lupd (clobber st writes) x v = clobber (lupd st x v) writes.
Proof.
  induction writes as [|w ws IH]; simpl; intros st x v Hnotin; auto.
  assert (Hx : x <> w).
  { intro Heq. apply Hnotin. left. auto. }
  assert (Hnotin_ws : ~ In x ws).
  { intro Hin. apply Hnotin. right. auto. }
  rewrite IH with (st := lupd st w (VZ 0)).
  - rewrite lupd_swap; auto.
  - auto.
Qed.

(** Single lemma for the CCall frame conjunct — avoids fragile Ltac pattern matching. *)
Lemma wp_ccall_frame : forall (s : state) (target : var) (writes : list var) (r : Z) (x : var),
  ~ In x (target :: writes) -> lget s x = lget (clobber (lupd s target (VZ r)) writes) x.
Proof.
  intros s target writes r x Hnotin.
  destruct (string_dec x target) as [Heq|Hne].
  - exfalso. apply Hnotin. left. auto.
  - rewrite clobber_unchanged.
    + symmetry. apply lupd_ne. auto.
    + intro Hin. apply Hnotin. right. auto.
Qed.

(** Prevent [simpl] from eliminating [In] — the frame pattern matches it. *)
Opaque In.

Ltac frame_prove_target :=
  intro x; intro Hin;
  match goal with
  | [ Hin : ~ In ?x0 (?t :: ?w) |- _ = clobber (upd _ ?t (VZ _)) ?w ?x0 ] =>
      destruct (string_dec x0 t);
      [ exfalso; apply Hin; unfold In; left; auto
      | rewrite clobber_unchanged; [ rewrite upd_unchanged; [ reflexivity | auto ] | intro; apply Hin; unfold In; right; auto ] ]
  | [ Hin : ~ In ?x0 (?t :: ?w) |- _ ] =>
      destruct (string_dec x0 t);
      [ exfalso; apply Hin; unfold In; left; auto
      | rewrite clobber_unchanged; [ rewrite upd_unchanged; [ reflexivity | auto ] | intro; apply Hin; unfold In; right; auto ] ]
  | [ Hin : ~ (?t = ?x0 \/ _) |- _ = (upd _ ?t (VZ _)) ?x0 ] =>
      destruct (string_dec x0 t);
      [ exfalso; apply Hin; left; auto
      | rewrite upd_unchanged; [ reflexivity | auto ] ]
  | [ Hin : ~ (?t = ?x0 \/ _) |- _ ] =>
      destruct (string_dec x0 t);
      [ exfalso; apply Hin; left; auto
      | rewrite upd_unchanged; [ reflexivity | auto ] ]
  | _ => idtac "frame_prove: no match"
  end.

(** [wp_prove] — structural recursion over goal shape after wp_reduce.
    Handles conjunctions, disjunctions, ABool, comparisons, reflexivity, lia. *)
Ltac wp_prove :=
  wp_reduce;
  match goal with
  | [ H: false = true |- _ ] => discriminate
  | [ H: true = false |- _ ] => discriminate
  | [ H: Z.leb ?a ?b = true |- _ ] => apply Z.leb_le in H; wp_prove
  | [ H: Z.leb ?a ?b = false |- _ ] => apply Z.leb_gt in H; wp_prove
  | [ H: Z.eqb ?a ?b = true |- _ ] => apply Z.eqb_eq in H; subst; wp_prove
  | [ H: Z.eqb ?a ?b = false |- _ ] => apply Z.eqb_neq in H; wp_prove
  | |- _ /\ _ => split; wp_prove
  | |- _ -> _ => intro; wp_prove
  | |- forall _, ~ In _ (_ :: _) -> _ = clobber (upd _ _ (VZ _)) _ _ => apply wp_ccall_frame
  | |- forall _, _ => intro; wp_prove
  | |- exists _, _ => eexists; wp_prove
  | |- (if ?c then _ else _) = 1 \/ (if ?c then _ else _) = 0 =>
      destruct c; auto
  | |- _ \/ _ => solve [left; wp_prove | right; wp_prove]
  | |- ?x = ?x => reflexivity
  | |- context[clobber ?s nil] => rewrite (clobber_nil s); wp_prove
  | |- _ => solve [lia | reflexivity | auto]
  end.

(** [vcg_exit] — proves the while-exit verification condition.
    The goal is: vcg_while_exit b inv Q
    = forall s, inv s -> beval b s = false -> Q s
    Unfolds definitions and dispatches arithmetic to lia. *)
Ltac vcg_exit :=
  unfold vcg_while_exit, beval, upd; simpl;
  repeat rewrite eqb_refl; simpl;
  intros; repeat (match goal with [H: _ /\ _ |- _] => destruct H end);
  match goal with [H: Z.leb _ _ = false |- _] => apply Z.leb_gt in H end;
  lia.

(** * Example 1: assignment — one tactic *)
Theorem add_auto : forall (a b : Z),
  True ->
  wp (CAss "r"%string (APlus (AVar "a"%string) (AVar "b"%string)))
     (fun s => asZ (s "r"%string) = (a + b)%Z)
     (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof. intros. wp_prove. Qed.

(** * Example 2: conditional — [split] then [lia] *)
Theorem max_auto : forall (a b : Z),
  0 <= a -> 0 <= b ->
  wp (CIf (BLe (AVar "b"%string) (AVar "a"%string))
          (CAss "r"%string (AVar "a"%string))
          (CAss "r"%string (AVar "b"%string)))
     (fun s => a <= asZ (s "r"%string) /\ b <= asZ (s "r"%string))
     (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof.
  intros.
  wp_reduce.
  split; [ intro Hleb; apply Z.leb_le in Hleb; wp_prove; split; lia
         | intro Hleb; apply Z.leb_gt in Hleb; wp_prove; split; lia ].
Qed.

(** * Example 3: black hole with havoc *)
Theorem a_unchanged_auto : forall (a b : Z),
  wp (CSeq
       (CAss "x"%string (APlus (AVar "a"%string) (AVar "b"%string)))
       (CHavoc ["x"%string]))
     (fun s => asZ (lget s "a"%string) = a)
     (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof. Admitted.

(** * Pipeline Integration

    After [wp_reduce], goals are either:
    - Closed (reflexivity, lia) → Level 1 succeeded
    - Simple arithmetic → Level 2: coq-hammer / SMT
    - Complex (invariants, quantifiers) → Level 3: LLM oracle

    The automation doesn't replace the pipeline — it's the first filter.
    What [wp_reduce] can't close, the SMT hammer tries next.
    What the hammer can't close, the LLM oracle generates a proof for. *)
