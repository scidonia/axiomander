Require Import ZArith String List Lia.
Require Import Imp Wp.
Import ListNotations.
Open Scope Z_scope.

(** * WP Proof Automation — Level 1 (Ltac)

    Reduces WP goals to simple arithmetic forms that can be
    dispatched by [lia], [reflexivity], or sent to the SMT hammer. *)

(** [wp_True] — any command satisfies WP with postcondition True. *)
Lemma wp_True : forall c s, wp c (fun _ => True) s.
Admitted.

(** [wp_reduce] — unfold state, aeval, beval, asZ; simplify. *)
Ltac wp_reduce :=
  unfold wp, aeval, beval, asZ, asString, asFloat; cbn.

(** Frame condition lemmas for CCall writes enforcement. *)
Lemma upd_unchanged : forall s x y v, x <> y -> upd s y v x = s x.
Proof.
  intros s x y v H.
  unfold upd; cbn.
  destruct (String.eqb y x) eqn:Heq.
  - apply String.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

Lemma clobber_nil : forall s, clobber s nil = s.
Proof.
  intros s. unfold clobber. reflexivity.
Qed.

Lemma clobber_unchanged : forall (s : state) (vars : list var) (x : var), ~ In x vars -> clobber s vars x = s x.
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

Ltac frame_prove_target :=
  intro x; intro Hnotin;
  match goal with
  | [ Hnotin : ~ (In ?x (?t :: ?w)) |- ?sx = clobber (upd ?s ?t (VZ ?r)) ?w ?x ] =>
      destruct (string_dec x t);
      [ exfalso; apply Hnotin; simpl; auto
      | rewrite clobber_unchanged; [ rewrite upd_unchanged; [ reflexivity | auto ] | intro; apply Hnotin; right; auto ] ]
  | [ Hnotin : ~ (?t = ?x \/ _) |- ?sx = (upd ?s ?t (VZ ?r)) ?x ] =>
      destruct (string_dec x t);
      [ exfalso; apply Hnotin; left; auto
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
  | |- forall _, _ => intro; wp_prove
  | |- exists _, _ => eexists; wp_prove
  | |- (if ?c then _ else _) = 1 \/ (if ?c then _ else _) = 0 =>
      destruct c; auto
  | |- _ \/ _ => first [left; wp_prove | right; wp_prove]
  | |- ?x = ?x => reflexivity
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
     (fun s => asZ (s "a"%string) = a)
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
