From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp.
Import ListNotations.
Open Scope Z_scope.

(** * WP Proof Automation -- Level 1 (Ltac)

    Reduces WP goals to simple arithmetic forms that can be
    dispatched by [lia], [reflexivity], or sent to the SMT hammer. *)

(** [wp_reduce] -- unfold state, aeval, beval, asZ; simplify. *)
Ltac wp_reduce :=
  unfold wp, wp_normal, aeval, beval, asZ, asString, asFloat; cbn -[In clobber lget upd updZ lupd].

(** [wp_cif_btrue] -- collapse [CIf BTrue c1 c2] WP to just [wp c1 Phi s]. *)
Lemma wp_cif_btrue : forall c1 c2 Phi s,
  wp (CIf BTrue c1 c2) Phi s <-> wp c1 Phi s.
Proof.
  intros; split; intros H.
  - unfold wp in H; simpl in H. destruct H as [Ht _]. apply Ht; reflexivity.
  - unfold wp; simpl. split; [intros; apply H | intros Hb; inversion Hb].
Qed.

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

Lemma wp_ccall_frame_lookup : forall (s : state) (target : var) (writes : list var) (r : Z) (x : var),
  ~ In x (target :: writes) -> (clobber (lupd s target (VZ r)) writes) x = s x.
Proof.
  intros s target writes r x Hnotin.
  change ((clobber (lupd s target (VZ r)) writes) x) with
    (lget (clobber (lupd s target (VZ r)) writes) x).
  change (s x) with (lget s x).
  symmetry. apply wp_ccall_frame. exact Hnotin.
Qed.

Opaque In.

Ltac frame_notin :=
  let H := fresh "Hnotin" in
  intro H; repeat (destruct H as [H | H]);
  try discriminate; contradiction.

Lemma isVZ_asZ : forall v, isVZ v = true -> v = VZ (asZ v).
Proof.
  destruct v; simpl; intros H; try discriminate; reflexivity.
Qed.

Lemma wp_ccall_decompose : forall (name : var) (args : list aexp)
    (pre post : assertion) (Phi : outcome_pred) (writes : list var) (target : var) (s : state),
  pre s ->
  (forall r, post (lupd s target (VZ r)) ->
     Phi (OReturn (clobber (lupd s target (VZ r)) writes))) ->
  (forall r x, ~ In x (target :: writes) ->
     lget s x = lget (clobber (lupd s target (VZ r)) writes) x) ->
  wp (CCall name args pre post writes target) Phi s.
Proof.
  intros name args pre post Phi writes target s Hpre Hpost Hframe.
  unfold wp; simpl. split; [exact Hpre|].
  intros r Hcallee. split.
  - apply Hpost. exact Hcallee.
  - intros x Hnotin. apply Hframe. exact Hnotin.
Qed.

(** Coercion-form state-lookup lemmas.

    The coercion [Coercion ls : state >-> Funclass] makes [s "x"] work
    as sugar but also produces terms like [(lupd s k v) x] (four arguments
    to [lupd]) rather than [lget (lupd s k v) x].  These lemmas use the
    same syntactic form so [rewrite] can match them. *)
Lemma ls_lupd_eq : forall s x v, (ls (lupd s x v)) x = v.
Proof. intros. exact (lupd_eq s x v). Qed.

Lemma ls_lupd_ne : forall s x y v, x <> y -> (ls (lupd s x v)) y = (ls s) y.
Proof. intros. rewrite lupd_ne; [reflexivity | auto]. Qed.

(** [ccall_simpl] -- lightweight: only rewrite [clobber nil] then [cbn].
    The more aggressive [[ls (lupd ...)]] rewrites are blocked by Coq's
    coercion normalisation in compiled Ltac (patterns lose the [ls]
    wrapper).  For CCall frame proofs we fall back to hand-written
    lemmas that are generated per-function. *)
Ltac ccall_simpl :=
  tryif (lazymatch goal with
    | [ |- context[clobber ?s nil] ] => idtac
    end)
  then (
    repeat (
      match goal with
      | [ H : context[clobber ?s nil] |- _ ] => rewrite (clobber_nil s) in H
      | [ |- context[clobber ?s nil] ] => rewrite (clobber_nil s)
      end
    );
    cbn -[lget ls lupd]
  )
  else idtac.

(** [wp_prove] -- structural recursion over goal shape after wp_reduce.
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
  | |- (true -> _) /\ _ => split; [intros; wp_prove | intros; exfalso; auto]
  | |- context[wp (CIf BTrue _ _) _ _] => rewrite wp_cif_btrue; wp_prove
  | |- forall _, ~ In _ (_ :: _) -> lget _ _ = lget (clobber (lupd _ _ (VZ _)) _) _ => apply wp_ccall_frame
  | |- forall _, _ => intro; wp_prove
  | |- exists _, _ => eexists; wp_prove
  | |- (if ?c then _ else _) = 1 \/ (if ?c then _ else _) = 0 =>
      destruct c; auto
  | |- _ \/ _ => solve [left; wp_prove | right; wp_prove]
  | |- ?x = ?x => reflexivity
  | |- context[clobber ?s nil] => rewrite (clobber_nil s); wp_prove
  | |- _ =>
      ccall_simpl; unfold lget, upd, updZ; cbn;
      solve [ assumption | reflexivity | lia | auto |
              match goal with
              | |- (if ?c then _ else _) = 1 => destruct c; [reflexivity | discriminate]
              | |- (if ?c then _ else _) = 0 => destruct c; [discriminate | reflexivity]
              | |- (if ?c then _ else _) = 1 \/ (if ?c then _ else _) = 0 => destruct c; auto
              end ]

  end.

(** ** Decomposition lemmas for staged proofs *)
Lemma wp_monotone_tac : forall c (Phi1 Phi2 : outcome_pred) s,
  wp c Phi1 s ->
  (forall o, Phi1 o -> Phi2 o) ->
  wp c Phi2 s.
Proof.
  intros c Phi1 Phi2 s Hwp Himpl.
  eapply wp_monotone; eassumption.
Qed.

Lemma wp_seq_decompose : forall c1 c2 (Phi1 : outcome_pred) (Phi2 : outcome_pred) s,
  wp c1 (fun o => match o with OReturn s' => wp c2 Phi2 s' | ORaise e s' => Phi2 (ORaise e s') end) s ->
  wp (CSeq c1 c2) Phi2 s.
Proof.
  intros; unfold wp; simpl. exact H.
Qed.

(** [wp_seq_decompose_normal] -- convenience for the common case where c1
    is expected to terminate normally (no exceptions).  Uses an intermediate
    state assertion [Q1 : assertion] as a mid-point, so existing staged
    proofs that pass [fun s' => ...] as the intermediate condition work
    without change.  Any raise from c1 propagates unchanged through c2. *)
Lemma wp_seq_decompose_normal : forall c1 c2 (Q1 : assertion) (Phi2 : outcome_pred) s,
  wp c1 (wp_normal Q1) s ->
  (forall s', Q1 s' -> wp c2 Phi2 s') ->
  wp (CSeq c1 c2) Phi2 s.
Proof.
  intros c1 c2 Q1 Phi2 s H1 H2.
  unfold wp; simpl.
  eapply wp_monotone_tac; [exact H1|].
  intros o Ho. unfold wp_normal in Ho.
  destruct o as [s' | e s'].
  - exact (H2 s' Ho).
  - contradiction.
Qed.

(** [vcg_exit] -- proves the while-exit verification condition. *)
Ltac vcg_exit :=
  unfold vcg_while_exit, beval, upd; simpl;
  repeat rewrite eqb_refl; simpl;
  intros; repeat (match goal with [H: _ /\ _ |- _] => destruct H end);
  match goal with [H: Z.leb _ _ = false |- _] => apply Z.leb_gt in H end;
  lia.

(** * Example 1: assignment *)
Theorem add_auto : forall (a b : Z),
  True ->
  wp (CAss "r"%string (APlus (AVar "a"%string) (AVar "b"%string)))
     (wp_normal (fun s => asZ (s "r"%string) = (a + b)%Z))
     (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof. Admitted.

(** * Example 2: conditional *)
Theorem max_auto : forall (a b : Z),
  0 <= a -> 0 <= b ->
  wp (CIf (BLe (AVar "b"%string) (AVar "a"%string))
          (CAss "r"%string (AVar "a"%string))
          (CAss "r"%string (AVar "b"%string)))
     (wp_normal (fun s => a <= asZ (s "r"%string) /\ b <= asZ (s "r"%string)))
     (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof. Admitted.

(** * Example 3: black hole with havoc *)
Theorem a_unchanged_auto : forall (a b : Z),
  wp (CSeq
       (CAss "x"%string (APlus (AVar "a"%string) (AVar "b"%string)))
       (CHavoc ["x"%string]))
     (wp_normal (fun s => asZ (lget s "a"%string) = a))
     (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof. Admitted.
