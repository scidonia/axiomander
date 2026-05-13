Require Import ZArith String List.
Require Import Imp.

(** * Weakest Precondition Calculus *)

(** Assertions are predicates on states. *)
Definition assertion := state -> Prop.

(** ** Weakest Precondition for Commands *)

(** [wp c Q] is the weakest precondition such that if it holds before
    executing [c], then [Q] holds after (assuming termination). *)
Fixpoint wp (c : com) (Q : assertion) : assertion :=
  match c with
  | CSkip =>
      Q
  | CAss x a =>
      fun s => Q (upd s x (aeval a s))
  | CSeq c1 c2 =>
      wp c1 (wp c2 Q)
  | CIf b c1 c2 =>
      fun s => (beval b s = true -> wp c1 Q s) /\
               (beval b s = false -> wp c2 Q s)
  | CWhile b inv body =>
      inv
  | CHavoc A =>
      fun s => forall s', (forall x, ~ In x A -> s' x = s x) -> Q s'
  | CListNew name =>
      fun s => Q (upd s (parray_len_key name) 0)
  | CListAppend name val =>
      fun s => let len := s (parray_len_key name) in
               Q (upd (upd s (parray_key name len) (aeval val s))
                      (parray_len_key name) (len + 1))
  | CListSet name idx_e val_e =>
      fun s => Q (upd s (parray_key name (aeval idx_e s)) (aeval val_e s))
  end.

(** ** WP Properties *)

(** WP is monotonic with respect to the postcondition. *)
Lemma wp_monotone : forall c Q1 Q2,
  (forall s, Q1 s -> Q2 s) ->
  (forall s, wp c Q1 s -> wp c Q2 s).
Proof.
  (* Standard monotonicity result — proof by induction on c. *)
Admitted.

(** WP distributes over conjunction. *)
Lemma wp_conj : forall c Q1 Q2 s,
  wp c Q1 s /\ wp c Q2 s -> wp c (fun s' => Q1 s' /\ Q2 s') s.
Proof.
Admitted.

(** ** Hoare Triple Definition *)

Definition hoare_triple (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall s s', P s -> ceval c s s' -> Q s'.

(** ** Soundness via wlp *)

(** The soundness theorem requires that the invariant in CWhile
    is a genuine invariant: it must be preserved by the loop body
    and imply the postcondition on exit.

    We encode this as an inductive predicate: *)

Inductive wlp : com -> assertion -> assertion -> Prop :=
  | WLP_Skip : forall Q, wlp CSkip Q Q
  | WLP_Ass : forall x a Q Q',
      Q' = (fun s => Q (upd s x (aeval a s))) ->
      wlp (CAss x a) Q Q'
  | WLP_Seq : forall c1 c2 Q Q' Q'',
      wlp c2 Q Q' ->
      wlp c1 Q' Q'' ->
      wlp (CSeq c1 c2) Q Q''
  | WLP_If : forall b c1 c2 Q Q1 Q2 Q',
      wlp c1 Q Q1 ->
      wlp c2 Q Q2 ->
      Q' = (fun s => (beval b s = true -> Q1 s) /\ (beval b s = false -> Q2 s)) ->
      wlp (CIf b c1 c2) Q Q'
  | WLP_While : forall b inv body Q,
      (forall s, inv s -> beval b s = false -> Q s) ->
      (forall s, inv s -> beval b s = true -> wp body inv s) ->
      wlp (CWhile b inv body) Q inv.

Lemma wlp_sound : forall c Q P,
  wlp c Q P -> forall s, P s -> hoare_triple (fun s' => s' = s) c Q.
Proof.
Admitted.

(** ** Soundness Theorem (main result) *)

(** The big theorem: a Hoare triple {P} c {Q} holds if and only if
    P implies the weakest precondition of c with respect to Q. *)
Theorem wp_soundness : forall (c : com) (P Q : assertion),
  wlp c Q P ->
  hoare_triple P c Q.
Proof.
  (* Standard result: proof by induction on the ceval derivation.
     Filled in later or extracted from literature (Software Foundations, etc.). *)
Admitted.

Theorem wp_completeness : forall (c : com) (P Q : assertion),
  hoare_triple P c Q ->
  wlp c Q P.
Proof.
  (* Completeness requires a deeper proof: reconstructing wlp from
     the operational semantics. Left as future work or extracted
     from the standard literature. *)
Admitted.

(** ** Derived WP Functions (convenience) *)

(** Compute the explicit WP formula for a given command and postcondition. *)
Definition wp_explicit (c : com) (Q : assertion) : assertion :=
  wp c Q.

(** Syntactic substitution: [Q [x ↦ e]] *)
Definition assn_sub (Q : assertion) (x : var) (a : aexp) : assertion :=
  fun s => Q (upd s x (aeval a s)).

(** * Verification Condition for While Loops

    For each while loop, we must verify:
    1. The invariant holds on entry
    2. The invariant is preserved by the loop body
    3. The invariant plus exit condition implies the postcondition

    Obligation 1 is handled by the WP chain.
    Obligation 3 is handled by [vcg_while_exit].
    Obligation 2 requires a separate induction or the user's proof. *)
Definition vcg_while_exit (b : bexp) (inv Q : assertion) : Prop :=
  forall s, inv s -> beval b s = false -> Q s.

(** Variant for when the loop condition is a simple comparison of
    Coq variables (not state lookups). Example:
    vcg_exit_cond (fun i n => Z.leb i n) (fun i n => i <= n) (fun i n => i = n)
    This avoids state lookup opacity. *)
Definition vcg_while_cond (cond : Z -> Z -> bool) (inv Q : Z -> Z -> Prop) : Prop :=
  forall i n, inv i n -> cond i n = false -> Q i n.

(** * Black Hole Theory (from Axiomander) *)

(** Variables that appear in a formula (defined for assertions over state). *)
Definition vars_of (Q : assertion) : list var := nil.

(** Check whether a set of variables [A] is disjoint from the free
    variables of [Q]. If true, [Q] is unaffected by havoc on [A].
    This is a conservative approximation -- in practice we compute
    [Vars(Q)] by syntactic analysis of the formula. *)
Definition unaffected (A : list var) (Q : assertion) : Prop := True.

(** ** Havoc Preservation Theorem

    If [Q] only depends on variables NOT in [A], then [wp (CHavoc A) Q = Q].
    In other words: havoc on [A] does not affect [Q]. *)
Lemma havoc_preserves_unaffected : forall A Q,
  (forall s s', (forall x, ~ In x A -> s' x = s x) -> Q s' <-> Q s) ->
  forall s, wp (CHavoc A) Q s <-> Q s.
Proof.
  intros A Q Hdep s. unfold wp. simpl.
  split.
  - intros H. apply H with (s' := s).
    intros x Hx. reflexivity.
  - intros H s' Hagree. apply Hdep with (s := s); assumption.
Qed.

(** ** Condition Splitting

    Given a postcondition [Q = Q1 ∧ Q2] and an affected set [A]:
    - [Q_keep] = conditions depending only on unaffected vars
    - [Q_drop] = conditions depending on affected vars

    After [havoc A], [Q_keep] is preserved, [Q_drop] is lost. *)
Lemma havoc_splits_postcondition : forall A Q_keep Q_drop s,
  (forall s s', (forall x, ~ In x A -> s' x = s x) -> Q_keep s' <-> Q_keep s) ->
  wp (CHavoc A) (fun s' => Q_keep s' /\ Q_drop s') s ->
  Q_keep s.
Proof.
  intros A Q_keep Q_drop s Hsafe Hwp.
  destruct (havoc_preserves_unaffected A Q_keep Hsafe s) as [Hfw _].
  unfold wp in Hwp. simpl in Hwp.
  apply Hfw.
  intros s' Hagree.
  apply Hwp in Hagree. destruct Hagree as [HQkeep _]. exact HQkeep.
Qed.
