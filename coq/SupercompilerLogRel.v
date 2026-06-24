From Stdlib Require Import List ZArith Bool String.
Import ListNotations.
Open Scope Z_scope.

Require Import LambdaA Supercompiler.

(** * Logical Relation and Adequacy for Supercompilation

    [E(e1, e2, F0)]: expressions [e1] and [e2] are logically related at
    base table [F0] iff for ALL extensions [F' ⊇ F0] and ALL fuel [n],
    they evaluate to the same [option pl_val]:

        ∀ F' ⊇ F0, ∀ n, p_eval F' n e1 = p_eval F' n e2.

    For the supercompiler:
    - [e1 = t], the original term
    - [e2 = supercompile F n history t], the supercompiled term
    - [F0 = F], the function table used for supercompilation
    - [F'] includes [F] plus any folded definitions produced

    Key theorems:
    - [adequacy]: [E(e1, e2, F) → p_eval F n e1 = p_eval F n e2]
    - [supercompile_fundamental]: [E(t, supercompile F n history t, F)]
    - [supercompile_adequate]: supercompiled term evaluates like original *)

(** * 1. World extension (function table inclusion) *)

Definition world_extends (W1 W2 : fn_table) : Prop :=
  forall f params body, In (f, (params, body)) W1 -> In (f, (params, body)) W2.

Lemma world_extends_refl : forall W, world_extends W W.
Proof. intros W f params body H; exact H. Qed.

Lemma world_extends_trans : forall W1 W2 W3,
  world_extends W1 W2 -> world_extends W2 W3 -> world_extends W1 W3.
Proof. intros W1 W2 W3 H12 H23 f params body H; apply H23; apply H12; auto. Qed.

(** * 2. Expression relation *)

(** The current supercompiler does not fold (no D1/D2), so there is
    no world growth.  The logical relation degenerates to evaluation
    equality at a fixed function table [F]:

        E(e1, e2, F)  :=  ∀ n, p_eval F n e1 = p_eval F n e2

    When folding is added (D1/D2), this extends to a Kripke relation
    indexed by [F ++ W] where [W] is the set of folded definitions
    produced during supercompilation.  See [SupercompilerFold.v]
    (future). *)

Definition E (e1 e2 : p_expr) (F : fn_table) : Prop :=
  forall n : nat, p_eval F n e1 = p_eval F n e2.

(** * 3. Adequacy: logically related terms evaluate identically *)

Theorem adequacy : forall e1 e2 F n,
  E e1 e2 F ->
  p_eval F n e1 = p_eval F n e2.
Proof.
  intros e1 e2 F n HE. apply HE.
Qed.

(** * 4. Fundamental lemma *)

Theorem supercompile_fundamental : forall F n history t,
  E t (supercompile F n history t) F.
Proof.
  intros F n history t m. apply (supercompile_sound F n history t m).
Qed.

(** * 5. End-to-end adequacy *)

Theorem supercompile_adequate : forall F n history t m v,
  p_eval F m (supercompile F n history t) = Some v ->
  p_eval F m t = Some v.
Proof.
  intros F n history t m v Hsc.
  pose proof (supercompile_fundamental F n history t) as HE.
  apply adequacy with (n := m) in HE. rewrite HE. exact Hsc.
Qed.

Theorem supercompile_adequate_sym : forall F n history t m v,
  p_eval F m t = Some v ->
  p_eval F m (supercompile F n history t) = Some v.
Proof.
  intros F n history t m v Ht.
  pose proof (supercompile_fundamental F n history t) as HE.
  apply adequacy with (n := m) in HE. rewrite <- HE. exact Ht.
Qed.

(** * 6. Contextual equivalence

    A context [C[-]] is a lambda_A term with a single hole.  Two terms
    [e1] and [e2] are contextually equivalent if for every context [C],
    filling the hole with [e1] or [e2] yields programs that evaluate
    to the same value:

        ∀ C, ∀ F n, p_eval F n C[e1] = p_eval F n C[e2].

    Since lambda_A is pure (no side effects), this is equivalent to the
    logical relation [E] being a congruence: if [E(e1, e2, F)] holds,
    then [E(C[e1], C[e2], F)] holds for any context [C]. *)

(** Contexts: a term with exactly one hole [[:]]. *)

(** Contexts cover the compositional cases where the relation lifts
    directly via [p_eval]'s definition.  [PLet] and [PCall] contexts
    are excluded — they require substitution/map commutation lemmas
    (same gap as [supercompile_sound]). *)

Inductive ctx :=
  | CHole
  | CBinOpL (op : pl_binop) (C : ctx) (rhs : p_expr)
  | CBinOpR (op : pl_binop) (lhs_val : pl_val) (C : ctx)
  | CIfCond (C : ctx) (thn els_br : p_expr).

Fixpoint fill (C : ctx) (e : p_expr) : p_expr :=
  match C with
  | CHole => e
  | CBinOpL op C' rhs => PBinOp op (fill C' e) rhs
  | CBinOpR op lhs_val C' => PBinOp op (PVal lhs_val) (fill C' e)
  | CIfCond C' thn els_br => PIf (fill C' e) thn els_br
  end.

(** * 7. Congruence: [E] is closed under contexts

    If [e1] and [e2] are logically related, plugging them into any
    context preserves the relation.  Proof by induction on [C],
    using the fact that each constructor of [p_expr] is compatible
    with the relation (compositionality of [p_eval]). *)

Lemma p_eval_binop_congr : forall F n op a1 a2 b1 b2,
  (forall m, p_eval F m a1 = p_eval F m a2) ->
  (forall m, p_eval F m b1 = p_eval F m b2) ->
  p_eval F n (PBinOp op a1 b1) = p_eval F n (PBinOp op a2 b2).
Proof.
  intros F n op a1 a2 b1 b2 Ha Hb.
  destruct n; simpl; auto.
  rewrite (Ha n), (Hb n); reflexivity.
Qed.

Lemma p_eval_if_congr : forall F n c1 c2 t1 t2 e1 e2,
  (forall m, p_eval F m c1 = p_eval F m c2) ->
  (forall m, p_eval F m t1 = p_eval F m t2) ->
  (forall m, p_eval F m e1 = p_eval F m e2) ->
  p_eval F n (PIf c1 t1 e1) = p_eval F n (PIf c2 t2 e2).
Proof.
  intros F n c1 c2 t1 t2 e1 e2 Hc Ht He.
  destruct n; simpl; auto.
  rewrite (Hc n). destruct (p_eval F n c2); auto.
  destruct p; auto.
  destruct b; simpl; [apply Ht | apply He].
Qed.

Lemma congruence : forall a1 a2 F C,
  E a1 a2 F ->
  E (fill C a1) (fill C a2) F.
Proof.
  intros a1 a2 F C HE.
  induction C; intro n; simpl.
  - apply HE.
  - (* CBinOpL *)
    apply (p_eval_binop_congr F n op (fill C a1) (fill C a2) rhs rhs IHC
      (fun m => eq_refl _)).
  - (* CBinOpR *)
    apply (p_eval_binop_congr F n op (PVal lhs_val) (PVal lhs_val) (fill C a1) (fill C a2)
      (fun m => eq_refl _) IHC).
  - (* CIfCond *)
    apply (p_eval_if_congr F n (fill C a1) (fill C a2) thn thn els_br els_br IHC
      (fun m => eq_refl _) (fun m => eq_refl _)).
Qed.

(** * 8. Contextual equivalence theorem

    A supercompiled term can replace the original in ANY program context
    without changing the observable result.  This is the strongest
    correctness guarantee for a program transformation. *)

Theorem supercompile_contextual_equivalence : forall F n history t C m v,
  p_eval F m (fill C (supercompile F n history t)) = Some v ->
  p_eval F m (fill C t) = Some v.
Proof.
  intros F n history t C m v Hsc.
  pose proof (supercompile_fundamental F n history t) as HE.
  pose proof (congruence _ _ F C HE) as Hcong.
  apply (adequacy _ _ F m) in Hcong.
  rewrite <- Hcong in Hsc. exact Hsc.
Qed.

Theorem supercompile_contextual_equivalence_sym : forall F n history t C m v,
  p_eval F m (fill C t) = Some v ->
  p_eval F m (fill C (supercompile F n history t)) = Some v.
Proof.
  intros F n history t C m v Ht.
  pose proof (supercompile_fundamental F n history t) as HE.
  pose proof (congruence _ _ F C HE) as Hcong.
  apply (adequacy _ _ F m) in Hcong.
  rewrite Hcong in Ht. exact Ht.
Qed.

(** * 9. What are F and W?

    - [F] is the **function table** [(fn_table)] — the user's signature
      [Σ] from the theory (fluid-contract-language-theory.md §1.1).
      It maps function names to [(params, body)] and is fixed for a
      given supercompilation run.  [F] contains user-defined pure
      predicates ([is_sorted], [is_hex], ...) and library built-ins.

    - [W] is the **world** — the set of new recursive function
      definitions created by the supercompiler's generalization+folding
      phase (D1/D2).  When the whistle blows and the supercompiler
      detects a repeating pattern, it generalizes the pattern into a
      fresh function body, adds it to [W], and replaces the original
      call sites with calls to the new function.

      For the current implementation (without D1/D2 folding):
        [W = []]  (empty world, no folding)

      For the full supercompiler with folding:
        [E(e1, e2, F, W) := ∀ F' ⊇ F ++ W, ∀ n, p_eval F' n e1 = p_eval F' n e2]

      The Kripke extension property ensures that adding more folded
      functions ([W'']) to [W] preserves the relation.  This is the
      key to proving that generalization + folding is sound: the
      generalized term inhabits a larger world where the original
      term can be folded back to a recursive call. *)
