From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.

(** The 8-lemma gate for the parallel exception development.

    If all eight Qed, convergence with the main pipeline is de-risked and
    we wire the Python side.  Each lemma stresses a different part of the
    hand-rolled WP:
      1. raise_val_irreducible      (in SnakeletExnLang.v)  -- stuck raise
      2. wp_raise                   (in SnakeletExnWp.v)     -- raise rule
      3. wp_try_normal, wp_try_catch                         -- try dispatch
      4. K[raise v] unwinding through a context              -- propagation
      5. wp_bind against the Result postcondition            -- composition
      6. wp_load / wp_store                                  -- heap steps
      7. exception arm carrying a points-to                  -- state-at-raise
      8. wp_call opaque against the FunCtx table             -- calls *)

Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.
Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
  (at level 20, e, Q at level 200, format "'WPE'  e  {{  Q  } }") : bi_scope.

Section gate.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Context `{FC : FunCtx}.

  (** Determinism for a top-level [Let x (Val v) e2] redex. *)
  Lemma prim_let_det x v e2 sigma kappa er sigma2 efs :
    prim_step (Let x (Val v) e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = subst x v e2 /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as -> Hin ->. apply fill_K_val in Hin as [-> ->].
        apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as -> Hin ->. apply fill_K_val in Hin as [-> ->].
        apply to_val_head_step in Hhead. discriminate.
  Qed.

  (** Determinism for [BinOp op (Val v1) (Val v2)]. *)
  Lemma prim_binop_det op v1 v2 sigma kappa er sigma2 efs :
    prim_step (BinOp op (Val v1) (Val v2)) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val (binop_eval op v1 v2) /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq;
          injection Heq as ?; subst;
          match goal with Hin : fill_K _ _ = Val _ |- _ =>
            apply fill_K_val in Hin as [-> ->] end;
          first [ apply to_val_pure_step in Hpure | idtac ]; try discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq;
          injection Heq as ?; subst;
          match goal with Hin : fill_K _ _ = Val _ |- _ =>
            apply fill_K_val in Hin as [-> ->] end;
          apply to_val_head_step in Hhead; discriminate.
  Qed.

  (** Determinism for [If (Val (LitBool true)) e1 e2]. *)
  Lemma prim_if_true_det e1 e2 sigma kappa er sigma2 efs :
    prim_step (If (Val (LitBool true)) e1 e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = e1 /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->]. apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->]. apply to_val_head_step in Hhead. discriminate.
  Qed.

  Lemma prim_if_false_det e1 e2 sigma kappa er sigma2 efs :
    prim_step (If (Val (LitBool false)) e1 e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = e2 /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->]. apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->]. apply to_val_head_step in Hhead. discriminate.
  Qed.

  (** Determinism for [Try (Val v) x h] (normal: handler skipped). *)
  Lemma prim_try_val_det v x h sigma kappa er sigma2 efs :
    prim_step (Try (Val v) x h) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val v /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        (* PureTryCatch: body is Raise (Val ev); but here body = Val v *)
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->].
        apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->].
        apply to_val_head_step in Hhead. discriminate.
  Qed.

  (** Determinism for [Try (Raise (Val ev)) x h] (catch: run handler).
      The interesting case: when [Try] is the outer context (K nonempty),
      its body [Raise (Val ev)] would have to step -- but it is irreducible
      (gate lemma 1), giving the contradiction. *)
  Lemma prim_try_catch_det ev x h sigma kappa er sigma2 efs :
    prim_step (Try (Raise (Val ev)) x h) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = subst x ev h /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x1 Hpure Heq | K x0 sg x1 sg2 efs2 Hhead Heq]; subst.
    (* head branch *)
    2: { destruct K as [|Ki K2]; simpl in Heq.
         { subst x0. inversion Hhead. }
         destruct Ki; simpl in Heq; try discriminate Heq.
         injection Heq as Hin ? ?; subst.
         exfalso.
         pose proof (fill_reducible_head K2 x0 _ _ _ _ Hhead) as Hred.
         rewrite Hin in Hred. eapply raise_val_irreducible. exact Hred. }
    (* pure branch *)
    destruct K as [|Ki K2]; simpl in Heq.
    { subst x0. inversion Hpure; subst; simpl in *.
      { repeat split; reflexivity. }
      destruct Ki; simpl in *; discriminate. }
    destruct Ki; simpl in Heq; try discriminate Heq.
    injection Heq as Hin ? ?; subst.
    exfalso.
    pose proof (fill_reducible_pure K2 x0 x1 empty Hpure) as Hred.
    rewrite Hin in Hred. eapply raise_val_irreducible. exact Hred.
  Qed.

  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200, format "'WPE'  e  {{  Q  } }") : bi_scope.

  (** Pure WP lemmas via wp_lift_pure_det + the determinism lemmas. *)
  Lemma wp_let x v e2 Phi :
    ▷ WPE (subst x v e2) {{ Phi }} ⊢ WPE (Let x (Val v) e2) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureLet.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_let_det in Hstep. tauto.
  Qed.

  Lemma wp_binop op v1 v2 Phi :
    ▷ WPE (Val (binop_eval op v1 v2)) {{ Phi }}
      ⊢ WPE (BinOp op (Val v1) (Val v2)) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureBinOp.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_binop_det in Hstep. tauto.
  Qed.

  Lemma wp_if_true e1 e2 Phi :
    ▷ WPE e1 {{ Phi }} ⊢ WPE (If (Val (LitBool true)) e1 e2) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureIfTrue.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_if_true_det in Hstep. tauto.
  Qed.

  Lemma wp_if_false e1 e2 Phi :
    ▷ WPE e2 {{ Phi }} ⊢ WPE (If (Val (LitBool false)) e1 e2) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureIfFalse.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_if_false_det in Hstep. tauto.
  Qed.

  (** * GATE LEMMA 3a: wp_try_normal.
      A try whose body returns a value [Val v] yields [v]; the handler
      is skipped. *)
  Lemma wp_try_normal v x h Phi :
    ▷ WPE (Val v) {{ Phi }} ⊢ WPE (Try (Val v) x h) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureTryVal.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_try_val_det in Hstep. tauto.
  Qed.

  (** * GATE LEMMA 3b: wp_try_catch.
      A try whose body raises [Raise (Val ev)] runs the handler with the
      exception object substituted for [x]. *)
  Lemma wp_try_catch ev x h Phi :
    ▷ WPE (subst x ev h) {{ Phi }} ⊢ WPE (Try (Raise (Val ev)) x h) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureTryCatch.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_try_catch_det in Hstep. tauto.
  Qed.

  (** Determinism for the unwind step [Let x (Raise (Val ev)) e2]. *)
  Lemma prim_unwind_let_det x ev e2 sigma kappa er sigma2 efs :
    prim_step (Let x (Raise (Val ev)) e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Raise (Val ev) /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x1 Hpure Heq | K x0 sg x1 sg2 efs2 Hhead Heq]; subst.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x0. inversion Hpure; subst; simpl in *.
        destruct Ki; simpl in H; try discriminate H.
        injection H; intros; subst; repeat split; reflexivity.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as ? Hin ?; subst.
        exfalso. pose proof (fill_reducible_pure K2 x0 x1 empty Hpure) as Hr.
        rewrite Hin in Hr. eapply raise_val_irreducible. exact Hr.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as ? Hin ?; subst.
        exfalso. pose proof (fill_reducible_head K2 x0 _ _ _ _ Hhead) as Hr.
        rewrite Hin in Hr. eapply raise_val_irreducible. exact Hr.
  Qed.

  (** * GATE LEMMA 4: raise unwinding through a neutral (Let) context.
      [Let x (Raise (Val (LitExn lbl pay))) e2] unwinds the raise out of
      the let -- the continuation [e2] is discarded -- yielding the
      exception result.  This is Python/ML semantics: an exception
      propagates up through the evaluation context until caught. *)
  Lemma wp_let_raise_unwind x lbl pay e2 Phi :
    Phi (RExn lbl pay) ⊢
      WPE (Let x (Raise (Val (LitExn lbl pay))) e2) {{ Phi }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_pure_det _ (Raise (Val (LitExn lbl pay)))); [done | | | ].
    - intros sigma. eapply reducible_pure.
      apply (PureRaiseUnwind (LetCtx x e2) (LitExn lbl pay)). reflexivity.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_unwind_let_det in Hstep. tauto.
    - iNext. by iApply wp_raise.
  Qed.

End gate.
