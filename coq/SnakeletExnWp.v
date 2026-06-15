From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export gen_heap fancy_updates.
From iris.bi Require Import fixpoint_mono.
From stdpp Require Import fin_maps.
Require Import SnakeletExnLang.

(** Hand-rolled weakest precondition for SnakeletExnLang.

    Unlike the stock Iris [wp] (postcondition [val -> iProp]), our
    postcondition ranges over [Result := RVal v | RExn label payload],
    following van Collem/de Vilhena/Krebbers (PLDI 2026): the result of a
    program is either a value or an uncaught raise.  A terminal expression
    [result_of e = Some r] feeds [r] to the postcondition; otherwise the
    expression must be reducible and we reason about the next step.

    We keep the model deliberately simple: no [num_laters_per_step], no
    later credits, empty observation list -- just enough to prove the
    8-lemma gate.  The heap interpretation reuses Iris [gen_heap]. *)

Class snakeletExn_heapGS_gen hlc Sigma := SnakeletExnHeapGS {
  #[global] snakeletExn_invGS :: invGS_gen hlc Sigma;
  #[global] snakeletExn_gen_heapG :: gen_heapGS loc sn_val Sigma;
}.
Global Existing Instance snakeletExn_invGS.
Global Existing Instance snakeletExn_gen_heapG.

Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section wp.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Context `{FC : FunCtx}.

  (** State interpretation: just the gen_heap authoritative view. *)
  Definition state_interp (sigma : sn_state) : iProp Sigma :=
    gen_heap_interp sigma.

  Implicit Types Phi : Result -> iProp Sigma.
  Implicit Types e : sn_expr.
  Implicit Types sigma : sn_state.

  (** The predicate whose fixpoint defines the WP. *)
  Definition wp_pre
      (wp : sn_expr -d> (Result -d> iPropO Sigma) -d> iPropO Sigma) :
      sn_expr -d> (Result -d> iPropO Sigma) -d> iPropO Sigma := fun e Phi =>
    match result_of e with
    | Some r => |={top}=> Phi r
    | None => ∀ sigma,
        state_interp sigma ={top,∅}=∗
          ⌜reducible e sigma⌝ ∗
          ∀ e' sigma' efs, ⌜prim_step e sigma [] e' sigma' efs⌝ ={∅}=∗ ▷ |={∅,top}=>
            state_interp sigma' ∗ wp e' Phi ∗
            ([∗ list] ef ∈ efs, wp ef (fun _ => True%I))
    end%I.

  Local Instance wp_pre_contractive : Contractive wp_pre.
  Proof.
    rewrite /wp_pre => n wp wp' Hwp e Phi.
    repeat (f_contractive || f_equiv); apply Hwp.
  Qed.

  Definition wp_exn : sn_expr -> (Result -> iProp Sigma) -> iProp Sigma :=
    fixpoint wp_pre.

  Lemma wp_exn_unfold e Phi : wp_exn e Phi ⊣⊢ wp_pre wp_exn e Phi.
  Proof. apply (fixpoint_unfold wp_pre). Qed.

  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200, format "'WPE'  e  {{  Q  } }") : bi_scope.

  (** A value terminates with [RVal v]. *)
  Lemma wp_value v Phi : Phi (RVal v) ⊢ WPE (Val v) {{ Phi }}.
  Proof.
    iIntros "H". rewrite wp_exn_unfold /wp_pre /=. by iModIntro.
  Qed.

  (** * GATE LEMMA 2: wp_raise.
      An uncaught [Raise (Val (LitExn lbl pay))] terminates with the
      exception result [RExn lbl pay].  The exceptional postcondition
      arm [Phi (RExn lbl pay)] is discharged against the CURRENT heap
      (state-at-raise), since the raise is terminal. *)
  Lemma wp_raise lbl pay Phi :
    Phi (RExn lbl pay) ⊢ WPE (Raise (Val (LitExn lbl pay))) {{ Phi }}.
  Proof.
    iIntros "H". rewrite wp_exn_unfold /wp_pre /=. by iModIntro.
  Qed.

  (** Generic pure-step lifting: if [e] is non-terminal, reducible in
      every state, and every step is the deterministic pure step to [e']
      (no heap change, no forks), then [WPE e] follows from [▷ WPE e'].
      All the pure WP lemmas (let, binop, if, try, unwind) instantiate
      this. *)
  Lemma wp_lift_pure_det e e' Phi :
    result_of e = None ->
    (forall sigma, reducible e sigma) ->
    (forall sigma kappa e2 sigma2 efs,
        prim_step e sigma kappa e2 sigma2 efs ->
        kappa = [] /\ e2 = e' /\ sigma2 = sigma /\ efs = []) ->
    ▷ WPE e' {{ Phi }} ⊢ WPE e {{ Phi }}.
  Proof.
    intros Hterm Hred Hdet.
    iIntros "H". rewrite (wp_exn_unfold e) /wp_pre Hterm.
    iIntros (sigma) "Hs".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit; [iPureIntro; apply Hred|].
    iIntros (e2 sigma2 efs Hstep).
    destruct (Hdet _ _ _ _ _ Hstep) as (_ & -> & -> & ->).
    iModIntro. iNext. iMod "Hclose". iModIntro.
    simpl. iFrame "Hs H".
  Qed.

  (** Reducibility witness from a pure step at the empty context. *)
  Lemma reducible_pure e e' sigma :
    pure_step e e' -> reducible e sigma.
  Proof.
    intros Hp. exists [], e', sigma, [].
    apply (PrimPureStep [] e sigma e' Hp).
  Qed.

  Lemma reducible_head e sigma e' sigma' efs :
    head_step e sigma e' sigma' efs -> reducible e sigma.
  Proof.
    intros Hh. exists [], e', sigma', efs.
    apply (PrimHeadStep [] e sigma e' sigma' efs Hh).
  Qed.

  (** If the hole steps, the filled expression is reducible. *)
  Lemma fill_reducible_pure K x x' sigma :
    pure_step x x' -> reducible (fill_K K x) sigma.
  Proof.
    intros Hp. exists [], (fill_K K x'), sigma, [].
    apply (PrimPureStep K x sigma x' Hp).
  Qed.

  Lemma fill_reducible_head K x sigma x' sigma' efs :
    head_step x sigma x' sigma' efs -> reducible (fill_K K x) sigma.
  Proof.
    intros Hh. exists [], (fill_K K x'), sigma', efs.
    apply (PrimHeadStep K x sigma x' sigma' efs Hh).
  Qed.

  (** result_of inversion. *)
  Lemma result_of_val e v : result_of e = Some (RVal v) -> e = Val v.
  Proof.
    destruct e; simpl; intros H; try discriminate H.
    - injection H as ->; reflexivity.
    - (* Raise case: result_of is Some (RExn..) or None, never RVal *)
      destruct e; try discriminate H. destruct v0; discriminate H.
  Qed.

  Lemma result_of_exn e lbl pay :
    result_of e = Some (RExn lbl pay) -> e = Raise (Val (LitExn lbl pay)).
  Proof.
    destruct e; simpl; try discriminate.
    destruct e; simpl; try discriminate.
    destruct v; simpl; try discriminate.
    intros H; inversion H; subst; reflexivity.
  Qed.

  (** Single-item step lifting: a step of [e] lifts to a step of
      [fill_item Ki e] in the same context.  Uses [fill_K (Ki :: K) = fill_item Ki o fill_K K]. *)
  Lemma prim_step_fill_item Ki e sigma kappa e' sigma' efs :
    prim_step e sigma kappa e' sigma' efs ->
    prim_step (fill_item Ki e) sigma kappa (fill_item Ki e') sigma' efs.
  Proof.
    intros Hstep. inversion Hstep as [K x sg x' Hpure Heq | K x sg x' sg' efs' Hhead Heq]; subst.
    - apply (PrimPureStep (Ki :: K) x _ x' Hpure).
    - apply (PrimHeadStep (Ki :: K) x _ x' _ efs Hhead).
  Qed.

  Lemma reducible_fill_item Ki e sigma :
    reducible e sigma -> reducible (fill_item Ki e) sigma.
  Proof.
    intros (kappa & e' & sigma' & efs & Hstep).
    exists kappa, (fill_item Ki e'), sigma', efs.
    by apply prim_step_fill_item.
  Qed.

  (** A pure redex of shape [fill_item Ki e] with [e] non-value and not a
      stuck raise is impossible -- the redex must be live inside [e]. *)
  Lemma kempty Ki e e' :
    to_val e = None -> (forall v, e <> Raise (Val v)) ->
    pure_step (fill_item Ki e) e' -> False.
  Proof.
    intros Hnv Hnr Hpure.
    inversion Hpure as [vv xx ee2 Hp | op vv1 vv2 Hp | ee1 ee2 Hp | ee1 ee2 Hp
                       | vv xx hh Hp | ev xx hh Hp | Ki0 w Hneu Hp ]; subst.
    1-5: destruct Ki; simpl in Hp; try discriminate Hp;
         injection Hp; intros; subst; simpl in Hnv; discriminate.
    - destruct Ki; simpl in Hp; try discriminate Hp.
      injection Hp; intros; subst. exfalso. eapply Hnr. reflexivity.
    - assert (Ki0 = Ki) as ->.
      { eapply (fill_item_no_val_inj Ki0 Ki (Raise (Val w)) e);
          [ reflexivity | exact Hnv | exact Hp ]. }
      apply fill_item_inj in Hp. exfalso. eapply Hnr. symmetry. exact Hp.
  Qed.

  Lemma kempty_head Ki e sigma e' sigma' efs :
    to_val e = None ->
    head_step (fill_item Ki e) sigma e' sigma' efs -> False.
  Proof.
    intros Hnv Hhead.
    destruct Ki; simpl in Hhead; inversion Hhead; subst;
      simpl in Hnv; discriminate.
  Qed.

  (** Fill-context step inversion: if [fill_item Ki e] steps and [e] is
      non-value and not a stuck raise (hence its redex is live), the step
      happens inside [e].  This is the [step_by_val] analogue and the
      linchpin for [wp_bind]. *)
  Lemma fill_item_step_inv Ki e sigma kappa e2 sigma2 efs :
    to_val e = None ->
    (forall v, e <> Raise (Val v)) ->
    prim_step (fill_item Ki e) sigma kappa e2 sigma2 efs ->
    exists e', e2 = fill_item Ki e' /\ prim_step e sigma kappa e' sigma2 efs.
  Proof.
    intros Hnv Hnr Hstep.
    inversion Hstep as [K x sg x' Hpure Heq | K x sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki2 K2]; simpl in Heq.
      + exfalso. subst x. eapply kempty; eauto.
      + assert (Ki2 = Ki) as ->.
        { eapply (fill_item_no_val_inj Ki2 Ki (fill_K K2 x) e); [ | exact Hnv | exact Heq ].
          apply fill_not_val. by apply to_val_pure_step in Hpure. }
        apply fill_item_inj in Heq. subst e.
        exists (fill_K K2 x'). split; [reflexivity|].
        apply (PrimPureStep K2 x _ x' Hpure).
    - destruct K as [|Ki2 K2]; simpl in Heq.
      + exfalso. subst x. eapply kempty_head; eauto.
      + assert (Ki2 = Ki) as ->.
        { eapply (fill_item_no_val_inj Ki2 Ki (fill_K K2 x) e); [ | exact Hnv | exact Heq ].
          apply fill_not_val. by apply to_val_head_step in Hhead. }
        apply fill_item_inj in Heq. subst e.
        exists (fill_K K2 x'). split; [reflexivity|].
        apply (PrimHeadStep K2 x _ x' _ efs Hhead).
  Qed.

End wp.

(** Notation for the WP and the two-postcondition form. *)
Notation "'WPE' e {{ Phi } }" := (wp_exn e Phi)
  (at level 20, e, Phi at level 200, format "'WPE'  e  {{  Phi  } }") : bi_scope.
