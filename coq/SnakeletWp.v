From iris.proofmode Require Import proofmode coq_tactics reduction.
From iris.program_logic Require Import lifting.
From iris.base_logic.lib Require Export gen_heap own ghost_map.
From iris.algebra Require Import excl.
From iris.algebra Require Import dfrac agree.
From stdpp Require Import fin_maps fin_map_dom.
Require Import SnakeletLang.
Import snakelet_notation.

Local Notation "l ↦{ dq } v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦{ dq }  v") : bi_scope.
Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Class snakelet_heapGS_gen hlc Σ := SnakeletHeapGS {
  #[global] snakelet_invGS :: invGS_gen hlc Σ;
  #[global] snakelet_gen_heapG :: gen_heapGS loc sn_val Σ;
}.
Global Existing Instance snakelet_invGS.
Global Existing Instance snakelet_gen_heapG.
Notation snakelet_heapGS := (snakelet_heapGS_gen HasLc).

Section snakelet_wp.
  Context `{!snakelet_heapGS_gen hlc Σ}.
  Context `{FC : FunCtx}.
  Context `{!ghost_mapG Σ string fun_entry}.

  Definition snakelet_state_interp (σ : sn_state) (ns : nat) (κs : list observation) (nt : nat) : iProp Σ :=
    gen_heap_interp σ.

  Global Program Instance snakelet_irisGS : irisGS_gen hlc snakelet_lang Σ := {|
    iris_invGS := snakelet_invGS;
    state_interp := snakelet_state_interp;
    fork_post _ := True%I;
    num_laters_per_step _ := 0%nat;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  |}.
  Global Opaque iris_invGS.
  Implicit Types l : loc.

  (** Determinant lemmas — pure steps *)
  Lemma reducible_pure_step e e' σ :
    pure_step e e' → reducible e σ.
  Proof.
    intros Hpure. eexists [], e', σ, [].
    eapply (PrimPureStep [] _ σ). exact Hpure.
  Qed.

  Lemma reducible_no_obs_pure_step e e' σ :
    pure_step e e' → reducible_no_obs e σ.
  Proof.
    intros Hpure. eexists e', σ, [].
    eapply (PrimPureStep [] _ σ). exact Hpure.
  Qed.

  Lemma prim_binop_det op v1 v2 σ κ e2 σ2 efs :
    prim_step (BinOp op (Val v1) (Val v2)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = Val (binop_eval op v1 v2).
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
  Qed.

  Lemma prim_let_det x v e σ κ e2 σ2 efs :
    prim_step (Let x (Val v) e) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = subst x v e.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
  Qed.

  Lemma prim_if_true_det e1 e2 σ κ e2' σ2 efs :
    prim_step (If (Val (LitBool true)) e1 e2) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2' = e1.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
  Qed.

  Lemma prim_if_false_det e1 e2 σ κ e2' σ2 efs :
    prim_step (If (Val (LitBool false)) e1 e2) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2' = e2.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
  Qed.

  Lemma prim_while_det e1 e2 σ κ e2' σ2 efs :
    prim_step (While e1 e2) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧
    e2' = If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit).
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H; discriminate H.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0.
      + destruct Ki; simpl in H; discriminate H.
  Qed.

  (* For-loop reductions: the list operand is already a value, so the only
     step is the pure peel at K = []. A ForCtx around a value list is
     impossible (fill_K_val rules it out). *)
  Lemma prim_for_nil_det x body σ κ e2' σ2 efs :
    prim_step (For x (Val (LitList [])) body) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2' = Val LitUnit.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ =>
             apply fill_K_val in H as [-> ->] end; inversion H0).
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ =>
             apply fill_K_val in H as [-> ->] end; inversion H0).
  Qed.

  Lemma prim_for_cons_det x v vs body σ κ e2' σ2 efs :
    prim_step (For x (Val (LitList (v :: vs))) body) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧
    e2' = Let "_" (subst x v body) (For x (Val (LitList vs)) body).
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ =>
             apply fill_K_val in H as [-> ->] end; inversion H0).
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ =>
             apply fill_K_val in H as [-> ->] end; inversion H0).
  Qed.

  (* Dict-key For-loop det lemmas — same proof structure as list For. *)
  Lemma prim_for_dict_nil_det x body σ κ e2' σ2 efs :
    prim_step (For x (Val (LitDict [])) body) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2' = Val LitUnit.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ =>
             apply fill_K_val in H as [-> ->] end; inversion H0).
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ =>
             apply fill_K_val in H as [-> ->] end; inversion H0).
  Qed.

  Lemma prim_for_dict_cons_det x k v kvs body σ κ e2' σ2 efs :
    prim_step (For x (Val (LitDict ((k, v) :: kvs))) body) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧
    e2' = Let "_" (subst x k body) (For x (Val (LitDict kvs)) body).
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0; subst; repeat split; reflexivity.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ =>
             apply fill_K_val in H as [-> ->] end; inversion H0).
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ =>
             apply fill_K_val in H as [-> ->] end; inversion H0).
  Qed.

  (** Head-step determinant lemmas *)
  Lemma head_load_det l σ e2 σ2 efs :
    head_step (Load (Val (LitLoc l))) σ e2 σ2 efs →
    ∃ v, σ !! l = Some v ∧ e2 = Val v ∧ σ2 = σ ∧ efs = [].
  Proof. intros H. inversion H; subst. eauto. Qed.

  Lemma head_store_det l v σ e2 σ2 efs :
    head_step (Store (Val (LitLoc l)) (Val v)) σ e2 σ2 efs →
    is_Some (σ !! l) ∧ e2 = Val LitUnit ∧ σ2 = <[l:=v]> σ ∧ efs = [].
  Proof. intros H. inversion H; subst. split; [done|]. auto. Qed.

  Lemma head_alloc_det v σ e2 σ2 efs :
    head_step (Alloc (Val v)) σ e2 σ2 efs →
    ∃ l, σ !! l = None ∧ e2 = Val (LitLoc l) ∧ σ2 = <[l:=v]> σ ∧ efs = [].
  Proof. intros H. inversion H; subst. eauto. Qed.

  Lemma head_faa_det l v σ e2 σ2 efs :
    head_step (FAA (Val (LitLoc l)) (Val v)) σ e2 σ2 efs →
    ∃ z, σ !! l = Some (LitInt z) ∧
         e2 = Val (LitInt z) ∧ σ2 = <[l:=LitInt (z + lit_as_z v)]> σ ∧ efs = [].
  Proof. intros H. inversion H; subst. eauto. Qed.

  Lemma head_fork_det e σ e2 σ2 efs :
    head_step (Fork e) σ e2 σ2 efs →
    e2 = Val LitUnit ∧ σ2 = σ ∧ efs = [e].
  Proof. intros H. inversion H; subst. auto. Qed.

  Lemma head_raise_det v σ e2 σ2 efs :
    head_step (Raise (Val v)) σ e2 σ2 efs →
    e2 = Val v ∧ σ2 = σ ∧ efs = [].
  Proof. intros H. inversion H; subst. auto. Qed.

  Lemma prim_raise_det v σ κ e2 σ2 efs :
    prim_step (Raise (Val v)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = Val v.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. exfalso; inversion H0.
      + destruct Ki; simpl in H; discriminate H.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. eapply head_raise_det in H0 as (->&->&->). auto.
      + destruct Ki; simpl in H; discriminate H.
  Qed.

  Lemma prim_try_val_det v handler σ κ e2 σ2 efs :
    prim_step (Try (Val v) handler) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = Val v.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H;
      [subst x; inversion H0; subst; auto | destruct Ki; simpl in H; discriminate H].
    - destruct K as [|Ki K']; simpl in H;
      [subst x; inversion H0; subst;
       match goal with H : head_step (Val _) _ _ _ _ |- _ => inversion H end
      | destruct Ki; simpl in H; discriminate H].
  Qed.

  Lemma prim_load_det l σ κ e2 σ2 efs v :
    σ !! l = Some v →
    prim_step (Load (Val (LitLoc l))) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = Val v.
  Proof.
    intros Hlookup Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. exfalso; inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
    - destruct K as [|Ki K']; simpl in H.
      + subst x. edestruct head_load_det as (v'&Hlook'&->&->&->); eauto.
        assert (v = v') by congruence; subst v'. auto.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
  Qed.

  Lemma prim_store_det l v σ κ e2 σ2 efs :
    is_Some (σ !! l) →
    prim_step (Store (Val (LitLoc l)) (Val v)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = <[l:=v]> σ ∧ efs = [] ∧ e2 = Val LitUnit.
  Proof.
    intros Hlookup Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. exfalso; inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
    - destruct K as [|Ki K']; simpl in H.
      + subst x. eapply head_store_det in H0 as (?&->&->&->). auto.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
  Qed.

  Lemma prim_alloc_det v σ κ e2 σ2 efs :
    prim_step (Alloc (Val v)) σ κ e2 σ2 efs →
    ∃ l, σ !! l = None ∧ κ = [] ∧ σ2 = <[l:=v]> σ ∧ efs = [] ∧ e2 = Val (LitLoc l).
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. exfalso; inversion H0.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
    - destruct K as [|Ki K']; simpl in H.
      + subst x. eapply head_alloc_det in H0 as (l&?&->&->&->). exists l; split; [done|]. auto.
      + destruct Ki; simpl in H;
          try discriminate H;
          (inversion H; clear H;
           match goal with H: fill_K _ _ = Val _ |- _ => apply fill_K_val in H as [-> ->] end;
           inversion H0; subst; repeat split; reflexivity).
  Qed.

  (** Pure WP lemmas *)
  Lemma wp_binop s E op v1 v2 Φ :
    ▷ Φ (binop_eval op v1 v2) -∗
    WP BinOp op (Val v1) (Val v2) @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (BinOp op (Val v1) (Val v2)) (Val (binop_eval op v1 v2)) σ
            (PureBinOp op v1 v2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2 σ2 efs Hprim.
      pose proof (prim_binop_det _ _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2 efs σ Hprim) "Hcred".
      pose proof (prim_binop_det _ _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    iApply (wp_value' with "HΦ").
  Qed.

  Lemma wp_let s E x v e2 Φ :
    ▷ WP subst x v e2 @ s; E {{ Φ }} -∗
    WP Let x (Val v) e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (Let x (Val v) e2) (subst x v e2) σ
            (PureLet v x e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_let_det _ _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_let_det _ _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  Lemma wp_if_true s E e1 e2 Φ :
    ▷ WP e1 @ s; E {{ Φ }} -∗
    WP If (#true)%S e1 e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (If (Val (LitBool true)) e1 e2) e1 σ
            (PureIfTrue e1 e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_if_true_det _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_if_true_det _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  Lemma wp_if_false s E e1 e2 Φ :
    ▷ WP e2 @ s; E {{ Φ }} -∗
    WP If (#false)%S e1 e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (If (Val (LitBool false)) e1 e2) e2 σ
            (PureIfFalse e1 e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_if_false_det _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_if_false_det _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  Lemma wp_while s E e1 e2 Φ :
    ▷ WP If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit) @ s; E {{ Φ }} -∗
    WP While e1 e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (While e1 e2) (If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit)) σ
            (PureWhile e1 e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_while_det _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_while_det _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  (** For-loop WP rules.  The list operand is a value; one pure step peels
      the head (or terminates on []).  [wp_for_list] does the induction. *)

  Lemma wp_for_nil s E x body Φ :
    ▷ Φ LitUnit -∗
    WP For x (Val (LitList [])) body @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + apply reducible_no_obs_reducible,
          (reducible_no_obs_pure_step _ _ σ (PureForNil x body)).
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_for_nil_det _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_for_nil_det _ _ _ _ _ _ _ Hprim) as [_ [_ [_ He2]]].
      rewrite He2. iApply wp_value'. by iFrame.
  Qed.

  Lemma wp_for_cons s E x v vs body Φ :
    ▷ WP Let "_" (subst x v body) (For x (Val (LitList vs)) body) @ s; E {{ Φ }} -∗
    WP For x (Val (LitList (v :: vs))) body @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + apply reducible_no_obs_reducible,
          (reducible_no_obs_pure_step _ _ σ (PureForCons x v vs body)).
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_for_cons_det _ _ _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_for_cons_det _ _ _ _ _ _ _ _ _ Hprim) as [_ [_ [_ He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  (** The fold rule: iterate [body] over the list model [M].  The invariant
      [P : list sn_val -> iProp] holds over the *remaining* suffix.  Proven by
      structural induction on [M] -- no iLoeb, no later beyond the per-step
      pure delay.  [Hclosed] states the loop body does not capture the "_"
      sequencing binder (always true for generated bodies, which use fresh
      names); it lets the post-iteration continuation match the inner For. *)
  Lemma wp_for_list s E x body (M : list sn_val) (P : list sn_val -> iProp Σ) :
    (forall w, subst "_" w body = body) ->
    P M -∗
    (□ ∀ v vs, P (v :: vs) -∗
        WP subst x v body @ s; E {{ _, P vs }}) -∗
    WP For x (Val (LitList M)) body @ s; E {{ _, P [] }}.
  Proof.
    iIntros (Hclosed) "HP #Hstep".
    iInduction M as [|v vs] "IH"; simpl.
    - iApply wp_for_nil. by iFrame.
    - iApply wp_for_cons. iNext.
      iApply (wp_bind (fill_item (LetCtx "_" _))).
      iApply (wp_wand with "[HP]").
      { iApply ("Hstep" with "HP"). }
      iIntros (w) "HPvs". simpl.
      iApply wp_let. iNext.
      assert (subst "_" w (For x (Val (LitList vs)) body)
              = For x (Val (LitList vs)) body) as Heq.
      { cbn [subst]. destruct (String.eqb "_" x); by rewrite ?Hclosed. }
      rewrite Heq.
      iApply ("IH" with "HPvs").
  Qed.

  (* Variant with a general postcondition Φ: the loop result is always
     LitUnit, so [Φ] need only hold at LitUnit once the list is consumed.
     This shape lets the call site keep an arbitrary continuation
     postcondition (the For sits under a [;; rest]). *)
  Lemma wp_for_list' s E x body (M : list sn_val)
      (P : list sn_val -> iProp Σ) (Φ : sn_val -> iProp Σ) :
    (forall w, subst "_" w body = body) ->
    P M -∗
    (□ ∀ v vs, P (v :: vs) -∗
        WP subst x v body @ s; E {{ _, P vs }}) -∗
    (P [] -∗ Φ LitUnit) -∗
    WP For x (Val (LitList M)) body @ s; E {{ Φ }}.
  Proof.
    iIntros (Hclosed) "HP #Hstep Hpost".
    iInduction M as [|v vs] "IH"; simpl.
    - iApply wp_for_nil. iNext. by iApply "Hpost".
    - iApply wp_for_cons. iNext.
      iApply (wp_bind (fill_item (LetCtx "_" _))).
      iApply (wp_wand with "[HP]").
      { iApply ("Hstep" with "HP"). }
      iIntros (w) "HPvs". simpl.
      iApply wp_let. iNext.
      assert (subst "_" w (For x (Val (LitList vs)) body)
              = For x (Val (LitList vs)) body) as Heq.
      { cbn [subst]. destruct (String.eqb "_" x); by rewrite ?Hclosed. }
      rewrite Heq.
      iApply ("IH" with "HPvs Hpost").
  Qed.

  (** Forall-accumulating for-loop.  Mirrors wp_for_list' but decomposes
      the Forall-invariant into per-element [Q v] premises. *)
  Lemma wp_for_list_forall (Q : sn_val -> Prop) s E x body (M : list sn_val)
      (Φ : sn_val -> iProp Σ) :
    (forall w, subst "_" w body = body) ->
    ⌜Forall Q M⌝ -∗
    (□ ∀ v vs,
        ⌜Forall Q (v :: vs)⌝ -∗
        WP subst x v body @ s; E {{ _, ⌜Forall Q vs⌝ }}) -∗
    (⌜Forall Q []⌝ -∗ Φ LitUnit) -∗
    WP For x (Val (LitList M)) body @ s; E {{ Φ }}.
  Proof.
    iIntros (Hclosed) "HP #Hstep Hpost".
    iInduction M as [|v vs] "IH"; simpl.
    - iApply wp_for_nil. iNext. by iApply "Hpost".
    - iApply wp_for_cons. iNext.
      iApply (wp_bind (fill_item (LetCtx "_" _))).
      iApply (wp_wand with "[HP]").
      { iApply ("Hstep" $! v vs with "HP"). }
      iIntros (w) "HPvs". simpl.
      iApply wp_let. iNext.
      assert (subst "_" w (For x (Val (LitList vs)) body)
              = For x (Val (LitList vs)) body) as Heq.        
      { cbn [subst]. destruct (String.eqb "_" x); by rewrite ?Hclosed. }
      rewrite Heq.
      iApply ("IH" with "HPvs Hpost").
  Qed.

  Lemma wp_raise s E v Φ :
    ▷ Φ v -∗ WP Raise (Val v) @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      eexists (Val v), σ1, []. eapply (PrimHeadStep [] (Raise _) σ1).
      eapply HeadRaise. }
    iNext. iIntros (e2 σ2 efs Hstep) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    pose proof (prim_raise_det _ _ _ _ _ _ Hstep) as [Hκ [Hσ [Hefs He2]]].
    rewrite He2 Hκ Hσ Hefs.
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  Lemma wp_try_val s E v handler Φ :
    ▷ Φ v -∗ WP Try (Val v) handler @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (Try (Val v) handler) (Val v) σ
            (PureTryReturn v handler)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2 σ2 efs Hprim.
      pose proof (prim_try_val_det _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2 efs σ Hprim) "Hcred".
      pose proof (prim_try_val_det _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iApply wp_value'. iExact "HΦ".
  Qed.

  (** Stateful WP lemmas.

      Puzzle: after [wp_lift_atomic_step], the postcondition is
      [from_option Φ False (to_val e2)].  We use [wp_lift_step] (which returns
      [WP e2 {{ Φ }}]) and handle the pure step directly — this avoids the
      [from_option] wrinkle entirely. *)

  Lemma wp_load s E l v Φ :
    l ↦ v -∗
    (l ↦ v -∗ Φ v) -∗
    WP Load (Val (LitLoc l)) @ s; E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      eexists _, _, []. eapply (PrimHeadStep [] (Load _) σ1).
      eapply (HeadLoad l v σ1). done. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    pose proof (prim_load_det l σ1 κ e2 σ2 efs v Hlookup Hprim) as [Hκ [Hσ2 [Hefs He2]]].
    rewrite He2 Hκ Hσ2 Hefs.
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSpecialize ("HΦ" with "Hl").
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  Lemma wp_store s E l v (w : sn_val) Φ :
    l ↦ v -∗
    (l ↦ w -∗ Φ LitUnit) -∗
    WP Store (Val (LitLoc l)) (Val w) @ s; E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      eexists _, _, []. eapply (PrimHeadStep [] (Store _ _) σ1).
      eapply (HeadStore l w σ1). eauto. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    assert (is_Some (σ1 !! l)). { eexists; eauto. }
    pose proof (prim_store_det l w σ1 κ e2 σ2 efs H Hprim) as [Hκ [Hσ2 [Hefs He2]]].
    rewrite He2 Hκ Hσ2 Hefs.
    iMod (gen_heap_update with "Hσ Hl") as "[Hσ Hl]".
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSpecialize ("HΦ" with "Hl").
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  Lemma fresh_loc (σ : sn_state) : ∃ l, σ !! l = None.
  Proof.
    set (d := @dom (gmap loc sn_val) (gset loc) (@gset_dom loc _ _ sn_val) σ).
    destruct (exist_fresh d) as [l Hl].
    exists l. eapply (not_elem_of_dom_1 (M:=gmap loc) (D:=gset loc)). exact Hl.
  Qed.

  Lemma wp_alloc s E v Φ :
    (∀ l, l ↦ v -∗ Φ (LitLoc l)) -∗
    WP Alloc (Val v) @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    edestruct fresh_loc as [l Hfree].
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      eexists (Val (LitLoc l)), (<[l:=v]> σ1), [].
      eapply (PrimHeadStep [] (Alloc _) σ1).
      eapply (HeadAlloc v σ1 l). done. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    pose proof (prim_alloc_det v σ1 κ e2 σ2 efs Hprim) as (l'&Hfree2&Hκ&Hσ2&Hefs&He2).
    rewrite He2 Hκ Hσ2 Hefs.
    iMod (gen_heap_alloc with "Hσ") as "[Hσ Hl]"; first done.
    iDestruct "Hl" as "[Hl _]".
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSpecialize ("HΦ" $! l' with "Hl").
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  (** Inversion lemma for calls.  The step source is determined by the
      single [fun_entries] table: an opaque call steps only within its
      precondition, to any postcondition-admitted value (the result is
      existentially quantified — [post] is a relation); a transparent call
      unfolds to its substituted body. *)
  (** * Environment-form tactic lemmas (heap_lang style).

      These state load/store against the proof-mode environment with an
      [envs_lookup] premise where the location [l] is *concrete* (it
      comes from the goal expression).  [iAssumptionCore] then finds the
      points-to hypothesis by unification on the location — never by
      name — and [envs_simple_replace] updates it in place, so the
      hypothesis keeps its name across a store.  This is what makes
      generated proof scripts robust: the script never mentions
      hypothesis names or locations, so small program variations
      (extra cells, renamed variables, different constants) leave the
      stage sequence unchanged. *)

  Lemma tac_wp_load Δ s E i K l v Φ :
    envs_lookup i Δ = Some (false, pointsto l (DfracOwn 1) v) →
    envs_entails Δ (WP fill_K K (Val v) @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill_K K (Load (Val (LitLoc l))) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hl Hwp.
    rewrite -wp_bind.
    eapply bi.wand_apply; first by apply bi.wand_entails, wp_load.
    rewrite envs_lookup_split //; simpl.
    apply bi.sep_mono_r. apply bi.wand_mono; [done|]. exact Hwp.
  Qed.

  Lemma tac_wp_store Δ s E i K l v w Φ :
    envs_lookup i Δ = Some (false, pointsto l (DfracOwn 1) v) →
    match envs_simple_replace i false
            (Esnoc Enil i (pointsto l (DfracOwn 1) w)) Δ with
    | Some Δ' => envs_entails Δ' (WP fill_K K (Val LitUnit) @ s; E {{ Φ }})
    | None => False
    end →
    envs_entails Δ (WP fill_K K (Store (Val (LitLoc l)) (Val w)) @ s; E {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hl Hsuc.
    destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:HΔ; [|contradiction].
    rewrite -wp_bind.
    eapply bi.wand_apply; first by apply bi.wand_entails, wp_store.
    rewrite envs_simple_replace_sound //; simpl.
    rewrite right_id.
    apply bi.sep_mono_r. apply bi.wand_mono; [done|]. exact Hsuc.
  Qed.

  Lemma prim_call_inv f vs σ κ e2 σ2 efs :
    prim_step (Call f (map Val vs)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧
    ((∃ pre post w, fun_entries f = Some (FunSpec pre post) ∧
        pre vs ∧ post vs w ∧ e2 = Val w) ∨
     (∃ params body, fun_entries f = Some (FunDef params body) ∧
        length vs = length params ∧ e2 = subst_list params vs body)).
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H; [
        subst x; inversion H0
      | destruct Ki; simpl in H; discriminate H
      ].
    - destruct K as [|Ki K']; simpl in H.
      + subst x.
        inversion H0 as
          [ | | | | | | |
            f0 vs0 st0 pr po w0 Hfc Hpre Hpost
          | f1 vs1 st1 pars bod Hfc' Hlen ]; subst; simpl.
        * do 3 (split; [done|]); left; eexists _, _, _.
          match goal with Hm : map Val _ = map Val _ |- _ => apply map_Val_inj in Hm as -> end.
          split; [exact Hfc | split; [exact Hpre | split; [exact Hpost | reflexivity]]].
        * do 3 (split; [done|]); right; eexists _, _.
          match goal with Hm : map Val _ = map Val _ |- _ => apply map_Val_inj in Hm as -> end.
          split; [exact Hfc' | split; [exact Hlen | reflexivity]].
      + destruct Ki; simpl in H; discriminate H.
  Qed.

  (** * Opaque call: modular contract reasoning.
      The caller proves the *precondition* and receives the
      *postcondition* for whatever result the callee produces.
      Reducibility follows from the table's total-correctness promise
      [fun_specs_total] — the existence of a result is the callee's
      obligation, not the call site's.  Calling outside the precondition
      is stuck, so WP (NotStuck) enforces the contract. *)
  Lemma wp_call s E f pre post vs Φ :
    fun_entries f = Some (FunSpec pre post) →
    pre vs →
    (∀ w : sn_val, ⌜post vs w⌝ -∗ Φ w) -∗
    WP Call f (map Val vs) @ s; E {{ Φ }}.
  Proof.
    iIntros (Hentry Hpre) "HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      destruct (fun_specs_total f pre post vs Hentry Hpre) as [v Hv].
      eexists (Val v), σ1, []. eapply (PrimHeadStep [] (Call f (map Val vs)) σ1).
      eapply HeadCallSpec; [exact Hentry|exact Hpre|exact Hv]. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    pose proof (prim_call_inv f vs σ1 κ e2 σ2 efs Hprim)
      as (Hκ & Hσ2 & Hefs &
          [(pre' & post' & w & Hentry' & Hpre' & Hpost' & He2)
          | (params & body & Hentry' & _ & _)]);
      last congruence.
    assert (post' = post) as -> by congruence.
    rewrite He2 Hκ Hσ2 Hefs.
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSpecialize ("HΦ" $! w with "[//]").
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  (** * Transparent call: unfold the definition.
      For helper functions without contracts and for testing the lowering:
      the call β-reduces to the body with arguments substituted. *)
  Lemma wp_call_unfold s E f params body vs Φ :
    fun_entries f = Some (FunDef params body) →
    length vs = length params →
    ▷ WP subst_list params vs body @ s; E {{ Φ }} -∗
    WP Call f (map Val vs) @ s; E {{ Φ }}.
  Proof.
    iIntros (Hentry Hlen) "HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      eexists (subst_list params vs body), σ1, [].
      eapply (PrimHeadStep [] (Call f (map Val vs)) σ1).
      eapply HeadCallUnfold; [exact Hentry|exact Hlen]. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    pose proof (prim_call_inv f vs σ1 κ e2 σ2 efs Hprim)
      as (Hκ & Hσ2 & Hefs &
          [(pre & post & w & Hentry' & _ & _)
          | (params' & body' & Hentry' & _ & He2)]);
      first congruence.
    assert (params' = params) as -> by congruence.
    assert (body' = body) as -> by congruence.
    rewrite He2 Hκ Hσ2 Hefs.
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSplitL; [iExact "HΦ" | done].
  Qed.

  (** * Opaque call: ghost-state spec table

      The caller holds [ghost_map_elem γ f (DfracOwn 1) (FunSpec pre post)]
      — a persistent fragment from [ghost_map].  The authoritative
      [ghost_map_auth γ m] lives in an invariant. *)
  Lemma wp_call_ghost γ s E f pre post vs Φ :
    fun_entries f = Some (FunSpec pre post) →
    pre vs →
    ghost_map_elem γ f (DfracOwn 1) (FunSpec pre post) -∗
    (∀ w : sn_val, ⌜post vs w⌝ -∗ Φ w) -∗
    WP Call f (map Val vs) @ s; E {{ Φ }}.
  Proof.
    iIntros (Hentry Hpre) "Hfrag HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      destruct (fun_specs_total f pre post vs Hentry Hpre) as [v Hv].
      eexists (Val v), σ1, [].
      eapply (PrimHeadStep [] (Call f (map Val vs)) σ1).
      eapply HeadCallSpec; [exact Hentry|exact Hpre|exact Hv]. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    pose proof (prim_call_inv f vs σ1 κ e2 σ2 efs Hprim)
      as (Hκ & Hσ2 & Hefs &
          [(pre' & post' & w & Hentry' & Hpre' & Hpost' & He2)
          | (params & body & Hentry' & _ & _)]);
      last congruence.
    assert (post' = post) as -> by congruence.
    rewrite He2 Hκ Hσ2 Hefs.
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSpecialize ("HΦ" $! w with "[//]").
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  (** * While loop with invariant

      Löb induction for loops with mutable state.  The invariant [I]
      is a [Z → iProp Σ] predicate.  The lemma works for loops where
      the condition is simply [z < n] with a counter that starts at 0
      and increases by 1 each iteration.  More general invariants are
      supported by the user providing a custom step function.

      The proof is direct: [iLöb] over the counter [z], then the step
      function is called, which can use the IH via [iApply "IH"]. *)
   Lemma wp_while_inv s E e1 e2 (I : Z → iProp Σ) z Φ :
     I z ∗
     ▷ (∀ z', I z' -∗
       WP If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit) @ s; E {{ Φ }})
     ⊢ WP While e1 e2 @ s; E {{ Φ }}.
   Proof.
     iIntros "[HI Hstep]".
     iApply wp_while; iNext.
     iSpecialize ("Hstep" $! z).
     iDestruct ("Hstep" with "HI") as "Hgoal".
     iExact "Hgoal".
  Qed.

  Lemma wp_for_list_var s E x body (v : sn_val) (M : list sn_val)
      (P : list sn_val -> iProp Σ) (Φ : sn_val -> iProp Σ) :
    v = LitList M ->
    (forall w, subst "_" w body = body) ->
    P M -∗
    (□ ∀ v vs, P (v :: vs) -∗
        WP subst x v body @ s; E {{ _, P vs }}) -∗
    (P [] -∗ Φ LitUnit) -∗
    WP For x (Val v) body @ s; E {{ Φ }}.
  Proof.
    intros -> ?. iApply wp_for_list'; eauto.
  Qed.

  (** Dict-key For-loop WP rules.  Same structure as list For, but the
      iteration binds the KEY (first element of each pair).  The invariant
      [P : list sn_val -> iProp] operates on the *key list* extracted from
      the dict's key-value pairs by [dict_keys]. *)
  Lemma wp_for_dict_nil s E x body Φ :
    ▷ Φ LitUnit -∗
    WP For x (Val (LitDict [])) body @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + apply reducible_no_obs_reducible,
          (reducible_no_obs_pure_step _ _ σ (PureForDictNil x body)).
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_for_dict_nil_det _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_for_dict_nil_det _ _ _ _ _ _ _ Hprim) as [_ [_ [_ He2]]].
      rewrite He2. iApply wp_value'. by iFrame.
  Qed.

  Lemma wp_for_dict_cons s E x k v kvs body Φ :
    ▷ WP Let "_" (subst x k body) (For x (Val (LitDict kvs)) body) @ s; E {{ Φ }} -∗
    WP For x (Val (LitDict ((k, v) :: kvs))) body @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + apply reducible_no_obs_reducible,
          (reducible_no_obs_pure_step _ _ σ (PureForDictCons x k v kvs body)).
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_for_dict_cons_det _ _ _ _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_for_dict_cons_det _ _ _ _ _ _ _ _ _ _ Hprim) as [_ [_ [_ He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  (** Dict-key fold rule.  Induction over the key-value pair list [kvs];
      the invariant [P] holds over the remaining *key list* extracted by
      [dict_keys]. *)
   Lemma wp_for_dict_keys s E x body (kvs : list (sn_val * sn_val))
       (P : list sn_val -> iProp Σ) :
     (forall w, subst "_" w body = body) ->
     P (dict_keys kvs) -∗
     (□ ∀ (k v : sn_val) (rest : list (sn_val * sn_val)),
         P (k :: dict_keys rest) -∗
         WP subst x k body @ s; E {{ _, P (dict_keys rest) }}) -∗
     WP For x (Val (LitDict kvs)) body @ s; E {{ _, P [] }}.
  Proof.
    iIntros (Hclosed) "HP #Hstep".
    iInduction kvs as [|[k v] kvs'] "IH"; simpl.
    - iApply wp_for_dict_nil. by iFrame.
    - iApply wp_for_dict_cons. iNext.
      iApply (wp_bind (fill_item (LetCtx "_" _))).
      iApply (wp_wand with "[HP]").
      { iApply ("Hstep" $! k v kvs' with "HP"). }
      iIntros (w) "HPvs". simpl.
      iApply wp_let. iNext.
      assert (subst "_" w (For x (Val (LitDict kvs')) body)
              = For x (Val (LitDict kvs')) body) as Heq.
      { cbn [subst]. destruct (String.eqb "_" x); by rewrite ?Hclosed. }
      rewrite Heq.
      iApply ("IH" with "HPvs").
  Qed.

  (** Dict-key variant with general postcondition Φ. *)
  Lemma wp_for_dict_keys' s E x body (kvs : list (sn_val * sn_val))
      (P : list sn_val -> iProp Σ) (Φ : sn_val -> iProp Σ) :
    (forall w, subst "_" w body = body) ->
     P (dict_keys kvs) -∗
     (□ ∀ (k v : sn_val) (rest : list (sn_val * sn_val)),
         P (k :: dict_keys rest) -∗
         WP subst x k body @ s; E {{ _, P (dict_keys rest) }}) -∗
     (P [] -∗ Φ LitUnit) -∗
     WP For x (Val (LitDict kvs)) body @ s; E {{ Φ }}.
  Proof.
    iIntros (Hclosed) "HP #Hstep Hpost".
    iInduction kvs as [|[k v] kvs'] "IH"; simpl.
    - iApply wp_for_dict_nil. iNext. by iApply "Hpost".
    - iApply wp_for_dict_cons. iNext.
      iApply (wp_bind (fill_item (LetCtx "_" _))).
      iApply (wp_wand with "[HP]").
      { iApply ("Hstep" $! k v kvs' with "HP"). }
      iIntros (w) "HPvs". simpl.
      iApply wp_let. iNext.
      assert (subst "_" w (For x (Val (LitDict kvs')) body)
              = For x (Val (LitDict kvs')) body) as Heq.
      { cbn [subst]. destruct (String.eqb "_" x); by rewrite ?Hclosed. }
      rewrite Heq.
      iApply ("IH" with "HPvs Hpost").
  Qed.

  (** Automation: repeatedly apply pure WP reductions. *)
  Ltac snakelet_pures :=
    repeat (iApply wp_binop || iApply wp_let || iApply wp_if_true || iApply wp_if_false).

End snakelet_wp.

(** Automation: match the WP goal to extract arguments, then apply the
    lemma explicitly.  Works outside the section. *)
Ltac snakelet_pure_step :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (BinOp ?op (Val ?v1) (Val ?v2)) ?Φ) =>
      iApply (@wp_binop _ _ _ _ _ _ op v1 v2 Φ)
  | |- environments.envs_entails _ (wp _ _ (Let ?x (Val ?v) ?e2) ?Φ) =>
      iApply (@wp_let _ _ _ _ _ _ x v e2 Φ)
  | |- environments.envs_entails _ (wp _ _ (If (Val (LitBool true)) ?e1 ?e2) ?Φ) =>
      iApply (@wp_if_true _ _ _ _ _ _ e1 e2 Φ)
  | |- environments.envs_entails _ (wp _ _ (If (Val (LitBool false)) ?e1 ?e2) ?Φ) =>
      iApply (@wp_if_false _ _ _ _ _ _ e1 e2 Φ)
  end.

Ltac snakelet_pures := repeat snakelet_pure_step.

(** Register [IntoVal] so [wp_value] resolves correctly.  Parametric in
    [FunCtx] so it applies at whatever function table the goal's language
    instance carries. *)
Global Instance into_val_val `{FunCtx} v : IntoVal (Val v) v.
Proof. done. Qed.
