From iris.proofmode Require Import proofmode coq_tactics reduction.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp SnakeletExnTactics.
Open Scope Z_scope.

Definition gen_table (f : string) : option fun_entry := None.

Lemma gen_table_total : forall f pre post vs,
  gen_table f = Some (FunSpec pre post) -> pre vs -> exists v, post vs v.
Proof. intros f pre post vs Hf. unfold gen_table in Hf. discriminate Hf. Qed.

#[global] Instance gen_fun_ctx : FunCtx :=
  {| fun_entries := gen_table; fun_specs_total := gen_table_total |}.

Section demo.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200) : bi_scope.
  Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

  (* The loop invariant for a guard-changing loop is PATH-DEPENDENT:
     when the guard cell still reads "ready" we are at the start; once it
     reads anything else it must read "done".  Indexed by the guard value. *)
  Definition demo_inv (s : string) : iProp Sigma :=
    (⌜s = "ready" \/ s = "done"⌝)%I.

  (* ---- BODY OBLIGATION: a SEPARATE, NAMED lemma ---------------------
     The Hoare triple for one body run, guard true (cell reads "ready"):
       {l ↦ "ready" * demo_inv "ready"}
         store(l, "done")
       {∃ s', l ↦ s' * demo_inv s' * eqb s' "ready" = false}
     This is proved on its own and consumed by the loop rule below. *)
  Lemma demo_body_spec (l : loc) :
    l ↦ LitString "ready" -∗ demo_inv "ready" -∗
    WPE (Store (Val (LitLoc l)) (Val (LitString "done")))
      {{ (fun r => match r with
          | RVal _ => ∃ s', l ↦ LitString s' ∗ demo_inv s' ∗ ⌜String.eqb s' "ready" = false⌝
          | RExn lbl p => False
          end)%I }}.
  Proof.
    iIntros "Hl _".
    heap_store.
    iExists "done". iFrame. iSplit.
    - iPureIntro. right. reflexivity.    (* demo_inv "done" *)
    - iPureIntro. reflexivity.           (* eqb "done" "ready" = false *)
  Qed.

  (* ---- LOOP: applies wp_while_str, FEEDING IN the body lemma --------
       c = ref "ready";
       while load(c) == "ready": store(c, "done")
       result = load(c)
     Postcondition: result = "done". *)
  Lemma demo_str_loop :
    ⊢ WPE
      (Let "c" (Alloc (Val (LitString "ready")))
      (Let "_"
        (While (BinOp EqOp (Load (Var "c")) (Val (LitString "ready")))
          (Store (Var "c") (Val (LitString "done"))))
      (Let "result" (Load (Var "c")) (Var "result"))))
      {{ (fun r => match r with
          | RVal v => ⌜exists s : string, v = LitString s /\ String.eqb s "done" = true⌝
          | RExn _ _ => False end)%I }}.
  Proof.
    iStartProof.
    heap_alloc.  (* fresh location l for c *)
    pure_step.   (* bind "c" *)
    iApply (wp_bind_item (LetCtx "_" (Let "result" (Load (Val (LitLoc l))) (Var "result")))); [reflexivity|].
    (* Apply the Hoare loop rule.  Initial invariant demo_inv "ready". *)
    iApply (wp_while_str l "ready" "ready"
              (Store (Val (LitLoc l)) (Val (LitString "done")))
              demo_inv _ with "[$] [] [] []").
    - intros v. reflexivity.            (* Hbc: "_" not free in body *)
    - iPureIntro. left. reflexivity.    (* demo_inv "ready" *)
    - (* body obligation: discharged by the NAMED lemma, no inline body proof *)
      iApply demo_body_spec.
    - (* closing wand: guard-false sf with demo_inv sf gives sf = "done" *)
      iIntros (sf) "%Hsf Hl %Hinv".
      assert (sf = "done") as ->.
      { destruct Hinv as [-> | ->]; [discriminate Hsf | reflexivity]. }
      unfold bind_post; simpl.
      pure_step.        (* sequencing _ : While -> Let result *)
      heap_load.        (* result = load(c) = "done" *)
      pure_step.        (* bind result *)
      finish_pure.
  Qed.
End demo.
