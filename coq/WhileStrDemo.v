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

  (* Minimal single-cell string-guard loop:
       c = ref "ready";
       while load(c) == "ready": store(c, "done")
       result = load(c)        (* "done" *)
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
    (* Focus the While via the outer Let "_" *)
    iApply (wp_bind_item (LetCtx "_" (Let "result" (Load (Val (LitLoc l))) (Var "result")))); [reflexivity|].
    (* Apply the string-guard while lemma.  Single cell => trivial frame emp. *)
    iApply (wp_while_str l "ready" "ready"
              (Store (Val (LitLoc l)) (Val (LitString "done")))
              emp (fun s' => ⌜s' = "done"⌝%string)%I _ with "[$] [] [] [] []").
    - intros v. reflexivity.   (* Hbc: "_" not free in body *)
    - (* Qfalse: Q s' = (s' = "done") entails guard "ready" falsified *)
      intros s'. iIntros "%Hq". subst s'. iSplit; [done | done].
    - done.                    (* Rpre = emp *)
    - (* body spec: from l ↦ "ready", run [store(l,"done")] => l ↦ "done" *)
      iIntros "Hl _".
      heap_store.
      iExists "done". iFrame. iPureIntro. reflexivity.
    - (* closing wand (after body): Q s' gives s' = "done", reassemble *)
      iIntros (s') "%Hq Hl".
      subst s'.
      unfold bind_post; simpl.
      pure_step.        (* sequencing _ : While returned LitUnit, into Let result *)
      heap_load.        (* result = load(c) = "done" *)
      pure_step.        (* bind result *)
      finish_pure.
    - (* immediate-exit wand: guard was "ready" =? "ready" = true, so this
         path is vacuous (Hf contradictory). *)
      iIntros "%Hf Hl _".
      simpl in Hf. discriminate Hf.
  Qed.
End demo.
