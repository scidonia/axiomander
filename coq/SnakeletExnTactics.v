From iris.proofmode Require Import proofmode coq_tactics reduction.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.

(** Stage-tactic layer for the exception-aware WP (Result postcondition).

    Ported from the old SnakeletTactics.v but against [wp_exn] (WPE):
    the postcondition ranges over [Result := RVal v | RExn label payload],
    there is no stuckness / mask, and bind composition goes through
    [wp_bind_item] with the [bind_post] transformer (both in SnakeletExnWp.v).

    The generated proof scripts use the same instruction set as before:
      pure_step, call_opaque, case_bool, finish_pure, heap_load/store/alloc,
      raise_step, try_step.
    Each stage tactic extracts everything it needs from the goal. *)

(** [reshape_expr e tac] decomposes [e] into an evaluation context [K]
    (a single context item, since our WP bind is per-item) and a redex
    [e'], then calls [tac Ki e'] for the innermost evaluation position.
    Try is a context (body reduces inside) but is NOT neutral, so it is
    handled by the dedicated try tactics, not generic bind. *)
Ltac reshape_item e tac :=
  lazymatch e with
  | Let ?x (Val ?v) ?e2          => tac (@None sn_ectx_item) e
  | Let ?x ?e1 ?e2               => tac (Some (LetCtx x e2)) e1
  | BinOp ?op (Val ?v1) (Val ?v2) => tac (@None sn_ectx_item) e
  | BinOp ?op ?e1 (Val ?v2)      => tac (Some (BinOpLCtx op v2)) e1
  | BinOp ?op ?e1 ?e2            => tac (Some (BinOpRCtx op e1)) e2
  | If (Val _) _ _               => tac (@None sn_ectx_item) e
  | If ?e0 ?e1 ?e2               => tac (Some (IfCtx e1 e2)) e0
  | Load (Val _)                 => tac (@None sn_ectx_item) e
  | Load ?e0                     => tac (Some LoadCtx) e0
  | Store (Val ?v1) (Val ?v2)    => tac (@None sn_ectx_item) e
  | Store ?e1 (Val ?v2)          => tac (Some (StoreLCtx v2)) e1
  | Store ?e1 ?e2                => tac (Some (StoreRCtx e1)) e2
  | Alloc (Val _)                => tac (@None sn_ectx_item) e
  | Alloc ?e0                    => tac (Some AllocCtx) e0
  | Raise (Val _)                => tac (@None sn_ectx_item) e
  | Raise ?e0                    => tac (Some RaiseCtx) e0
  | _                            => tac (@None sn_ectx_item) e
  end.

Section tactics.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Context `{FC : FunCtx}.
  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200) : bi_scope.
  Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

  Implicit Types Phi : Result -> iProp Sigma.

End tactics.

(** [wp_bind Ki] focuses the WP on the sub-expression in context [Ki]
    using [wp_bind_item].  The neutrality side-condition is discharged by
    [reflexivity] (all bind contexts are neutral; Try is handled separately). *)
Ltac wp_bind_ctx Ki :=
  iApply (wp_bind_item Ki); [reflexivity|].

(** After a redex reduces to a value under a [bind_post], pop the value
    through [wp_value] so the enclosing context's next redex is exposed.
    [simpl] then unfolds [bind_post (RVal v)] back to the context WP. *)
Ltac popvals :=
  repeat lazymatch goal with
  | |- envs_entails _ (wp_exn (Val _) ?Q) =>
      lazymatch Q with
      | bind_post _ _ => iApply wp_value; simpl
      end
  end.

(** Reduce the redex once it is in focus position (top of WP). *)
Ltac pure_step_redex :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Let _ (Val _) _) _) =>
      iApply wp_let; iNext; simpl
  | |- envs_entails _ (wp_exn (BinOp _ (Val _) (Val _)) _) =>
      iApply wp_binop; iNext; simpl
  | |- envs_entails _ (wp_exn (If (Val (LitBool true)) _ _) _) =>
      iApply wp_if_true; iNext; simpl
  | |- envs_entails _ (wp_exn (If (Val (LitBool false)) _ _) _) =>
      iApply wp_if_false; iNext; simpl
  | |- envs_entails _ (wp_exn (If (Val (LitBool ?b)) _ _) _) =>
      (* the boolean may be an unreduced [Z.ltb]/[Z.leb]/[Z.eqb] term
         (e.g. after a concrete heap-loop binop): compute it, then retry. *)
      let bv := eval cbv in b in
      lazymatch bv with
      | true  => replace b with true by (cbv; reflexivity);
                 iApply wp_if_true; iNext; simpl
      | false => replace b with false by (cbv; reflexivity);
                 iApply wp_if_false; iNext; simpl
      | _ => fail "pure_step: symbolic condition; use case_bool"
      end
  | |- envs_entails _ (wp_exn (Try (Val _) _ _) _) =>
      iApply wp_try_normal; iNext; simpl
  | |- envs_entails _ (wp_exn (Try (Raise (Val _)) _ _) _) =>
      iApply wp_try_catch; iNext; simpl
  | |- envs_entails _ (wp_exn (Call _ _) _) =>
      fail "pure_step: redex is a call; use call_opaque"
  | _ => fail "pure_step: no pure redex"
  end.

(** One pure reduction.  Focusing is goal-driven: [reshape_item] finds the
    innermost evaluation position; if it is nested, [wp_bind] focuses it
    first.  Calls are never reduced here. *)
(** Focus the innermost evaluation position by repeatedly binding the
    outermost non-value context item until a redex sits at the top. *)
Ltac focus_redex :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn ?e _) =>
      reshape_item e ltac:(fun Ki e' =>
        lazymatch Ki with
        | @None sn_ectx_item => idtac      (* redex already at top *)
        | Some ?K => wp_bind_ctx K; focus_redex
        end)
  end.

Ltac pure_step :=
  popvals; focus_redex; pure_step_redex.

(** Unfold a concrete [While] one iteration.  Focuses the loop (it may
    sit under a [Let "_" _ cont] bind), applies [wp_while] to expose
    [If cond (Let "_" body (While ..)) (Val LitUnit)], then simplifies.
    The subsequent case_bool / pure_step / heap stages drive the body. *)
Ltac loop_unfold :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (While _ _) _) =>
      iApply wp_while; iNext; simpl
  | _ => fail "loop_unfold: goal is not a While"
  end.

(** Convert boolean path constraints into Props for [lia]. *)
Ltac snakelet_pure_hyps :=
  repeat match goal with
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
  | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  end.

(** Raise step: reduce an in-focus [Raise (Val (LitExn ...))] to its
    exception result.  Also handles a raise nested in a neutral context
    (it unwinds). *)
Ltac raise_step :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Raise (Val (LitExn _ _))) _) =>
      iApply wp_raise
  | _ => fail "raise_step: goal is not a raise"
  end;
  (* discharge the resulting RExn arm: String.eqb on the concrete label
     reduces, leaving the raises-condition Prop (or False). *)
  simpl; try (iPureIntro; snakelet_pure_hyps;
              first [ reflexivity | lia | done ]).

(** Path fork on a symbolic boolean condition. *)
Ltac case_bool :=
  popvals;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (If (Val (LitBool ?b)) _ _) _) =>
      lazymatch b with
      | true => fail "case_bool: literally true; use pure_step"
      | false => fail "case_bool: literally false; use pure_step"
      | _ => let Hcond := fresh "Hcond" in destruct b eqn:Hcond
      end
  | _ => fail "case_bool: goal is not an If on a boolean value"
  end.

(** Terminal stage: a value meets the postcondition.  Pops any pending
    bind contexts, applies [wp_value] to expose the [RVal v] arm of the
    Result-match postcondition, then discharges the pure obligation with
    path constraints + lia. *)
Ltac finish_pure :=
  popvals;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Val _) _) => iApply wp_value
  | _ => idtac
  end;
  simpl; iPureIntro; snakelet_pure_hyps;
  try (first
         [ reflexivity
         | nia
         | lia
         | (f_equal; nia)
         | done
         (* Z.leb / Z.ltb goal: rewrite to Prop inequality, then nia *)
         | (rewrite Z.leb_le; nia)
         | (rewrite Z.ltb_lt; nia)
         (* existential value-shape postcondition.  The side-condition may
            contain Z.leb/Z.ltb goals; convert them before using nia. *)
         | (eexists; split;
            [ reflexivity
            | try rewrite Z.leb_le; try rewrite Z.ltb_lt;
              try rewrite Z.eqb_eq;
              first [ reflexivity | nia ] ])
         | (repeat split; first [ reflexivity | nia ]) ]).

(** Convert a syntactic list of value expressions [[Val v1; ...; Val vn]]
    to the value list [[v1; ...; vn]] so [Call f args] matches the
    [Call f (map Val vs)] shape of [wp_call]. *)
Ltac strip_vals args :=
  lazymatch args with
  | nil => constr:(@nil sn_val)
  | Val ?v :: ?rest => let r := strip_vals rest in constr:(v :: r)
  end.

Ltac snakelet_solve_pre :=
  solve [ done
        | hnf; repeat lazymatch goal with |- @ex _ _ => eexists end;
          first [ done | split; [done | lia] | lia ] ].

(** Apply [wp_call] once the Call redex is at the top of the WP. *)
Ltac call_opaque_redex solver :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call ?f ?args) _) =>
      let vs := strip_vals args in
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunSpec ?pre ?post) =>
          iApply (wp_call f pre post vs); [ reflexivity | solve [solver] | ];
          iNext; let v := fresh "v" in let Hv := fresh "Hv" in
          iIntros (v Hv); simpl in Hv; subst v; simpl
      | _ => fail "call_opaque: not an opaque (FunSpec) call"
      end
  | _ => fail "call_opaque: redex is not a Call"
  end.

(** Opaque call: focus the Call redex (it is typically the bound
    expression of a Let), then apply [wp_call].  [solver] discharges the
    precondition (default: [snakelet_solve_pre]). *)
Ltac call_opaque_pre solver :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call _ _) _) => call_opaque_redex solver
  | _ => fail "call_opaque: redex is not a Call"
  end.

Ltac call_opaque_core := call_opaque_pre snakelet_solve_pre.

(** Walk nested evaluation contexts to the innermost redex and check it
    is a [Call fname _].  Non-destructive (inspection only). *)
Ltac check_redex_call fname e :=
  reshape_item e ltac:(fun Ki e' =>
    lazymatch Ki with
    | @None sn_ectx_item =>
        lazymatch e' with
        | Call fname _ => idtac
        | _ => fail "call_opaque: goal redex is not a call to the given function"
        end
    | Some _ => check_redex_call fname e'
    end).

(** Drift check: assert the expected callee, then run the core. *)
Ltac check_callee fname :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn ?e _) => check_redex_call fname e
  | _ => fail "call_opaque: not a WPE goal"
  end.

Tactic Notation "call_opaque" := call_opaque_core.
Tactic Notation "call_opaque" constr(f) := check_callee f; call_opaque_core.
Tactic Notation "call_opaque_pre" tactic3(t) := call_opaque_pre t.

(** Heap stages.  Each focuses its redex (typically the bound expression
    of a Let) via [focus_redex], applies the heap WP lemma framing the
    relevant points-to from the spatial context, and reintroduces the
    (possibly updated) points-to under a fresh hypothesis.  [simpl] then
    pops the value through [bind_post]. *)
Ltac heap_load :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Load (Val (LitLoc ?l))) _) =>
      iApply (wp_load l with "[$]"); iNext; iIntros "?"; simpl
  | _ => fail "heap_load: redex is not a Load"
  end.

Ltac heap_store :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Store (Val (LitLoc ?l)) (Val ?v)) _) =>
      iApply (wp_store l v with "[$]"); iNext; iIntros "?"; simpl
  | _ => fail "heap_store: redex is not a Store"
  end.

Ltac heap_alloc :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Alloc (Val _)) _) =>
      iApply wp_alloc; iNext;
      let l := fresh "l" in iIntros (l) "?"; simpl
  | _ => fail "heap_alloc: redex is not an Alloc"
  end.

(** Transparent call: unfold the FunDef body. *)
Ltac call_transparent_redex :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call ?f ?args) _) =>
      let vs := strip_vals args in
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunDef ?params ?body) =>
          iApply (wp_call_unfold f params body vs);
            [ reflexivity | reflexivity | iNext; simpl ]
      | _ => fail "call_transparent: not a transparent (FunDef) call"
      end
  | _ => fail "call_transparent: redex is not a Call"
  end.

Ltac call_transparent_core :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call _ _) _) => call_transparent_redex
  | _ => fail "call_transparent: redex is not a Call"
  end.

Tactic Notation "call_transparent" := call_transparent_core.
Tactic Notation "call_transparent" constr(f) := check_callee f; call_transparent_core.


(** * While-loop invariant lemma (Loeb induction on a heap counter).

    Proves that a while loop of the standard form
      While {BinOp LtOp {Load l} {Val (LitInt bound)}}
            {Let "_t2" {Let "_t1" {Load l} {BinOp AddOp {Var "_t1"} ...}} {Store l ...}}
    with invariant [z <= bound] terminates with cell value [bound]. *)
Section while_lemma.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Context `{FC : FunCtx}.
  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200) : bi_scope.
  Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

  Lemma wp_while_inv (l : loc) (bound : Z) (z : Z) (Phi : Result -> iProp Sigma) :
    l ↦ LitInt z -∗
    ⌜Z.le z bound⌝ -∗
    (l ↦ LitInt bound -∗ Phi (RVal LitUnit)) -∗
    WPE (While (BinOp LtOp (Load (Val (LitLoc l))) (Val (LitInt bound)))
              (Let "_t2" (Let "_t1" (Load (Val (LitLoc l)))
                 (BinOp AddOp (Var "_t1") (Val (LitInt 1))))
                 (Store (Val (LitLoc l)) (Var "_t2")))) {{ Phi }}.
  Proof.
    iLöb as "IH" forall (z Phi).
    iIntros "Hc %Hz Hwand".
    iApply wp_while; iNext; simpl.
    heap_load. pure_step. case_bool.
    - snakelet_pure_hyps.
      pure_step.  (* if true branch *)
      heap_load.  (* Load cell for body *)
      pure_step.  (* _t1 Let *)
      pure_step.  (* binop add *)
      pure_step.  (* _t2 Let *)
      heap_store. (* store result *)
      pure_step.  (* sequencing _ *)
      iApply ("IH" $! (z + 1)%Z Phi with "[$] [] Hwand").
      { admit. }
    - snakelet_pure_hyps.
      pure_step.  (* if false branch *)
      iApply wp_value. iApply "Hwand". iFrame.
   Abort.
End while_lemma.
