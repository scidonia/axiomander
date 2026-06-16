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
  | |- envs_entails _ (wp_exn (If (Val (LitBool _)) _ _) _) =>
      fail "pure_step: symbolic condition; use case_bool"
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
Ltac pure_step :=
  popvals;
  lazymatch goal with
  | |- envs_entails _ (wp_exn ?e _) =>
      reshape_item e ltac:(fun Ki e' =>
        lazymatch Ki with
        | @None sn_ectx_item => pure_step_redex
        | Some ?K =>
            lazymatch e' with
            | Call _ _ => fail "pure_step: redex is a call; use call_opaque"
            | _ => wp_bind_ctx K; pure_step_redex
            end
        end)
  | _ => fail "pure_step: not a WPE goal"
  end.

(** Raise step: reduce an in-focus [Raise (Val (LitExn ...))] to its
    exception result.  Also handles a raise nested in a neutral context
    (it unwinds). *)
Ltac raise_step :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Raise (Val (LitExn _ _))) _) =>
      iApply wp_raise
  | |- envs_entails _ (wp_exn (Let _ (Raise (Val (LitExn _ _))) _) _) =>
      iApply wp_let_raise_unwind
  | _ => fail "raise_step: goal is not a raise"
  end.

(** Path fork on a symbolic boolean condition. *)
Ltac case_bool :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (If (Val (LitBool ?b)) _ _) _) =>
      lazymatch b with
      | true => fail "case_bool: literally true; use pure_step"
      | false => fail "case_bool: literally false; use pure_step"
      | _ => let Hcond := fresh "Hcond" in destruct b eqn:Hcond
      end
  | _ => fail "case_bool: goal is not an If on a boolean value"
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
  try (first [ reflexivity | lia | (f_equal; lia) | done ]).

(** Convert a syntactic list of value expressions [[Val v1; ...; Val vn]]
    to the value list [[v1; ...; vn]] so [Call f args] matches the
    [Call f (map Val vs)] shape of [wp_call]. *)
Ltac strip_vals args :=
  lazymatch args with
  | nil => constr:(@nil sn_val)
  | Val ?v :: ?rest => let r := strip_vals rest in constr:(v :: r)
  end.

(** Opaque call: apply [wp_call] with the table-derived pre/post.  The
    precondition [pre vs] is discharged by [solver] (default: existential
    shape + lia); the postcondition is introduced and substituted. *)
Ltac call_opaque_pre solver :=
  popvals;
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
  | _ => fail "call_opaque: goal is not a Call"
  end.

Ltac snakelet_solve_pre :=
  solve [ done
        | hnf; repeat lazymatch goal with |- @ex _ _ => eexists end;
          first [ done | split; [done | lia] | lia ] ].

Ltac call_opaque := call_opaque_pre snakelet_solve_pre.

(** Heap stages. *)
Ltac heap_load :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Load (Val (LitLoc _))) _) =>
      iApply (wp_load with "[$]"); iNext
  | _ => fail "heap_load: goal is not a Load"
  end.

Ltac heap_store :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Store (Val (LitLoc _)) (Val _)) _) =>
      iApply (wp_store with "[$]"); iNext
  | _ => fail "heap_store: goal is not a Store"
  end.
