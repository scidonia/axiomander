(** Tactics for SnakeletLang: [reshape_expr] + [wp_bind] with auto-inference
    of evaluation contexts, ported from Iris heap_lang's [tactics.v], plus
    [snakelet_auto] — a reproducible driver that discharges WP goals over
    straight-line programs (pure steps + chains of opaque/transparent calls)
    without intervention. *)

From iris.proofmode Require Import proofmode environments.
From iris.program_logic Require Import weakestpre lifting.
Require Import SnakeletLang SnakeletWp.

(** [reshape_expr e tac] decomposes [e] into an evaluation context [K]
    and a sub-expression [e'], then calls [tac K e']. *)
Ltac reshape_expr e tac :=
  let rec go K e :=
    lazymatch e with
    | Let ?x (Val ?v) ?e2     => tac K e
    | Let ?x ?e1 ?e2          => go (LetCtx x e2 :: K) e1
    | BinOp ?op (Val ?v1) (Val ?v2) => tac K e
    | BinOp ?op ?e1 (Val ?v2)       => go (BinOpLCtx op v2 :: K) e1
    | BinOp ?op ?e1 ?e2             => go (BinOpRCtx op e1 :: K) e2
    | If (Val _) _ _               => tac K e
    | If ?e0 ?e1 ?e2               => go (IfCtx e1 e2 :: K) e0
    | Load (Val _)                 => tac K e
    | Load ?e                      => go (LoadCtx :: K) e
    | Store (Val ?v1) (Val ?v2)    => tac K e
    | Store ?e1 (Val ?v2)          => go (StoreLCtx v2 :: K) e1
    | Store ?e1 ?e2                => go (StoreRCtx e1 :: K) e2
    | Alloc (Val _)                => tac K e
    | Alloc ?e                     => go (AllocCtx :: K) e
    | FAA (Val ?v1) (Val ?v2)      => tac K e
    | FAA ?e1 (Val ?v2)            => go (FaaLCtx v2 :: K) e1
    | FAA ?e1 ?e2                  => go (FaaRCtx e1 :: K) e2
    | _                        => tac K e
    end
  in go (@nil sn_ectx_item) e.

(** [wp_bind e] (the tactic) finds [e] as a sub-expression of the
    goal's WP expression and uses [wp_bind] (the lemma) to focus on it. *)
Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      lazymatch K with
      | [] => idtac
      | _ =>
          let Ki := fresh "Ki" in
          (* Apply wp_bind for each item: iterate through K *)
          let rec iter_K l :=
            lazymatch l with
            | [] => idtac
            | ?Ki :: ?K' => iApply (wp_bind (fill_item Ki)); simpl; iter_K K'
            end
          in iter_K K
      end
    )
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** * Call-chain automation

    [snakelet_auto] repeatedly applies one of:
    - a pure WP step (let/binop/if with value arguments),
    - [wp_call] / [wp_call_unfold] for a call in redex position
      (the table entry is computed by [hnf], so the FunSpec/FunDef
      names are preserved for readable side goals),
    - [wp_bind] to focus a call (or other redex) in evaluation position,
    - [wp_value'] when the program is a value,
    and finishes pure postcondition goals with reflexivity/lia.

    Precondition obligations are discharged by [snakelet_solve_pre], which
    handles the simple shapes (existentially quantified argument lists with
    optional linear-arithmetic side conditions).  Postconditions are assumed
    deterministic (an equation on the result) in simple cases — the result
    is substituted and the chain continues.  If any sub-step fails (e.g. a
    nondeterministic postcondition or an unprovable precondition), that
    whole step rolls back and the goal is left at the call for manual
    treatment — earlier progress is kept. *)

(** Convert a syntactic list of value expressions [[Val v1; ...; Val vn]]
    to the value list [[v1; ...; vn]] (so [Call f args] matches the
    [Call f (map Val vs)] shape of the call lemmas). *)
Ltac strip_vals args :=
  lazymatch args with
  | nil => constr:(@nil sn_val)
  | Val ?v :: ?rest => let r := strip_vals rest in constr:(v :: r)
  end.

(** Solve simple precondition obligations: existentially quantified
    argument shapes with optional linear-arithmetic side conditions.
    Extend with [first [...]] branches as spec idioms grow. *)
Ltac snakelet_solve_pre :=
  solve [ done
        | by eexists
        | by (eexists; split; [done | lia]) ].

(** Reduce fill/subst redexes and normalize [of_val] back to [Val] so the
    syntactic matches in [snakelet_step] fire ([of_val] is introduced by
    the generic [wp_bind] continuation). *)
Ltac snakelet_simpl := simpl; try (unfold of_val).

Ltac snakelet_call_step :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Call ?f ?args) ?Q) =>
      let vs := strip_vals args in
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunDef ?params ?body) =>
          iApply (wp_call_unfold s E f params body vs);
            [ reflexivity | reflexivity | iNext; snakelet_simpl ]
      | Some (FunSpec ?pre ?post) =>
          iApply (wp_call s E f pre post vs);
            [ reflexivity
            | snakelet_solve_pre
            | let w := fresh "w" in
              let Hw := fresh "Hw" in
              iIntros (w Hw); simpl in Hw; subst w; snakelet_simpl ]
      end
  end.

Ltac snakelet_step :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Val _) _) =>
      iApply wp_value'; snakelet_simpl
  | |- envs_entails _ (wp _ _ (Let _ (Val _) _) _) =>
      snakelet_pure_step; iNext; snakelet_simpl
  | |- envs_entails _ (wp _ _ (BinOp _ (Val _) (Val _)) _) =>
      snakelet_pure_step; iNext; snakelet_simpl
  | |- envs_entails _ (wp _ _ (If (Val (LitBool _)) _ _) _) =>
      snakelet_pure_step; iNext; snakelet_simpl
  | |- envs_entails _ (wp _ _ (Call _ _) _) =>
      snakelet_call_step
  | |- envs_entails _ (wp _ _ (Let _ ?e1 _) _) =>
      wp_bind e1
  | |- envs_entails _ (wp _ _ (BinOp _ ?e1 (Val _)) _) =>
      wp_bind e1
  | |- envs_entails _ (wp _ _ (BinOp _ _ ?e2) _) =>
      wp_bind e2
  | |- envs_entails _ (wp _ _ (If ?e0 _ _) _) =>
      wp_bind e0
  end.

Ltac snakelet_auto :=
  iStartProof;
  repeat snakelet_step;
  try (iPureIntro; first [reflexivity | lia | done]).
