(** Tactics for SnakeletLang: [reshape_expr] + [wp_bind] with auto-inference
    of evaluation contexts, ported from Iris heap_lang's [tactics.v]. *)

From iris.proofmode Require Import proofmode environments.
From iris.program_logic Require Import lifting.
Require Import SnakeletLang.

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
