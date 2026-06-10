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

(** * Stage tactics — the instruction set for generated proofs

    The pipeline emits proof scripts as sequences of these tactics, one
    per verification intent (syntax-directed: the SnakeletIR node category
    determines the stage tactic).  Each stage can fail independently with
    a classifiable error message, so the script doubles as the proof
    trace and the failing stage identifies itself by name — no error-dump
    parsing.

    The instruction set:
    - [call_opaque]      — spec'd call: table lookup + precondition +
                           postcondition substitution
    - [call_transparent] — definition call: unfold to substituted body
    - [pure_step]        — one pure reduction (let/binop/literal if)
    - [case_bool]        — path fork on a symbolic boolean (the branch
                           hypothesis becomes a path constraint)
    - [finish_pure]      — terminal stage: value meets the postcondition

    Tactics are argument-light: everything derivable from the goal is
    extracted from the goal ([eval hnf] on the table preserves the named
    pre/post for readable side goals).  Optional [constr] arguments
    (e.g. [call_opaque "square"]) assert the expected redex for drift
    detection between the generator and the goal.

    [snakelet_auto] composes the same instructions for interactive use;
    generated output never calls the monolith. *)

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
    Extend with [first [...]] branches as spec idioms grow.  Obligations
    this cannot solve are exported to SMT by the pipeline; the resulting
    axiom is then supplied explicitly in the generated script. *)
Ltac snakelet_solve_pre :=
  solve [ done
        | by repeat eexists
        | by (repeat eexists; split; [done | lia]) ].

(** Reduce fill/subst redexes and normalize [of_val] back to [Val] so the
    syntactic stage matches fire ([of_val] is introduced by the generic
    [wp_bind] continuation and is not unfolded by [simpl]). *)
Ltac snakelet_simpl := simpl; try (unfold of_val).

(** Introduce the result of an opaque call.  The postcondition is assumed
    deterministic (an equation on the result) in the mechanical fragment:
    substitute and continue.  Nondeterministic posts fail here, rolling
    the stage back for SMT/LLM escalation. *)
Ltac snakelet_intro_post :=
  let w := fresh "w" in
  let Hw := fresh "Hw" in
  iIntros (w Hw); simpl in Hw; subst w; snakelet_simpl.

(** Focus a Let-bound call.  Generated bodies are in ANF, so calls appear
    either in redex position or immediately under a Let binder. *)
Ltac snakelet_focus_call :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Call _ _) _) => idtac
  | |- envs_entails _ (wp _ _ (Let _ (Call ?f ?args) _) _) =>
      wp_bind (Call f args)
  | _ => fail "snakelet_focus_call: no Call in redex position"
  end.

(** Opaque call with a caller-supplied precondition discharge tactic.
    This is the SMT escalation slot: when [snakelet_solve_pre] cannot
    crack a precondition (nonlinear arithmetic, strings), the pipeline
    exports the obligation to SMT and regenerates the stage as
    [call_opaque_pre (exact smt_ax_N)] (or a small wrapper around it). *)
Ltac call_opaque_pre_core pretac :=
  snakelet_focus_call;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Call ?f ?args) _) =>
      let vs := strip_vals args in
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunSpec ?pre ?post) =>
          iApply (wp_call s E f pre post vs);
            [ reflexivity | solve [pretac] | snakelet_intro_post ]
      | Some (FunDef _ _) =>
          fail "call_opaque: function is transparent (FunDef); use call_transparent"
      | None =>
          fail "call_opaque: no table entry for function"
      end
  end.

Ltac call_opaque_core := call_opaque_pre_core snakelet_solve_pre.

Tactic Notation "call_opaque_pre" tactic(t) := call_opaque_pre_core t.

Ltac call_transparent_core :=
  snakelet_focus_call;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Call ?f ?args) _) =>
      let vs := strip_vals args in
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunDef ?params ?body) =>
          iApply (wp_call_unfold s E f params body vs);
            [ reflexivity | reflexivity | iNext; snakelet_simpl ]
      | Some (FunSpec _ _) =>
          fail "call_transparent: function is opaque (FunSpec); use call_opaque"
      | None =>
          fail "call_transparent: no table entry for function"
      end
  end.

Tactic Notation "call_opaque" := call_opaque_core.
Tactic Notation "call_opaque" constr(fname) :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Call fname _) _) => call_opaque_core
  | |- envs_entails _ (wp _ _ (Let _ (Call fname _) _) _) => call_opaque_core
  | _ => fail "call_opaque: goal redex is not a call to the given function"
  end.

Tactic Notation "call_transparent" := call_transparent_core.
Tactic Notation "call_transparent" constr(fname) :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Call fname _) _) => call_transparent_core
  | |- envs_entails _ (wp _ _ (Let _ (Call fname _) _) _) => call_transparent_core
  | _ => fail "call_transparent: goal redex is not a call to the given function"
  end.

(** One pure reduction: let-with-value, binop-with-values, or a literal
    conditional.  Focusing is goal-driven and free — a non-value redex in
    evaluation position is wp_bind'ed automatically, so the generator
    emits exactly one [pure_step] per reduction (per IR node), never bind
    plumbing.  Calls are never focused here: they have their own stage
    tactics. *)
Ltac pure_step :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Let _ (Val _) _) _) =>
      snakelet_pure_step; iNext; snakelet_simpl
  | |- envs_entails _ (wp _ _ (BinOp _ (Val _) (Val _)) _) =>
      snakelet_pure_step; iNext; snakelet_simpl
  | |- envs_entails _ (wp _ _ (If (Val (LitBool true)) _ _) _) =>
      snakelet_pure_step; iNext; snakelet_simpl
  | |- envs_entails _ (wp _ _ (If (Val (LitBool false)) _ _) _) =>
      snakelet_pure_step; iNext; snakelet_simpl
  | |- envs_entails _ (wp _ _ (If (Val (LitBool _)) _ _) _) =>
      fail "pure_step: symbolic condition; use case_bool"
  | |- envs_entails _ (wp _ _ (Call _ _) _) =>
      fail "pure_step: redex is a call; use call_opaque or call_transparent"
  | |- envs_entails _ (wp _ _ (Let _ (Call _ _) _) _) =>
      fail "pure_step: redex is a call; use call_opaque or call_transparent"
  | |- envs_entails _ (wp _ _ (Let _ ?e1 _) _) =>
      wp_bind e1; pure_step
  | |- envs_entails _ (wp _ _ (BinOp _ ?e1 (Val _)) _) =>
      wp_bind e1; pure_step
  | |- envs_entails _ (wp _ _ (BinOp _ _ ?e2) _) =>
      wp_bind e2; pure_step
  | |- envs_entails _ (wp _ _ (If ?e0 _ _) _) =>
      wp_bind e0; pure_step
  | _ => fail "pure_step: no pure redex (let/binop/if with value arguments)"
  end.

(** Path fork on a symbolic boolean condition.  The branch hypothesis
    (e.g. [Z.ltb x 0 = true]) becomes a path constraint available to
    [finish_pure]'s arithmetic.  The generator decides where to split —
    [snakelet_auto] never splits on its own. *)
Ltac case_bool :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (If (Val (LitBool ?b)) _ _) _) =>
      lazymatch b with
      | true => fail "case_bool: condition is literally true; use pure_step"
      | false => fail "case_bool: condition is literally false; use pure_step"
      | _ => let Hcond := fresh "Hcond" in destruct b eqn:Hcond
      end
  | _ => fail "case_bool: goal is not an If on a boolean value"
  end.

(** Convert boolean path constraints into Props for [lia].
    [binop_eval] comparisons produce [bool_decide]; hand-written
    conditions may use [Z.ltb]/[Z.leb]/[Z.eqb] directly. *)
Ltac snakelet_pure_hyps :=
  repeat match goal with
  | H : bool_decide _ = true |- _ => apply bool_decide_eq_true_1 in H
  | H : bool_decide _ = false |- _ => apply bool_decide_eq_false_1 in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
  | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  end.

(** Terminal stage: a value (or an already-pure goal) meets the
    postcondition, using accumulated path constraints. *)
Ltac finish_pure :=
  try (lazymatch goal with
       | |- envs_entails _ (wp _ _ (Val _) _) => iApply wp_value'
       end);
  iPureIntro; snakelet_pure_hyps;
  first [ reflexivity
        | lia
        | done
        | eexists; split; [reflexivity | lia] ].

(** * Interactive composition

    [snakelet_auto] drives the same instruction set for demos and manual
    proofs.  It never case-splits (that is a generator decision), so it
    stops gracefully at symbolic conditionals. *)

Ltac snakelet_call_step :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Call ?f _) _) =>
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunSpec _ _) => call_opaque_core
      | Some (FunDef _ _) => call_transparent_core
      end
  end.

Ltac snakelet_step :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Val _) _) =>
      iApply wp_value'; snakelet_simpl
  | |- envs_entails _ (wp _ _ (Let _ (Val _) _) _) =>
      pure_step
  | |- envs_entails _ (wp _ _ (BinOp _ (Val _) (Val _)) _) =>
      pure_step
  | |- envs_entails _ (wp _ _ (If (Val (LitBool true)) _ _) _) =>
      pure_step
  | |- envs_entails _ (wp _ _ (If (Val (LitBool false)) _ _) _) =>
      pure_step
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
