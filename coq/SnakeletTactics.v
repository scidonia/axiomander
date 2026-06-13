(** Tactics for SnakeletLang: [reshape_expr] + [wp_bind] with auto-inference
    of evaluation contexts, ported from Iris heap_lang's [tactics.v], plus
    [snakelet_auto] — a reproducible driver that discharges WP goals over
    straight-line programs (pure steps + chains of opaque/transparent calls)
    without intervention. *)

From iris.proofmode Require Import proofmode environments coq_tactics reduction.
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
    | BinOp ?op (Val ?v1) ?e2       => go (BinOpRCtx op v1 :: K) e2
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
          (* [reshape_expr] accumulates K innermost-first; the wp_bind
             lemma must be applied outermost-first, so recurse on the
             tail before applying the head. *)
          let rec iter_K l :=
            lazymatch l with
            | [] => idtac
            | ?Ki :: ?K' => iter_K K'; iApply (wp_bind (fill_item Ki)); simpl
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
(** Note: [eexists] applies to any single-constructor inductive — on a
    conjunction it splits and on an equality it unify-solves — so a bare
    [repeat eexists] overreaches.  Strip only genuine [ex] goals, then
    dispatch on what remains. *)
Ltac snakelet_solve_pre :=
  solve [ done
        | hnf; repeat lazymatch goal with |- @ex _ _ => eexists end;
          first [ done
                | split; [done | lia]
                | lia ] ].

(** Reduce fill/subst redexes and normalize [of_val] back to [Val] so the
    syntactic stage matches fire ([of_val] is introduced by the generic
    [wp_bind] continuation and is not unfolded by [simpl]).  [cbn] is
    included because [simpl] does not reduce concrete arithmetic inside
    value constructors (LitInt (0 + 1) stays unreduced under simpl). *)
Ltac snakelet_simpl := simpl; cbn; try (unfold of_val).

(** Pop leftover value-WP layers introduced by nested wp_bind
    continuations ([WP Val v {{ w, WP ... }}]).  Every stage tactic
    normalizes these away first, so generated scripts never contain
    explicit [iApply wp_value'] plumbing and are insensitive to how
    many bind layers an earlier stage stacked. *)
Ltac snakelet_popvals :=
  repeat lazymatch goal with
  | |- envs_entails _ (wp _ _ (Val _) _) =>
      iApply wp_value'; snakelet_simpl
  end.

(** Introduce the result of an opaque call.  The postcondition is assumed
    deterministic (an equation on the result) in the mechanical fragment:
    substitute and continue.  Nondeterministic posts fail here, rolling
    the stage back for SMT/LLM escalation. *)
Ltac snakelet_intro_post :=
  let w := fresh "w" in
  let Hw := fresh "Hw" in
  iIntros (w Hw); simpl in Hw; subst w; snakelet_simpl.

(** Focus a call in evaluation position: [reshape_expr] locates the
    innermost redex along the evaluation-context spine; if it is a Call,
    wp_bind it. *)
Ltac snakelet_focus_call :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Call _ _) _) => idtac
  | |- envs_entails _ (wp _ _ ?e _) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch e' with
        | Call ?f ?args => wp_bind (Call f args)
        | _ => fail "snakelet_focus_call: redex is not a call"
        end)
  | _ => fail "snakelet_focus_call: not a WP goal"
  end.

(** Opaque call with a caller-supplied precondition discharge tactic.
    This is the SMT escalation slot: when [snakelet_solve_pre] cannot
    crack a precondition (nonlinear arithmetic, strings), the pipeline
    exports the obligation to SMT and regenerates the stage as
    [call_opaque_pre (exact smt_ax_N)] (or a small wrapper around it). *)
Ltac call_opaque_pre_core pretac :=
  snakelet_popvals;
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
  snakelet_popvals;
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

(** The named variants assert the expected callee (drift detection
    between generator and goal): the evaluation-position redex must be a
    call to [fname]. *)
Ltac snakelet_check_callee fname :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Call fname _) _) => idtac
  | |- envs_entails _ (wp _ _ ?e _) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch e' with
        | Call fname _ => idtac
        | _ => fail "goal redex is not a call to the given function"
        end)
  | _ => fail "not a WP goal"
  end.

Tactic Notation "call_opaque" := call_opaque_core.
Tactic Notation "call_opaque" constr(fname) :=
  snakelet_check_callee fname; call_opaque_core.

Tactic Notation "call_transparent" := call_transparent_core.
Tactic Notation "call_transparent" constr(fname) :=
  snakelet_check_callee fname; call_transparent_core.

(** Reduce the redex once it is in focus position. *)
Ltac pure_step_redex :=
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
  | _ => fail "pure_step: no pure redex (let/binop/if with value arguments)"
  end.

(** One pure reduction: let-with-value, binop-with-values, or a literal
    conditional.  Focusing is goal-driven and free — [reshape_expr]
    locates the innermost redex along the evaluation-context spine and
    wp_bind's it, so the generator emits exactly one [pure_step] per
    reduction (per IR node), never bind plumbing.  Calls are never
    reduced here: they have their own stage tactics. *)
Ltac pure_step :=
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?e _) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch K with
        | nil => pure_step_redex
        | _ =>
            lazymatch e' with
            | Call _ _ =>
                fail "pure_step: redex is a call; use call_opaque or call_transparent"
            | _ => wp_bind e'; pure_step_redex
            end
        end)
  | _ => fail "pure_step: not a WP goal"
  end.

(** Path fork on a symbolic boolean condition.  The branch hypothesis
    (e.g. [Z.ltb x 0 = true]) becomes a path constraint available to
    [finish_pure]'s arithmetic.  The generator decides where to split —
    [snakelet_auto] never splits on its own. *)
Ltac case_bool :=
  snakelet_popvals;
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
  snakelet_popvals;
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

(** * Heap operations

    Location-keyed stage tactics (heap_lang style).  Load and store go
    through the environment-form lemmas [tac_wp_load]/[tac_wp_store]:
    the location is extracted from the goal expression by
    [reshape_expr], and [iAssumptionCore] finds the points-to
    hypothesis by *unification on that concrete location* — never by
    name.  Store updates the hypothesis in place (it keeps its name).
    Alloc introduces an anonymously-named cell; nothing downstream
    refers to it by name.

    Consequence: generated proof scripts contain only bare
    [heap_alloc]/[heap_store]/[heap_load] stages — no hypothesis names,
    no locations — so small program variations (extra cells, renamed
    variables, different constants) leave the stage sequence
    unchanged. *)

Ltac heap_alloc :=
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?e _) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch e' with
        | Alloc (Val _) =>
            wp_bind e'; iApply wp_alloc;
            let l := fresh "l" in iIntros (l) "?"; snakelet_simpl
        | _ => fail "heap_alloc: redex is not an Alloc"
        end)
  | _ => fail "heap_alloc: goal is not a WP"
  end.

(** Variant that names the points-to hypothesis explicitly, so
    [iLöb as "IH" forall "name"] can refer to it. *)
Ltac heap_alloc_named s :=
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ ?e _) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch e' with
        | Alloc (Val _) =>
            wp_bind e'; iApply wp_alloc;
            let l := fresh "l" in iIntros (l) s; snakelet_simpl
        | _ => fail "heap_alloc_named: redex is not an Alloc"
        end)
  | _ => fail "heap_alloc_named: goal is not a WP"
  end.

(** [reshape_expr] accumulates the evaluation context innermost-first,
    but [fill_K] is head-outermost — reverse before passing to the
    environment-form lemmas. *)
Ltac rev_ectx K acc :=
  lazymatch K with
  | nil => acc
  | ?Ki :: ?K' => rev_ectx K' constr:(Ki :: acc)
  end.

Ltac heap_store :=
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch e' with
        | Store (Val (LitLoc _)) (Val _) =>
            let K' := rev_ectx K (@nil sn_ectx_item) in
            eapply (tac_wp_store _ s E _ K');
            [iAssumptionCore | pm_reduce; snakelet_simpl]
        | _ => fail "heap_store: redex is not a Store"
        end)
  | _ => fail "heap_store: goal is not a WP"
  end.

Ltac heap_load :=
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch e' with
        | Load (Val (LitLoc _)) =>
            let K' := rev_ectx K (@nil sn_ectx_item) in
            eapply (tac_wp_load _ s E _ K');
            [iAssumptionCore | snakelet_simpl]
        | _ => fail "heap_load: redex is not a Load"
        end)
  | _ => fail "heap_load: goal is not a WP"
  end.

(** * While loop unfolding

    [loop_unfold] applies [wp_while] to unfold the loop one iteration,
    revealing [If cond (body ;; While cond body) LitUnit].  The
    subsequent [case_bool] / [pure_step] / [finish_pure] stages handle
    the branches.  Loop invariants are at the proof-script level:
    the generator supplies the invariant as a hypothesis before each
    iteration; here we just provide the structural step. *)

(** Symbolic loop entry point.  [loop_inv I z] introduces [wp_while_inv]
    with invariant [I] at initial index [z], extracting [e1], [e2], and
    [Φ] directly from the WP goal so that variable substitutions from
    earlier [pure_step] stages do not block matching. *)
Ltac loop_inv_tac I z :=
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (While ?e1 ?e2) ?Φ) =>
      iApply (wp_while_inv _ _ e1 e2 I z Φ)
  | |- envs_entails _ (wp _ _ ?e _) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch e' with
        | While _ _ => wp_bind e'; loop_inv_tac I z
        | _ => fail "loop_inv: redex is not a While"
        end)
  | _ => fail "loop_inv: goal is not a WP"
  end.

Tactic Notation "loop_inv" uconstr(I) uconstr(z) := loop_inv_tac I z.

Ltac loop_unfold :=
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (While _ _) _) =>
      iApply wp_while; iNext; snakelet_simpl
  | |- envs_entails _ (wp _ _ ?e _) =>
      reshape_expr e ltac:(fun K e' =>
        lazymatch e' with
        | While _ _ => wp_bind e'; loop_unfold
        | _ => fail "loop_unfold: redex is not a While"
        end)
  | _ => fail "loop_unfold: goal is not a WP"
  end.

(** Focus a symbolic while loop and apply its per-loop lemma.
    Called by the generator as: [loop_inv_call lemma_name l bound exit_cont]. *)
(** [focus_while] focuses onto a While sub-expression inside an
    evaluation context (e.g. [;; Load c]), so that the next stage
    can call a per-loop lemma on the bare [WP While ...]. *)
Ltac focus_while :=
  iStartProof;
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (While _ _) _) => idtac
  | |- envs_entails _ (wp _ _ ?e _) =>
    reshape_expr e ltac:(fun K e' =>
      lazymatch e' with
      | While _ _ => idtac
      | _ => fail "focus_while: redex is not a While"
      end;
      lazymatch K with
      | [] => idtac
      | _ =>
        let revK := rev_ectx K (@nil sn_ectx_item) in
        iApply (wp_bind (fill_K revK))
      end)
  | _ => fail "focus_while: goal is not a WP"
  end.

(* Focus a For sub-expression under an evaluation context (e.g. a trailing
   [;; rest]), so wp_for_list applies with the continuation in the
   postcondition.  Mirrors focus_while. *)
Ltac focus_for :=
  iStartProof;
  snakelet_popvals;
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (For _ _ _) _) => idtac
  | |- envs_entails _ (wp _ _ ?e _) =>
    reshape_expr e ltac:(fun K e' =>
      lazymatch e' with
      | For _ _ _ => idtac
      | _ => fail "focus_for: redex is not a For"
      end;
      lazymatch K with
      | [] => idtac
      | _ =>
        let revK := rev_ectx K (@nil sn_ectx_item) in
        iApply (wp_bind (fill_K revK))
      end)
  | _ => fail "focus_for: goal is not a WP"
  end.

(** * Exception handling

    [raise_val] reduces [Raise (Val v)] to [Val v] (under current
    semantics Raise is a no-op; future work will distinguish it from
    normal return).  [try_val] reduces [Try (Val v) handler] to
    [Val v] via the PureTryReturn pure step. *)

Ltac raise_val :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Raise (Val _)) _) =>
      iApply wp_raise; iNext; snakelet_simpl
  | _ => fail "raise_val: goal is not Raise (Val _)"
  end.

Ltac try_val :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Try (Val _) _) _) =>
      iApply wp_try_val; iNext; snakelet_simpl
  | _ => fail "try_val: goal is not Try (Val _) handler"
  end.

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
  | |- envs_entails _ (wp _ _ (Alloc _) _) =>
      heap_alloc
  | |- envs_entails _ (wp _ _ (Store _ _) _) =>
      heap_store
  | |- envs_entails _ (wp _ _ (While _ _) _) =>
      loop_unfold
  | |- envs_entails _ (wp _ _ (Load _) _) =>
      heap_load
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
