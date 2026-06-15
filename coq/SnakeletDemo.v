(** End-to-end demo: Iris WP proofs for SnakeletLang.

    Notations: [#n] for integers, [#true]/[#false] for booleans,
    [e1 + e2] for arithmetic, [let: "x" := e1 in e2] for let-bindings. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From iris.base_logic.lib Require Export gen_heap ghost_map.
Require Import SnakeletLang SnakeletWp.
Require Import SnakeletTactics.
Import snakelet_notation.
Open Scope Z_scope.

(** Contracts for opaque functions: a precondition on the arguments and a
    postcondition relating arguments to result.  The precondition also
    carries the arity/typing constraint. *)
Definition int1_pre (args : list sn_val) : Prop :=
  ∃ x : Z, args = [LitInt x].
Definition square_post (args : list sn_val) (r : sn_val) : Prop :=
  match args with [LitInt x] => r = LitInt (x * x) | _ => False end.
Definition double_post (args : list sn_val) (r : sn_val) : Prop :=
  match args with [LitInt x] => r = LitInt (x + x) | _ => False end.

(** A contract with a *nontrivial* precondition: [decr] requires its
    argument to be at least 1. *)
Definition decr_pre (args : list sn_val) : Prop :=
  ∃ x : Z, args = [LitInt x] ∧ 1 ≤ x.
Definition decr_post (args : list sn_val) (r : sn_val) : Prop :=
  match args with [LitInt x] => r = LitInt (x - 1) | _ => False end.

(** The function table: ["square"]/["double"]/["decr"] are *opaque*
    (contract only), ["twice"] is a *transparent* helper that unfolds to
    its body.  Written with [String.eqb] chains (rather than match on
    string literals) so the totality proof below can case-split. *)
Definition demo_table (f : string) : option fun_entry :=
  if String.eqb f "square" then Some (FunSpec int1_pre square_post)
  else if String.eqb f "double" then Some (FunSpec int1_pre double_post)
  else if String.eqb f "decr" then Some (FunSpec decr_pre decr_post)
  else if String.eqb f "twice" then Some (FunDef ["x"] (Var "x" + Var "x")%S)
  else None.

(** The callee-side promise: every spec'd function, called within its
    precondition, has a result satisfying its postcondition.  In the full
    pipeline this is discharged when each implementation is verified
    against its contract. *)
Lemma demo_table_total : ∀ f pre post vs,
  demo_table f = Some (FunSpec pre post) → pre vs → ∃ v, post vs v.
Proof.
  intros f pre post vs Hf Hpre. unfold demo_table in Hf.
  destruct (String.eqb f "square"); simplify_eq.
  { destruct Hpre as (x & ->). by eexists. }
  destruct (String.eqb f "double"); simplify_eq.
  { destruct Hpre as (x & ->). by eexists. }
  destruct (String.eqb f "decr"); simplify_eq.
  { destruct Hpre as (x & -> & Hx). by eexists. }
  destruct (String.eqb f "twice"); simplify_eq.
Qed.

#[global] Instance demo_fun_ctx : FunCtx :=
  {| fun_entries := demo_table; fun_specs_total := demo_table_total |}.

Section demo.
  Context `{!snakelet_heapGS_gen hlc Σ}.

  (** [3 + 4 = 7] *)
  Lemma add_3_4 s E :
    ⊢ WP (#3 + #4)%S @ s; E {{ v, ⌜v = LitInt 7⌝ }}.
  Proof.
    iApply (@wp_binop _ _ _ _ s E AddOp (LitInt 3) (LitInt 4) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** [let x = 1 in x + x = 2] *)
  Lemma let_add s E :
    ⊢ WP (let: "x" := #1 in Var "x" + Var "x")%S
      @ s; E {{ v, ⌜v = LitInt 2⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "x" (LitInt 1) _).
    iNext.
    iApply (@wp_binop _ _ _ _ s E AddOp (LitInt 1) (LitInt 1) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** [if true then 10 else 20 = 10] *)
  Lemma if_true_10_20 s E :
    ⊢ WP (If (#true)%S (#10)%S (#20)%S)%S
      @ s; E {{ v, ⌜v = LitInt 10⌝ }}.
  Proof.
    iApply wp_if_true. iNext. iApply wp_value'. iPureIntro. reflexivity.
  Qed.

  (** [if false then 10 else 20 = 20] *)
  Lemma if_false_10_20 s E :
    ⊢ WP (If (#false)%S (#10)%S (#20)%S)%S
      @ s; E {{ v, ⌜v = LitInt 20⌝ }}.
  Proof.
    iApply wp_if_false. iNext. iApply wp_value'. iPureIntro. reflexivity.
  Qed.

  (** Let-bound conditional:
      [let b = true in if b then 1 else 0 = 1] *)
  Lemma let_if_true s E :
    ⊢ WP (let: "b" := #true in
            If (Var "b") (#1)%S (#0)%S)%S
      @ s; E {{ v, ⌜v = LitInt 1⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "b" (LitBool true) _).
    iNext.
    iApply wp_if_true. iNext. iApply wp_value'. iPureIntro. reflexivity.
  Qed.

  (** Multi-step arithmetic via let-bindings:
      [let x = 3 in let y = 4 in x * y = 12] *)
  Lemma let_let_mul s E :
    ⊢ WP (let: "x" := #3 in
            let: "y" := #4 in
              Var "x" * Var "y")%S
      @ s; E {{ v, ⌜v = LitInt 12⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "x" (LitInt 3) _). iNext.
    iApply (@wp_let _ _ _ _ s E "y" (LitInt 4) _). iNext.
    iApply (@wp_binop _ _ _ _ s E MulOp (LitInt 3) (LitInt 4) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** [let x = 5 in let y = 2 in x - y = 3] *)
  Lemma let_let_sub s E :
    ⊢ WP (let: "x" := #5 in
            let: "y" := #2 in
              Var "x" - Var "y")%S
      @ s; E {{ v, ⌜v = LitInt 3⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "x" (LitInt 5) _). iNext.
    iApply (@wp_let _ _ _ _ s E "y" (LitInt 2) _). iNext.
    iApply (@wp_binop _ _ _ _ s E SubOp (LitInt 5) (LitInt 2) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** Comparison operators:
      [let x = 3 in x < 5 = true] *)
  Lemma let_lt s E :
    ⊢ WP (let: "x" := #3 in
            Var "x" < #5)%S
      @ s; E {{ v, ⌜v = LitBool true⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "x" (LitInt 3) _). iNext.
    iApply (@wp_binop _ _ _ _ s E LtOp (LitInt 3) (LitInt 5) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** * Parametric contracts (hold for all inputs) *)
  Lemma add_contract s E (a b : Z) :
    ⊢ WP (let: "a" := #a in
            let: "b" := #b in
              Var "a" + Var "b")%S
      @ s; E {{ v, ⌜v = LitInt (a + b)%Z⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "a" (LitInt a) _). iNext.
    iApply (@wp_let _ _ _ _ s E "b" (LitInt b) _). iNext.
    iApply (@wp_binop _ _ _ _ s E AddOp (LitInt a) (LitInt b) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  Lemma mul_contract s E (a b : Z) :
    ⊢ WP (let: "a" := #a in
            let: "b" := #b in
              Var "a" * Var "b")%S
      @ s; E {{ v, ⌜v = LitInt (a * b)%Z⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "a" (LitInt a) _). iNext.
    iApply (@wp_let _ _ _ _ s E "b" (LitInt b) _). iNext.
    iApply (@wp_binop _ _ _ _ s E MulOp (LitInt a) (LitInt b) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  Lemma max_contract s E (a b : Z) :
    ⊢ WP (let: "a" := #a in
            let: "b" := #b in
              If (Val (LitBool (Z.ltb a b))) (Var "b") (Var "a"))%S
      @ s; E {{ v, ⌜v = LitInt (Z.max a b)⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "a" (LitInt a) _). iNext.
    iApply (@wp_let _ _ _ _ s E "b" (LitInt b) _). iNext.
    destruct (Z_lt_dec a b) as [Hlt | Hge].
    - simpl. assert (Z.ltb a b = true) as -> by (apply Z.ltb_lt; auto).
      iApply wp_if_true. iNext. iApply wp_value'. iPureIntro.
      rewrite Z.max_r; [reflexivity | lia].
    - simpl. assert (Z.ltb a b = false) as -> by (apply Z.ltb_nlt; auto).
      iApply wp_if_false. iNext. iApply wp_value'. iPureIntro.
      rewrite Z.max_l; [reflexivity | lia].
  Qed.

  Lemma abs_nonneg s E (x : Z) :
    ⊢ WP (let: "x" := #x in
            If (Val (LitBool (Z.ltb x 0))) (#0 - Var "x") (Var "x"))%S
      @ s; E {{ v, ∃ (z : Z), ⌜v = LitInt z⌝ ∗ ⌜z >= 0⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ _ s E "x" (LitInt x) _). iNext.
    destruct (Z_lt_dec x 0) as [Hlt | Hge].
    - simpl. assert (Z.ltb x 0 = true) as -> by (apply Z.ltb_lt; auto).
      iApply wp_if_true. iNext.
      iApply (@wp_binop _ _ _ _ s E SubOp (LitInt 0) (LitInt x) _).
      iNext. iPureIntro. exists (0 - x)%Z. split; [reflexivity | lia].
    - simpl. assert (Z.ltb x 0 = false) as -> by (apply Z.ltb_nlt; auto).
      iApply wp_if_false. iNext. iApply wp_value'. iPureIntro. exists x.
      split; [reflexivity | lia].
  Qed.

  (** * [wp_bind] demo *)
  Lemma if_lt_wp_bind s E :
    ⊢ WP (If (#2 < #3)%S (Val (LitInt 10)) (Val (LitInt 20)))%S
      @ s; E {{ v, ⌜v = LitInt 10⌝ }}.
  Proof.
    wp_bind (#2 < #3)%S.
    iApply (@wp_binop _ _ _ _ s E LtOp (LitInt 2) (LitInt 3) _).
    iNext. simpl.
    iApply wp_if_true. iNext. iApply wp_value'. iPureIntro. reflexivity.
  Qed.

  (** * Negative tests (intentionally unprovable) *)
  Lemma add_3_4_bug s E :
    ⊢ WP (#3 + #4)%S @ s; E {{ v, ⌜v = LitInt 42⌝ }}.
  Proof. (* [binop_eval AddOp 3 4 = 7 != 42].  Unprovable. *) Admitted.

  Lemma if_true_not_zero s E :
    ⊢ WP (If (#true)%S (#1)%S (#0)%S)%S
      @ s; E {{ v, ⌜v = LitInt 0⌝ }}.
  Proof. (* [if true then 1 else 0 = 1 != 0]. *) Admitted.

  (** * Opaque calls (contract-driven)

      Calls are verified against [demo_fun_ctx] via [wp_call]: the caller
      proves the precondition, and the continuation receives the
      postcondition for whatever result the callee produces. *)

  Lemma call_square s E :
    ⊢ WP Call "square" [Val (LitInt 5)] @ s; E
      {{ v, ⌜v = LitInt 25⌝ }}.
  Proof.
    iApply (wp_call s E "square" int1_pre square_post [LitInt 5]).
    { reflexivity. }
    { by exists 5%Z. }
    iIntros (w Hw). unfold square_post in Hw. subst w. done.
  Qed.

  Lemma call_double s E :
    ⊢ WP Call "double" [Val (LitInt 7)] @ s; E
      {{ v, ⌜v = LitInt 14⌝ }}.
  Proof.
    iApply (wp_call s E "double" int1_pre double_post [LitInt 7]).
    { reflexivity. }
    { by exists 7%Z. }
    iIntros (w Hw). unfold double_post in Hw. subst w. done.
  Qed.

  (** [decr] has a real precondition: the caller must prove [1 ≤ x] at the
      call site or the proof does not go through. *)
  Lemma call_decr s E (x : Z) :
    1 ≤ x →
    ⊢ WP Call "decr" [Val (LitInt x)] @ s; E
      {{ v, ⌜v = LitInt (x - 1)⌝ }}.
  Proof.
    intros Hx.
    iApply (wp_call s E "decr" decr_pre decr_post [LitInt x]).
    { reflexivity. }
    { by exists x. }
    iIntros (w Hw). unfold decr_post in Hw. subst w. done.
  Qed.

  (** * Transparent call (definition unfolds)

      ["twice"] carries no contract — the call β-reduces to its body with
      the arguments substituted, and verification proceeds on the body.
      Parametric in the argument, as for the other contracts. *)
  Lemma call_twice_transparent s E (x : Z) :
    ⊢ WP Call "twice" [Val (LitInt x)] @ s; E
      {{ v, ⌜v = LitInt (x + x)⌝ }}.
  Proof.
    iApply (wp_call_unfold s E "twice" ["x"] (Var "x" + Var "x")%S [LitInt x]).
    { reflexivity. }
    { reflexivity. }
    iNext. simpl.
    iApply (@wp_binop _ _ _ _ s E AddOp (LitInt x) (LitInt x) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** A negative test, proved positively: calling a function with no entry
      is stuck — no [prim_step] exists, because both call rules demand a
      [fun_entries] witness and [demo_fun_ctx] has none for
      ["nonexistent"]. *)
  Lemma call_unknown_stuck σ :
    ¬ reducible (Λ := snakelet_lang) (Call "nonexistent" [Val (LitInt 0)]) σ.
  Proof.
    intros (κ & e' & σ' & efs & Hstep).
    apply (prim_call_inv "nonexistent" [LitInt 0]) in Hstep
      as (_ & _ & _ & [(pre & post & w & Hentry & _) | (params & body & Hentry & _)]);
      simpl in Hentry; discriminate Hentry.
  Qed.

  (** Another negative test, proved positively: a transparent call with the
      wrong arity is stuck. *)
  Lemma call_twice_wrong_arity_stuck σ :
    ¬ reducible (Λ := snakelet_lang)
        (Call "twice" [Val (LitInt 1); Val (LitInt 2)]) σ.
  Proof.
    intros (κ & e' & σ' & efs & Hstep).
    apply (prim_call_inv "twice" [LitInt 1; LitInt 2]) in Hstep
      as (_ & _ & _ & [(pre & post & w & Hentry & _) | (params & body & Hentry & Hlen & _)]).
    - simpl in Hentry. discriminate Hentry.
    - simpl in Hentry. injection Hentry as <- <-. simpl in Hlen. discriminate Hlen.
  Qed.

  (** * Call chains, discharged by a reproducible tactic

      A function body that chains calls — results flowing into the next
      call via let-bindings — verified by [snakelet_auto] without
      intervention: [square(5) = 25] (opaque), [twice(25) = 50]
      (transparent unfold), [decr(50) = 49] (opaque, pre [1 ≤ 50]
      discharged automatically). *)
  Lemma call_chain s E :
    ⊢ WP (let: "a" := Call "square" [Val (LitInt 5)] in
          let: "b" := Call "twice" [Var "a"] in
          Call "decr" [Var "b"])%S
      @ s; E {{ v, ⌜v = LitInt 49⌝ }}.
  Proof. snakelet_auto. Qed.

  (** Chains mixing calls with pure arithmetic are also automatic. *)
  Lemma call_chain_mixed s E :
    ⊢ WP (let: "a" := Call "square" [Val (LitInt 3)] in
          let: "b" := Var "a" + #1 in
          Call "decr" [Var "b"])%S
      @ s; E {{ v, ⌜v = LitInt 9⌝ }}.
  Proof. snakelet_auto. Qed.

  (** * Staged proofs — the generated-script form

      The pipeline emits one stage tactic per SnakeletIR node instead of
      the [snakelet_auto] monolith: each line can fail independently, the
      failing stage identifies itself by name, and the script doubles as
      the proof trace.  Optional name arguments assert the expected redex
      (drift detection between generator and goal). *)
  Lemma call_chain_staged s E :
    ⊢ WP (let: "a" := Call "square" [Val (LitInt 5)] in
          let: "b" := Call "twice" [Var "a"] in
          Call "decr" [Var "b"])%S
      @ s; E {{ v, ⌜v = LitInt 49⌝ }}.
  Proof.
    iStartProof.
    call_opaque "square".      (* a := 25, pre: int1 *)
    pure_step.                 (* bind "a" *)
    call_transparent "twice".  (* unfold: 25 + 25 *)
    pure_step.                 (* binop: 50 *)
    pure_step.                 (* bind "b" *)
    call_opaque "decr".        (* 49, pre: 1 <= 50 *)
    finish_pure.
  Qed.

  (** Path fork: a symbolic conditional becomes two staged branches, the
      branch hypothesis acting as a path constraint for the arithmetic
      ([x < 0] in the true branch, [0 <= x] in the false branch).  The
      generator decides the split point; [snakelet_auto] never splits. *)
  Lemma abs_staged s E (x : Z) :
    ⊢ WP (let: "x" := #x in
            If (Val (LitBool (Z.ltb x 0))) (#0 - Var "x") (Var "x"))%S
      @ s; E {{ v, ∃ z : Z, ⌜v = LitInt z⌝ ∗ ⌜z >= 0⌝ }}.
  Proof.
    iStartProof.
    pure_step.                 (* bind "x" *)
    case_bool.                 (* fork on x <? 0 *)
    - pure_step.               (* true branch: select 0 - x *)
      pure_step.               (* binop: 0 - x *)
      finish_pure.             (* z := 0 - x; constraint x < 0 *)
    - pure_step.               (* false branch: select x *)
      finish_pure.             (* z := x; constraint 0 <= x *)
  Qed.

  (** The contract is *enforced*, not assumed: calling [decr] outside its
      precondition ([1 ≤ x] fails for [0]) is stuck — no [prim_step]
      exists, so no WP proof can sneak past the precondition. *)
  Lemma call_decr_pre_violation_stuck σ :
    ¬ reducible (Λ := snakelet_lang) (Call "decr" [Val (LitInt 0)]) σ.
  Proof.
    intros (κ & e' & σ' & efs & Hstep).
    apply (prim_call_inv "decr" [LitInt 0]) in Hstep
      as (_ & _ & _ & [(pre & post & w & Hentry & Hpre & _)
                      | (params & body & Hentry & _)]).
    - assert (Hd : fun_entries "decr" = Some (FunSpec decr_pre decr_post))
        by reflexivity.
      rewrite Hd in Hentry. simplify_eq.
      destruct Hpre as (x & Hx & Hge). simplify_eq. lia.
    - assert (Hd : fun_entries "decr" = Some (FunSpec decr_pre decr_post))
        by reflexivity.
      rewrite Hd in Hentry. discriminate Hentry.
  Qed.

  (** * Heap operations (alloc, store, load) — staged proof

      One cell created, written, read back.  The [heap_alloc] stage
      introduces a fresh location [l] with the points-to resource
      [Hl]; [heap_store] and [heap_load] reference ["Hl"] directly.
      The staged proof is the generated-script form. *)
  Lemma heap_alloc_store_load s E :
    ⊢ WP (Let "x" (Alloc (Val (LitInt 42)))
             (Store (Var "x") (Val (LitInt 7)) ;;
              Load (Var "x")))%S
      @ s; E {{ v, ⌜v = LitInt 7⌝ }}.
  Proof.
    iStartProof.
    heap_alloc.                          (* l, Hl : l ↦ 42 *)
    pure_step.                           (* bind "x" *)
    heap_store.                          (* Hl : l ↦ 7 *)
    pure_step.                           (* let _ = LitUnit in ... *)
    heap_load.                           (* Hl : l ↦ 7, post: LitInt 7 *)
    finish_pure.
  Qed.

  (** * While loop — staged proof

      A loop that immediately terminates (condition false).  [loop_unfold]
      exposes the [If]; [pure_step] dispatches the false branch. *)
  Lemma while_false s E :
    ⊢ WP (While (Val (LitBool false)) (Val LitUnit)) @ s; E
      {{ v, ⌜v = LitUnit⌝ }}.
  Proof.
    iApply wp_while. iNext.
    iApply wp_if_false. iNext.
    iApply wp_value'. iPureIntro. reflexivity.
  Qed.

  (** * While loop with heap state — counting from 0 to 2

      A loop incrementing a heap cell until the condition fails (2 < 2).
      The loop body is [Store c (Load c + 1)]; the [;;] continuation
      unfolds to a [Let "_" step.  Three loop_unfold stages (iterations
      0→1, 1→2, 2→exit) plus the final Load produce the postcondition. *)
  Lemma while_count_to_two s E :
    ⊢ WP (Let "c" (Alloc (Val (LitInt 0)))
             ((While (BinOp LtOp (Load (Var "c")) (Val (LitInt 2)))
                (Store (Var "c")
                  (BinOp AddOp (Load (Var "c")) (Val (LitInt 1))))) ;;
              Load (Var "c")))%S
      @ s; E {{ v, ⌜v = LitInt 2⌝ }}.
  Proof.
    iStartProof.
    heap_alloc. pure_step.                  (* fresh cell, bind c *)
    (* ---- iteration 1: c=0, 0<2=true ---- *)
    loop_unfold.
    heap_load. pure_step. pure_step.        (* cond: load, <, enter body *)
    heap_load. pure_step. heap_store. pure_step.  (* body: load, +, store, ;; *)
    (* ---- iteration 2: c=1, 1<2=true ---- *)
    loop_unfold.
    heap_load. pure_step. pure_step.
    heap_load. pure_step. heap_store. pure_step.
    (* ---- iteration 3: c=2, 2<2=false ---- *)
    loop_unfold.
    heap_load. pure_step. pure_step.        (* cond false: exit loop *)
    pure_step.                              (* ;; bind after LitUnit *)
    heap_load. finish_pure.                 (* final read: 2 *)
  Qed.

  (** * Frame conditions — multi-cell separation

      Two heap cells coexist: [a] receives 10, [b] holds 2.
      The store to [a] does not touch [b]; the load from [b] in the
      final step proves [b ↦ 2] was preserved (Iris separation logic
      frames automatically — no clobber or writes list needed).
      Multi-cell naming: alloc produces distinct Coq location names
      (la, lb) and hypothesis names (Ha, Hb). *)
  Lemma two_cells_frame s E :
    ⊢ WP (Let "a" (Alloc (Val (LitInt 1)))
             (Let "b" (Alloc (Val (LitInt 2)))
                (Store (Var "a") (Val (LitInt 10)) ;;
                 Load (Var "b"))))%S
      @ s; E {{ v, ⌜v = LitInt 2⌝ }}.
  Proof.
    iStartProof.
    wp_bind (Alloc (Val (LitInt 1))).
    iApply wp_alloc. iIntros (la) "Ha". simpl.
    iApply wp_let. iNext. simpl.
    wp_bind (Alloc (Val (LitInt 2))).
    iApply wp_alloc. iIntros (lb) "Hb". simpl.
    iApply wp_let. iNext. simpl.
    wp_bind (Store (Val (LitLoc la)) (Val (LitInt 10))).
    iApply (wp_store with "Ha"). iIntros "Ha". simpl.
    snakelet_simpl. snakelet_pure_step. iNext. snakelet_simpl.
    wp_bind (Load (Val (LitLoc lb))).
    iApply (wp_load with "Hb"). iIntros "Hb".
    iPureIntro. reflexivity.
  Qed.

  (** * Multi-cell robustness — location-keyed staged proofs

      The same bare stage sequence closes regardless of which cell is
      targeted: [tac_wp_load]/[tac_wp_store] find the points-to
      hypothesis by unification on the location extracted from the goal
      expression, never by name.  Swapping target cells or adding cells
      changes only the stage count, not the script shape. *)
  Lemma two_cells_staged s E :
    ⊢ WP (Let "a" (Alloc (Val (LitInt 1)))
             (Let "b" (Alloc (Val (LitInt 2)))
                (Store (Var "a") (Val (LitInt 10)) ;;
                 Load (Var "b"))))%S
      @ s; E {{ v, ⌜v = LitInt 2⌝ }}.
  Proof.
    iStartProof.
    heap_alloc. pure_step.
    heap_alloc. pure_step.
    heap_store. pure_step.
    heap_load. finish_pure.
  Qed.

  (** Identical script, swapped target cells. *)
  Lemma two_cells_staged_swapped s E :
    ⊢ WP (Let "a" (Alloc (Val (LitInt 1)))
             (Let "b" (Alloc (Val (LitInt 2)))
                (Store (Var "b") (Val (LitInt 10)) ;;
                 Load (Var "a"))))%S
      @ s; E {{ v, ⌜v = LitInt 1⌝ }}.
  Proof.
    iStartProof.
    heap_alloc. pure_step.
    heap_alloc. pure_step.
    heap_store. pure_step.
    heap_load. finish_pure.
  Qed.

  (** * Exception handling — Raise and Try

      Under the current semantics, [Raise v] is a no-op (reduces to
      [Val v]), and [Try (Val v) handler] discards the handler and
      returns [v].  These lemmas establish the infrastructure for
      future work where Raise will carry exception information. *)
  Lemma raise_noop s E :
    ⊢ WP (Raise (Val (LitInt 42))) @ s; E {{ v, ⌜v = LitInt 42⌝ }}.
  Proof. iApply wp_raise. iNext. iPureIntro. reflexivity. Qed.

  Lemma try_val_noop s E :
    ⊢ WP (Try (Val (LitInt 7)) (Val LitUnit)) @ s; E {{ v, ⌜v = LitInt 7⌝ }}.
  Proof. iApply wp_try_val. iNext. iPureIntro. reflexivity. Qed.

  (** * Ghost-state opaque calls

      The caller holds a [ghost_map_elem] fragment that attests the spec
      in the ghost table.  [wp_call_ghost] consumes it (persistently) and
      the call proceeds under the contract.  The authoritative part lives
      in an invariant (not shown here). *)
  Section ghost_calls.
    Context `{!ghost_mapG Σ string fun_entry}.

    Lemma square_ghost_elem γ s E :
      ghost_map_elem γ "square" (DfracOwn 1) (FunSpec int1_pre square_post) -∗
      WP Call "square" [Val (LitInt 5)] @ s; E {{ v, ⌜v = LitInt 25⌝ }}.
    Proof.
      iIntros "Hsq".
      iApply (wp_call_ghost γ s E "square" int1_pre square_post [LitInt 5]
               (λ v, ⌜v = LitInt 25⌝)%I with "[$Hsq]").
      { reflexivity. }
      { by exists 5%Z. }
      iIntros (w Hw). unfold square_post in Hw. subst w. iPureIntro. reflexivity.
    Qed.

    Lemma square_ghost_auth_elem γ s E :
      ghost_map_auth γ (DfracOwn 1) {["square" := FunSpec int1_pre square_post]} -∗
      ghost_map_elem γ "square" (DfracOwn 1) (FunSpec int1_pre square_post) -∗
      WP Call "square" [Val (LitInt 5)] @ s; E {{ v, ⌜v = LitInt 25⌝ }}.
    Proof.
      iIntros "Hauth Hsq".
      iDestruct (ghost_map_lookup with "Hauth Hsq") as "%Hlookup".
      iApply (wp_call_ghost γ s E "square" int1_pre square_post [LitInt 5]
               (λ v, ⌜v = LitInt 25⌝)%I with "[$Hsq]").
      { reflexivity. }
      { by exists 5%Z. }
      iIntros (w Hw). unfold square_post in Hw. subst w. iPureIntro. reflexivity.
  Qed.
End ghost_calls.

(** * Dict operations *)
Section dict_demo.
  Context `{!snakelet_heapGS_gen hlc Σ}.

  Lemma dict_get_hit s E :
    ⊢ WP (DictGet (Val (LitDict [(LitInt 1, LitInt 100)])) (Val (LitInt 1)))
      @ s; E {{ w, ⌜w = LitInt 100⌝ }}.
  Proof.
    iApply (@wp_dict_get _ _ _ _ _ _ [(LitInt 1, LitInt 100)] (LitInt 1) (LitInt 100) _).
    - vm_compute. reflexivity.
    - iNext. iPureIntro. reflexivity.
  Qed.
End dict_demo.

End demo.
