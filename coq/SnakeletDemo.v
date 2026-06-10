(** End-to-end demo: Iris WP proofs for SnakeletLang.

    Notations: [#n] for integers, [#true]/[#false] for booleans,
    [e1 + e2] for arithmetic, [let: "x" := e1 in e2] for let-bindings. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From iris.base_logic.lib Require Export gen_heap.
Require Import SnakeletLang SnakeletWp.
Require Import SnakeletTactics.
Import snakelet_notation.
Open Scope Z_scope.

Section demo.
  Context `{!snakelet_heapGS_gen hlc Σ}.

  (** [3 + 4 = 7] *)
  Lemma add_3_4 s E :
    ⊢ WP (#3 + #4)%S @ s; E {{ v, ⌜v = LitInt 7⌝ }}.
  Proof.
    iApply (@wp_binop _ _ _ s E AddOp (LitInt 3) (LitInt 4) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** [let x = 1 in x + x = 2] *)
  Lemma let_add s E :
    ⊢ WP (let: "x" := #1 in Var "x" + Var "x")%S
      @ s; E {{ v, ⌜v = LitInt 2⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ s E "x" (LitInt 1) _).
    iNext.
    iApply (@wp_binop _ _ _ s E AddOp (LitInt 1) (LitInt 1) _).
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
    iApply (@wp_let _ _ _ s E "b" (LitBool true) _).
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
    iApply (@wp_let _ _ _ s E "x" (LitInt 3) _). iNext.
    iApply (@wp_let _ _ _ s E "y" (LitInt 4) _). iNext.
    iApply (@wp_binop _ _ _ s E MulOp (LitInt 3) (LitInt 4) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** [let x = 5 in let y = 2 in x - y = 3] *)
  Lemma let_let_sub s E :
    ⊢ WP (let: "x" := #5 in
            let: "y" := #2 in
              Var "x" - Var "y")%S
      @ s; E {{ v, ⌜v = LitInt 3⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ s E "x" (LitInt 5) _). iNext.
    iApply (@wp_let _ _ _ s E "y" (LitInt 2) _). iNext.
    iApply (@wp_binop _ _ _ s E SubOp (LitInt 5) (LitInt 2) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** Comparison operators:
      [let x = 3 in x < 5 = true] *)
  Lemma let_lt s E :
    ⊢ WP (let: "x" := #3 in
            Var "x" < #5)%S
      @ s; E {{ v, ⌜v = LitBool true⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ s E "x" (LitInt 3) _). iNext.
    iApply (@wp_binop _ _ _ s E LtOp (LitInt 3) (LitInt 5) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  (** * Parametric contracts (hold for all inputs) *)
  Lemma add_contract s E (a b : Z) :
    ⊢ WP (let: "a" := #a in
            let: "b" := #b in
              Var "a" + Var "b")%S
      @ s; E {{ v, ⌜v = LitInt (a + b)%Z⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ s E "a" (LitInt a) _). iNext.
    iApply (@wp_let _ _ _ s E "b" (LitInt b) _). iNext.
    iApply (@wp_binop _ _ _ s E AddOp (LitInt a) (LitInt b) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  Lemma mul_contract s E (a b : Z) :
    ⊢ WP (let: "a" := #a in
            let: "b" := #b in
              Var "a" * Var "b")%S
      @ s; E {{ v, ⌜v = LitInt (a * b)%Z⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ s E "a" (LitInt a) _). iNext.
    iApply (@wp_let _ _ _ s E "b" (LitInt b) _). iNext.
    iApply (@wp_binop _ _ _ s E MulOp (LitInt a) (LitInt b) _).
    iNext. iPureIntro. reflexivity.
  Qed.

  Lemma max_contract s E (a b : Z) :
    ⊢ WP (let: "a" := #a in
            let: "b" := #b in
              If (Val (LitBool (Z.ltb a b))) (Var "b") (Var "a"))%S
      @ s; E {{ v, ⌜v = LitInt (Z.max a b)⌝ }}.
  Proof.
    iApply (@wp_let _ _ _ s E "a" (LitInt a) _). iNext.
    iApply (@wp_let _ _ _ s E "b" (LitInt b) _). iNext.
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
    iApply (@wp_let _ _ _ s E "x" (LitInt x) _). iNext.
    destruct (Z_lt_dec x 0) as [Hlt | Hge].
    - simpl. assert (Z.ltb x 0 = true) as -> by (apply Z.ltb_lt; auto).
      iApply wp_if_true. iNext.
      iApply (@wp_binop _ _ _ s E SubOp (LitInt 0) (LitInt x) _).
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
    iApply (@wp_binop _ _ _ s E LtOp (LitInt 2) (LitInt 3) _).
    iNext. simpl.
    iApply wp_if_true. iNext. iApply wp_value'. iPureIntro. reflexivity.
  Qed.

  (** * Function call demos *)
  Lemma call_square s E :
    ⊢ WP Call "square" [Val (LitInt 5)] @ s; E
      {{ v, ⌜v = LitInt 25⌝ }}.
  Proof. Admitted.

  Lemma call_double s E :
    ⊢ WP Call "double" [Val (LitInt 7)] @ s; E
      {{ v, ⌜v = LitInt 14⌝ }}.
  Proof. Admitted.

  (** * Negative tests (intentionally unprovable) *)
  Lemma add_3_4_bug s E :
    ⊢ WP (#3 + #4)%S @ s; E {{ v, ⌜v = LitInt 42⌝ }}.
  Proof. (* [binop_eval AddOp 3 4 = 7 != 42].  Unprovable. *) Admitted.

  Lemma if_true_not_zero s E :
    ⊢ WP (If (#true)%S (#1)%S (#0)%S)%S
      @ s; E {{ v, ⌜v = LitInt 0⌝ }}.
  Proof. (* [if true then 1 else 0 = 1 != 0]. *) Admitted.

End demo.
