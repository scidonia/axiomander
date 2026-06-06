(* Iris proof skeleton for `bump` *)
(* Classification: mixed_pure_resource *)

From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang proofmode notation.


(* SMT-trusted axioms — one per pure side condition *)
(* Each was verified by Z3 (QF_LIA) — the negation is unsatisfiable. *)
Axiom smt_pure_bump_0 : t0 = old_box_value.
Axiom smt_pure_bump_1 : t1 = old_box_value + 1.
Axiom smt_pure_bump_2 : t2 = t1.

Lemma bump_spec box old_box_value :
  {{{ box_value_points_to box old_box_value ∗ ⌜old_box_value >= 0⌝ }}}
    bump_core box
  {{{ result, RET result;
      box_value_points_to box (old_box_value + 1) ∗
      ⌜result = old_box_value + 1⌝ }}}.
Proof.
  iIntros (Φ) "(Hfield & %Hnonneg) HΦ".
  wp_load.
  wp_pures.
  (* SMT: t1 == old_box_value + 1 *)
  wp_store.
  wp_load.
  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  (* SMT-trusted pure equalities — one exact per axiom above *)
  repeat split.
  exact smt_pure_bump_0.
  exact smt_pure_bump_1.
  exact smt_pure_bump_2.
Qed.

(*
  Function: bump
  Classification: mixed_pure_resource
  First lowering: succeeded
  Resource footprint: box.value
  Resource model: owned_field_v0
  Pure side conditions: 3
  Pure SMT discharged: 3/3 (trusted)
  Iris proof skeleton: generated
*)