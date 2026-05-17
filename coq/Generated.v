(* Generated from py/examples/simple_test.py *)
Require Import ZArith String List Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

(* ── add ── *)
Definition add_body : com :=
  CAss "result"%string (APlus (AVar "a"%string) (AVar "b"%string)).

Theorem add_correct : forall (a b : Z),
  True ->
  wp add_body (fun s => s "result"%string = (a + b)%Z)
              (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof. intros. wp_prove. Qed.

(* ── max_of_two ── *)
Definition max_body : com :=
  CIf (BLe (AVar "b"%string) (AVar "a"%string))
      (CAss "result"%string (AVar "a"%string))
      (CAss "result"%string (AVar "b"%string)).

Theorem max_correct : forall (a b : Z),
  (0 <= a) -> (0 <= b) ->
  wp max_body
     (fun s => a <= s "result"%string /\ b <= s "result"%string)
     (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof.
  intros a b Ha Hb. wp_reduce.
  split; [intro Hleb; apply Z.leb_le in Hleb; wp_prove; split; lia
         | intro Hleb; apply Z.leb_gt in Hleb; wp_prove; split; lia].
Qed.
