From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp.
Import ListNotations.
Open Scope Z_scope.

(** * Example 1: add(a, b) = a + b *)
Definition add_body : com :=
  CAss "result"%string (APlus (AVar "a"%string) (AVar "b"%string)).

Theorem add_correct : forall (a b : Z),
  True ->
  wp add_body (wp_normal (fun s => asZ (s "result"%string) = (a + b)%Z))
              (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof.
  intros. unfold wp, wp_normal, add_body, upd. simpl. reflexivity.
Qed.

(** * Example 2: abs_val(n) *)
Definition abs_val_body : com :=
  CIf (BLe (ANum 0) (AVar "n"%string))
      (CAss "result"%string (AVar "n"%string))
      (CAss "result"%string (AMult (ANum (-1)) (AVar "n"%string))).

Theorem abs_val_correct : forall (n : Z),
  0 <= n ->
  wp abs_val_body (wp_normal (fun s => 0 <= asZ (s "result"%string)))
                  (updZ empty_state "n"%string n).
Proof.
  intros n Hle.
  unfold wp, wp_normal, abs_val_body, upd. simpl.
  split.
  - intro H. apply Z.leb_le in H. exact Hle.
  - intro H. apply Z.leb_gt in H. lia.
Qed.

(** * Example 3: max_of_two(a, b) *)
Definition max_body : com :=
  CIf (BLe (AVar "b"%string) (AVar "a"%string))
      (CAss "result"%string (AVar "a"%string))
      (CAss "result"%string (AVar "b"%string)).

Theorem max_correct : forall (a b : Z),
  0 <= a -> 0 <= b ->
  wp max_body
     (wp_normal (fun s => a <= asZ (s "result"%string) /\ b <= asZ (s "result"%string)))
     (updZ (updZ empty_state "a"%string a) "b"%string b).
Proof.
  intros a b Ha Hb.
  unfold wp, wp_normal, max_body, upd. simpl.
  split.
  - intro H. apply Z.leb_le in H. split; lia.
  - intro H. apply Z.leb_gt in H. split; lia.
Qed.

(** * Example 4: sum_to(n) -- loop with invariant *)
Definition sum_invariant (n : Z) (s : state) : Prop :=
  asZ (s "acc"%string) = asZ (s "i"%string) * (asZ (s "i"%string) + 1) / 2 /\ asZ (s "i"%string) <= n.

Definition sum_body (n : Z) : com :=
  let init_acc := CAss "acc"%string (ANum 0) in
  let init_i   := CAss "i"%string (ANum 0) in
  let incr_i   := CAss "i"%string (APlus (AVar "i"%string) (ANum 1)) in
  let incr_acc := CAss "acc"%string (APlus (AVar "acc"%string) (AVar "i"%string)) in
  let loop_body := CSeq incr_i incr_acc in
  let loop := CWhile (BLe (AVar "i"%string) (AVar "n"%string))
                     (sum_invariant n) loop_body in
  let after_loop := CAss "result"%string (AVar "acc"%string) in
  CSeq init_acc (CSeq init_i (CSeq loop after_loop)).

Theorem sum_correct : forall (n : Z),
  0 <= n ->
  wp (sum_body n)
     (wp_normal (fun s => s "result"%string = VZ (n * (n + 1) / 2)))
     (updZ empty_state "n"%string n).
Proof.
  intros n Hn.
  unfold sum_body, wp, wp_normal, upd. simpl.
  unfold sum_invariant. simpl.
  split.
  - reflexivity.
  - exact Hn.
Qed.
