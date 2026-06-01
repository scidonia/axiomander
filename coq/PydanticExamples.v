From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp Pydantic.
Import ListNotations.
Open Scope Z_scope.

(** * Example 1: Distance squared from origin *)

Definition distance_sq_body : com :=
  CAss "result"%string
    (APlus (AMult (AVar "p.x"%string) (AVar "p.x"%string))
           (AMult (AVar "p.y"%string) (AVar "p.y"%string))).

Theorem distance_sq_correct : forall (px py : Z),
  px >= 0 -> py >= 0 ->
  wp distance_sq_body
  (wp_normal (fun s => asZ (s "result"%string)
          = asZ (s "p.x"%string) * asZ (s "p.x"%string)
          + asZ (s "p.y"%string) * asZ (s "p.y"%string)))
     (init_point_state px py).
Proof.
  intros. unfold wp, wp_normal, distance_sq_body, init_point_state, store_field, flat_key; simpl. reflexivity.
Qed.

(** * Example 2: Rectangle area *)

Record Rect : Type := {
  rect_x : Z;
  rect_y : Z;
  rect_w : Z;
  rect_h : Z;
}.

Definition init_rect_state (rw rh : Z) : state :=
  let s := store_field "r"%string "h"%string (VZ rh) empty_state in
  store_field "r"%string "w"%string (VZ rw) s.

Definition area_body : com :=
  CAss "result"%string
    (AMult (AVar "r.w"%string) (AVar "r.h"%string)).

Theorem area_correct : forall (w h : Z),
  w > 0 -> h > 0 ->
  wp area_body
     (wp_normal (fun s => asZ (s "result"%string) = asZ (s "r.w"%string) * asZ (s "r.h"%string)))
     (init_rect_state w h).
Proof.
  intros. unfold wp, wp_normal, area_body, init_rect_state, store_field, flat_key; simpl. reflexivity.
Qed.
