From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

(** * Black Hole Examples (Axiomander-style)

    Three theorems demonstrating the black hole theory:
    1. Unaffected properties survive a havoc
    2. Affected properties are lost across a havoc
    3. Re-asserting dropped properties restores verification *)

(** Shared definitions *)
Definition compute_and_havoc : com :=
  CSeq
    (CAss "x"%string (APlus (AVar "a"%string) (AVar "b"%string)))
    (CHavoc ["x"%string]).

Definition init_state_ab (a b : Z) : state :=
  updZ (updZ empty_state "a"%string a) "b"%string b.

(** * Theorem 1: Unaffected property survives a black hole *)
Theorem a_unchanged : forall (a b : Z),
  wp compute_and_havoc
     (fun s => asZ (s "a"%string) = a)
     (init_state_ab a b).
Proof. Admitted.

(** * Theorem 2: Affected property is lost across a black hole *)
Theorem x_lost : forall (a b : Z),
  a + b <> 0 ->
  ~ (wp compute_and_havoc
       (fun s => asZ (s "x"%string) = a + b)
       (init_state_ab a b)).
Proof. Admitted.

(** * Theorem 3: Re-asserting the dropped property restores verification *)
Theorem recovery : forall (a b : Z),
  let body := CSeq compute_and_havoc
                    (CAss "x"%string (APlus (AVar "a"%string) (AVar "b"%string))) in
  wp body (fun s => asZ (s "x"%string) = a + b) (init_state_ab a b).
Proof. Admitted.
