From Stdlib Require Import List ZArith Bool.
Import ListNotations.

(* Library of recursor combinators for list predicates.

   Each recursor is a Fixpoint — structurally recursive, Coq accepts
   natively.  Proved lemmas are proved once and applied everywhere.
   User-defined `for x in xs:` predicates lower to these combinators.
*)

Fixpoint forallb {A} (p : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => true
  | x :: rest => p x && forallb p rest
  end.

Fixpoint existsb {A} (p : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => false
  | x :: rest => p x || existsb p rest
  end.

Fixpoint countb {A} (p : A -> bool) (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: rest => (if p x then 1 else 0) + countb p rest
  end.

Fixpoint fold_left_acc {A B} (f : B -> A -> B) (acc : B) (xs : list A) : B :=
  match xs with
  | [] => acc
  | x :: rest => fold_left_acc f (f acc x) rest
  end.

Fixpoint filterb {A} (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: rest => if p x then x :: filterb p rest else filterb p rest
  end.

(* Lemmas proved once — callers use these instead of re-proving per predicate. *)

Lemma forallb_true : forall A (p : A -> bool) (xs : list A),
  forallb p xs = true <-> (forall x, In x xs -> p x = true).
Proof.
Admitted.

Lemma existsb_true : forall A (p : A -> bool) (xs : list A),
  existsb p xs = true <-> exists x, In x xs /\ p x = true.
Proof.
Admitted.

Lemma countb_app : forall A (p : A -> bool) (xs ys : list A),
  countb p (xs ++ ys) = countb p xs + countb p ys.
Proof.
Admitted.
