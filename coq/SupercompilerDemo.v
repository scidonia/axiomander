From Stdlib Require Import List ZArith Bool String.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Require Import LambdaA Supercompiler D1Fold.

(** * Supercompilation Demo

    Shows the supercompiler in action on concrete terms. *)

(** * 1. Constant folding: 1 + 2 * 3 *)

Definition t_arith : p_expr :=
  PBinOp PAddOp
    (PVal (PLitInt 1))
    (PBinOp PMulOp (PVal (PLitInt 2)) (PVal (PLitInt 3))).

Eval vm_compute in supercompile [] 10 [] t_arith.
(* Expected: PVal (PLitInt 7) *)

(** * 2. Branch pruning: if (3 > 2) then "yes" else "no" *)

Definition t_branch : p_expr :=
  PIf (PBinOp PGtOp (PVal (PLitInt 3)) (PVal (PLitInt 2)))
      (PVal (PLitString "yes"))
      (PVal (PLitString "no")).

Eval vm_compute in supercompile [] 10 [] t_branch.
(* Expected: PVal (PLitString "yes") *)

(** * 3. Let inlining *)

Definition t_let : p_expr :=
  PLet "x" (PVal (PLitInt 10))
    (PLet "y" (PVal (PLitInt 5))
      (PBinOp PAddOp (PVar "x") (PVar "y"))).

Eval vm_compute in supercompile [] 10 [] t_let.
(* Expected: PVal (PLitInt 15) *)

(** * 4. Function call inlining *)

(** double(n) = n + n *)
Definition F_double : fn_table :=
  [("double", (["n"], PBinOp PAddOp (PVar "n") (PVar "n")))].

Definition t_call : p_expr :=
  PCall "double" [PVal (PLitInt 7)].

Eval vm_compute in supercompile F_double 10 [] t_call.
(* Expected: PVal (PLitInt 14) *)

(** * 5. Nested function call *)

(** add(a, b) = a + b; square_sum(x) = add(double(x), x) *)
Definition F_nested : fn_table :=
  [ ("double",     (["n"], PBinOp PAddOp (PVar "n") (PVar "n")))
  ; ("add",        (["a"; "b"], PBinOp PAddOp (PVar "a") (PVar "b")))
  ].

Definition t_nested : p_expr :=
  PCall "add" [PCall "double" [PVal (PLitInt 3)]; PVal (PLitInt 1)].

Eval vm_compute in supercompile F_nested 10 [] t_nested.
(* double(3) = 6, add(6, 1) = 7. Expected: PVal (PLitInt 7) *)

(** * 6. Supercompile with open term (variable input)
    When input is unknown, driving stops at variables.
    The supercompiler preserves the structure. *)

Definition t_open : p_expr :=
  PIf (PBinOp PGtOp (PVar "x") (PVal (PLitInt 0)))
      (PBinOp PAddOp (PVar "x") (PVal (PLitInt 1)))
      (PVal (PLitInt 0)).

Eval vm_compute in supercompile [] 10 [] t_open.
(* x is unknown: no reduction possible, returns original structure *)

(** * 7. D1 supercompilation result for is_sorted

    The predicate body is:
      if len(xs) <= 1 then true
      else and(xs[0] <= xs[1], is_sorted(tail(xs)))

    With open input [xs], drive_step can't inline the PCall because
    [xs] is not a PVal.  The whistle fires immediately (no driving).
    D1 folding detects the recursive structure and would emit a Fixpoint,
    but needs symbolic driving of the body (open-term driving). *)

Definition is_sorted_body : p_expr :=
  PIf (PBinOp PLeOp (PBinOp PLenOp (PVar "xs") (PVal PLitUnit))
                    (PVal (PLitInt 1)))
      (PVal (PLitBool true))
      (PBinOp PAndOp
        (PBinOp PLeOp (PVar "xs") (PVar "xs"))  (* simplified: xs[0] <= xs[1] *)
        (PCall "is_sorted" [PCall "tail" [PVar "xs"]])).

Definition F_is_sorted : fn_table :=
  [("is_sorted", (["xs"], is_sorted_body))].

Eval vm_compute in supercompile_full F_is_sorted 5 (PCall "is_sorted" [PVar "xs"]).

(** * 8. Soundness check: constant folding preserves p_eval *)

Example arith_sound : forall fuel,
  p_eval [] fuel t_arith =
  p_eval [] fuel (supercompile [] 10 [] t_arith).
Proof.
  intro fuel.
  apply (supercompile_sound [] 10 [] t_arith fuel).
Qed.
