From Stdlib Require Import ZArith String List.
Require Import Imp.

(** * Weakest Precondition Calculus *)

(** Assertions are predicates on states. *)
Definition assertion := state -> Prop.

(** ** Weakest Precondition for Commands *)

Fixpoint wp (c : com) (Q : assertion) : assertion :=
  match c with
  | CSkip =>
      Q
  | CAss x a =>
      fun s => Q (lupd s x (aeval a s))
  | CSeq c1 c2 =>
      wp c1 (wp c2 Q)
  | CIf b c1 c2 =>
      fun s => (beval b s = true -> wp c1 Q s) /\
               (beval b s = false -> wp c2 Q s)
  | CWhile b inv body =>
      inv
  | CHavoc A =>
      fun s => forall s', (forall x, ~ In x A -> lget s' x = lget s x) -> Q s'
  | CListNew name =>
      fun s => Q (hupd s name len_f (VZ 0))
  | CListAppend name val =>
      fun s => let len := asZ (hget s name len_f) in
               Q (hupd (hupd s name (elem_f len) (aeval val s))
                       name len_f (VZ (len + 1)))
  | CListPop name =>
      fun s => Q (hupd s name len_f (VZ (asZ (hget s name len_f) - 1)))
  | CListSet name idx_e val_e =>
      fun s => Q (hupd s name (elem_f (asZ (aeval idx_e s))) (aeval val_e s))
  | CDictSet name key_e val_e =>
      fun s => let k := asZ (aeval key_e s) in
               let is_new := Z.eqb 0 (asZ (hget s name (dlen_f k))) in
               let old_count := asZ (hget s name count_f) in
               let new_count := old_count + (if is_new then 1 else 0) in
               Q (hupd (hupd (hupd s name (dval_f k) (aeval val_e s))
                             name (dlen_f k) (VZ 1))
                       name count_f (VZ new_count))
  | CDictGet name key_e target =>
      fun s => Q (lupd s target (hget s name (dval_f (asZ (aeval key_e s)))))
  | CDictEnsureList name key_e =>
      fun s => let dk_len := dlen_f (asZ (aeval key_e s)) in
               Q (if Z.eqb (asZ (hget s name dk_len)) 0
                  then hupd s name dk_len (VZ 0)
                  else s)
  | CDictAppend name key_e val_e =>
      fun s => let k := asZ (aeval key_e s) in
               let dk_len := dlen_f k in
               let len := asZ (hget s name dk_len) in
               Q (hupd (hupd s name (elem_f len) (aeval val_e s))
                       name dk_len (VZ (len + 1)))
  | CDictAppendKv name key_e val_e =>
      fun s => let k := asZ (aeval key_e s) in
               let is_new := Z.eqb 0 (asZ (hget s name (dlen_f k))) in
               let c := asZ (hget s name count_f) in
               let new_c := c + (if is_new then 1 else 0) in
               let s1 := hupd (hupd (hupd s name (dval_f k) (aeval val_e s))
                                    name (dlen_f k) (VZ 1))
                              name (elem_f c) (aeval val_e s) in
               Q (hupd (hupd s1 name (elem_f c) (aeval key_e s))
                       name count_f (VZ new_c))
   | CCall name args pre post writes target =>
       fun s => pre s /\ (forall r, post (lupd s target (VZ r)) ->
         Q (clobber (lupd s target (VZ r)) writes) /\
         (forall x, ~ In x (target :: writes) -> lget s x = lget (clobber (lupd s target (VZ r)) writes) x))
  | CAssume P =>
      fun s => P s -> Q s
  end.

(** ** Soundness *)
Theorem wp_sound : forall (c : com) (Q : assertion) s s',
  wp c Q s -> ceval c s s' -> Q s'.
Proof. Admitted.

(** VCG while-exit condition *)
Definition vcg_while_exit (b : bexp) (inv Q : assertion) : Prop :=
  forall s, inv s -> beval b s = false -> Q s.

(** ** Monotonicity *)
Lemma wp_monotone : forall (c : com) (Q1 Q2 : assertion) s,
  (forall s', Q1 s' -> Q2 s') ->
  wp c Q1 s -> wp c Q2 s.
Proof. Admitted.

(** ** Hoare Triple Definition *)

Definition hoare_triple (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall s s', P s -> ceval c s s' -> Q s'.

(** ** Notation *)
Open Scope Z_scope.
