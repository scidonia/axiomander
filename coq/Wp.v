Require Import ZArith String List.
Require Import Imp.

(** * Weakest Precondition Calculus *)

(** Assertions are predicates on states. *)
Definition assertion := state -> Prop.

(** ** Weakest Precondition for Commands *)

(** [wp c Q] is the weakest precondition such that if it holds before
    executing [c], then [Q] holds after (assuming termination). *)
Fixpoint wp (c : com) (Q : assertion) : assertion :=
  match c with
  | CSkip =>
      Q
  | CAss x a =>
      fun s => Q (upd s x (aeval a s))
  | CSeq c1 c2 =>
      wp c1 (wp c2 Q)
  | CIf b c1 c2 =>
      fun s => (beval b s = true -> wp c1 Q s) /\
               (beval b s = false -> wp c2 Q s)
  | CWhile b inv body =>
      inv
  | CHavoc A =>
      fun s => forall s', (forall x, ~ In x A -> s' x = s x) -> Q s'
  | CDictSet name key_e val_e =>
      fun s => let dk := dict_key name (asZ (aeval key_e s)) in
               let is_new := Z.eqb 0 (asZ (s (parray_len_key dk))) in
               let old_count := asZ (s (dict_count_key name)) in
               let new_count := old_count + (if is_new then 1 else 0) in
               Q (upd (upd (upd s dk (aeval val_e s))
                           (parray_len_key dk) (VZ 1))
                      (dict_count_key name) (VZ new_count))
  | CDictGet name key_e target =>
      fun s => Q (upd s target (s (dict_key name (asZ (aeval key_e s)))))
  | CDictEnsureList name key_e =>
      fun s => let dk := dict_key name (asZ (aeval key_e s)) in
               Q (if Z.eqb (asZ (s (parray_len_key dk))) 0
                  then upd s (parray_len_key dk) (VZ 0)
                  else s)
  | CDictAppend name key_e val_e =>
      fun s => let dk := dict_key name (asZ (aeval key_e s)) in
               let len := asZ (s (parray_len_key dk)) in
               Q (upd (upd s (parray_key dk len) (aeval val_e s))
                      (parray_len_key dk) (VZ (len + 1)))
  | CDictAppendKv name key_e val_e =>
      fun s => let dk := dict_key name (asZ (aeval key_e s)) in
               let is_new := Z.eqb 0 (asZ (s (parray_len_key dk))) in
               let c := asZ (s (dict_count_key name)) in
               let new_c := c + (if is_new then 1 else 0) in
               let s1 := upd (upd (upd s dk (aeval val_e s))
                                  (parray_len_key dk) (VZ 1))
                             (parray_key (dict_vals_key name) c) (aeval val_e s) in
               Q (upd (upd s1 (parray_key (dict_keys_key name) c) (aeval key_e s))
                      (dict_count_key name) (VZ new_c))
  | CCall name args pre post writes target =>
      fun s => pre s /\ (forall r, post (upd s target (VZ r)) ->
        Q (clobber (upd s target (VZ r)) writes) /\
        (forall x, ~ In x (target :: writes) -> s x = (clobber (upd s target (VZ r)) writes) x))
  end.

(** ** Soundness — [wp c Q] implies the Hoare triple {wp c Q} c {Q}. *)
Theorem wp_sound : forall (c : com) (Q : assertion) s s',
  wp c Q s -> ceval c s s' -> Q s'.
Proof. Admitted.

(** VCG while-exit condition: invariant + exit → postcondition *)
Definition vcg_while_exit (b : bexp) (inv Q : assertion) : Prop :=
  forall s, inv s -> beval b s = false -> Q s.

(** ** Monotonicity — [wp] preserves implication *)
Lemma wp_monotone : forall (c : com) (Q1 Q2 : assertion) s,
  (forall s', Q1 s' -> Q2 s') ->
  wp c Q1 s -> wp c Q2 s.
Proof. Admitted.

(** ** Hoare Triple Definition *)

Definition hoare_triple (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall s s', P s -> ceval c s s' -> Q s'.

(** ** Notation *)
Open Scope Z_scope.
