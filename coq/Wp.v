From Stdlib Require Import ZArith String List.
Require Import Imp.

(** * Weakest Precondition Calculus *)

(** Assertions are predicates on states. *)
Definition assertion := state -> Prop.

(** Outcome predicates: postconditions now range over outcomes, not states.
    This uniformly handles normal returns and exceptions without separate
    proof rules.  A purely normal postcondition [Q : state -> Prop] lifts
    to [fun o => match o with OReturn s' => Q s' | _ => False end]. *)
Definition outcome_pred := outcome -> Prop.

(** [wp_normal Q] lifts a state assertion [Q] into an outcome predicate that
    requires a normal return and discards any raised exception. *)
Definition wp_normal (Q : assertion) : outcome_pred :=
  fun o => match o with OReturn s' => Q s' | ORaise _ _ => False end.

(** ** Weakest Precondition for Commands

    [wp c Phi s] holds iff, for every outcome [o] of [c] from [s], [Phi o].
    [Phi : outcome -> Prop] is the unified postcondition predicate. *)

Fixpoint wp (c : com) (Phi : outcome_pred) : assertion :=
  match c with
  | CSkip =>
      fun s => Phi (OReturn s)
  | CAss x a =>
      fun s => Phi (OReturn (lupd s x (aeval a s)))
  | CSeq c1 c2 =>
      (* c1 must return normally, then c2 must satisfy Phi *)
      wp c1 (fun o =>
        match o with
        | OReturn s' => wp c2 Phi s'
        | ORaise e s' => Phi (ORaise e s')
        end)
  | CIf b c1 c2 =>
      fun s => (beval b s = true  -> wp c1 Phi s) /\
               (beval b s = false -> wp c2 Phi s)
  | CWhile b inv body =>
      (* WP for while: the loop invariant is the precondition.
         Exit postcondition: Phi (OReturn s) when b is false.
         Raising inside the loop: Phi (ORaise e s'). *)
      inv
  | CHavoc A =>
      fun s => forall s', (forall x, ~ In x A -> lget s' x = lget s x) ->
               Phi (OReturn s')
  | CListNew name =>
      fun s => Phi (OReturn (hupd s name len_f (VZ 0)))
  | CListAppend name val =>
      fun s => let len := asZ (hget s name len_f) in
               Phi (OReturn (hupd (hupd s name (elem_f len) (aeval val s))
                                  name len_f (VZ (len + 1))))
  | CListPop name =>
      fun s => Phi (OReturn (hupd s name len_f (VZ (asZ (hget s name len_f) - 1))))
  | CListSet name idx_e val_e =>
      fun s => Phi (OReturn (hupd s name (elem_f (asZ (aeval idx_e s))) (aeval val_e s)))
  | CDictSet name key_e val_e =>
      fun s => let k := asZ (aeval key_e s) in
               let is_new := Z.eqb 0 (asZ (hget s name (dlen_f k))) in
               let old_count := asZ (hget s name count_f) in
               let new_count := old_count + (if is_new then 1 else 0) in
               Phi (OReturn (hupd (hupd (hupd s name (dval_f k) (aeval val_e s))
                                        name (dlen_f k) (VZ 1))
                                  name count_f (VZ new_count)))
  | CDictGet name key_e target =>
      fun s => Phi (OReturn (lupd s target (hget s name (dval_f (asZ (aeval key_e s))))))
  | CDictEnsureList name key_e =>
      fun s => let dk_len := dlen_f (asZ (aeval key_e s)) in
               Phi (OReturn (if Z.eqb (asZ (hget s name dk_len)) 0
                             then hupd s name dk_len (VZ 0)
                             else s))
  | CDictAppend name key_e val_e =>
      fun s => let k := asZ (aeval key_e s) in
               let dk_len := dlen_f k in
               let len := asZ (hget s name dk_len) in
               Phi (OReturn (hupd (hupd s name (elem_f len) (aeval val_e s))
                                  name dk_len (VZ (len + 1))))
  | CDictAppendKv name key_e val_e =>
      fun s => let k := asZ (aeval key_e s) in
               let is_new := Z.eqb 0 (asZ (hget s name (dlen_f k))) in
               let c := asZ (hget s name count_f) in
               let new_c := c + (if is_new then 1 else 0) in
               let s1 := hupd (hupd (hupd s name (dval_f k) (aeval val_e s))
                                    name (dlen_f k) (VZ 1))
                               name (elem_f c) (aeval val_e s) in
               Phi (OReturn (hupd (hupd s1 name (elem_f c) (aeval key_e s))
                                  name count_f (VZ new_c)))
  | CSetAdd name key_e =>
      fun s => let k := asString (aeval key_e s) in
               let is_new := Z.eqb 0 (asZ (hget s name (smem_f k))) in
               let old_count := asZ (hget s name count_f) in
               let new_count := old_count + (if is_new then 1 else 0) in
               Phi (OReturn (hupd (hupd s name (smem_f k) (VZ 1))
                                  name count_f (VZ new_count)))
  | CSetDiscard name key_e =>
      fun s => let k := asString (aeval key_e s) in
               let was_present := Z.eqb 1 (asZ (hget s name (smem_f k))) in
               let old_count := asZ (hget s name count_f) in
               let new_count := old_count - (if was_present then 1 else 0) in
               Phi (OReturn (hupd (hupd s name (smem_f k) (VZ 0))
                                  name count_f (VZ new_count)))
  | CListPopTo name target =>
      fun s => let len := asZ (hget s name len_f) in
               let last_val := hget s name (elem_f (len - 1)) in
               Phi (OReturn (lupd (hupd s name len_f (VZ (len - 1))) target last_val))
  | CCall name args pre post writes target =>
      fun s => pre s /\ (forall r, post (lupd s target (VZ r)) ->
        Phi (OReturn (clobber (lupd s target (VZ r)) writes)) /\
        (forall x, ~ In x (target :: writes) ->
          lget s x = lget (clobber (lupd s target (VZ r)) writes) x))
  | CAssume P =>
      fun s => P s -> Phi (OReturn s)
  | CRaise e =>
      fun s => Phi (ORaise (aeval e s) s)
  | CTry body exc handler =>
      (* If body returns normally, skip handler (return as-is).
         If body raises, bind the exception to [exc] and run handler. *)
      wp body (fun o =>
        match o with
        | OReturn s' => Phi (OReturn s')
        | ORaise e s' => wp handler Phi (lupd s' exc e)
        end)
  end.

(** ** Backward compatibility: lift a state postcondition to outcome_pred.
    All existing [wp c (wp_normal Q) s] proofs correspond to the old
    [wp_old c Q s] where exceptions make the goal [False] (i.e., the old
    semantics simply did not model exceptions). *)

(** ** Soundness *)
Theorem wp_sound : forall (c : com) (Phi : outcome_pred) s o,
  wp c Phi s -> ceval c s o -> Phi o.
Proof. Admitted.

(** VCG while-exit condition (outcome form) *)
Definition vcg_while_exit (b : bexp) (inv : assertion) (Phi : outcome_pred) : Prop :=
  forall s, inv s -> beval b s = false -> Phi (OReturn s).

(** ** Monotonicity *)
Lemma wp_monotone : forall (c : com) (Phi1 Phi2 : outcome_pred) s,
  (forall o, Phi1 o -> Phi2 o) ->
  wp c Phi1 s -> wp c Phi2 s.
Proof. Admitted.

(** ** Hoare Triple Definition (outcome form) *)

Definition hoare_triple (P : assertion) (c : com) (Phi : outcome_pred) : Prop :=
  forall s o, P s -> ceval c s o -> Phi o.

(** Convenience: Hoare triple for purely normal programs (no exceptions). *)
Definition hoare_triple_normal (P : assertion) (c : com) (Q : assertion) : Prop :=
  hoare_triple P c (wp_normal Q).

(** ** Notation *)
Open Scope Z_scope.
