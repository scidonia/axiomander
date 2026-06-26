From Stdlib Require Import List ZArith Bool String.
Import ListNotations.
Open Scope Z_scope.

Require Import LambdaA.

(** * Supercompiler for lambda_A. *)

(** * 1. Driving — one-step symbolic reduction *)

Definition drive_step (F : fn_table) (t : p_expr) : option p_expr :=
  match t with
  | PVal _ | PVar _ => None
  (* Binary ops: evaluate when both operands are literals. *)
  | PBinOp op (PVal v1) (PVal v2) =>
      option_map (fun v => PVal v) (binop_eval op v1 v2)
  | PBinOp _ _ _ => None
  (* If: prune when condition is a literal. *)
  | PIf (PVal (PLitBool true)) e1 e2 => Some e1
  | PIf (PVal (PLitBool false)) e1 e2 => Some e2
  | PIf _ _ _ => None
  (* Let: inline only when the binding is a literal value.
     Symbolic bindings (introduced by case-splitting) are preserved
     for information propagation. *)
  | PLet x (PVal v) e2 => Some (subst x v e2)
  | PLet _ _ _ => None
  (* Head: extract first element. *)
  | PListHead (PListCons h _) => Some h
  | PListHead (PVal v) =>
      match v with
      | PLitList (v' :: _) => Some (PVal v')
      | _ => None
      end
  | PListHead _ => None
  (* Tail: return the remainder. *)
  | PListTail (PListCons _ t) => Some t
  | PListTail (PVal v) =>
      match v with
      | PLitList (_ :: rest) => Some (PVal (PLitList rest))
      | _ => None
      end
  | PListTail _ => None
  (* IsNil: check if a list is empty. *)
  | PListIsNil (PListCons _ _) => Some (PVal (PLitBool false))
  | PListIsNil (PVal (PLitList [])) => Some (PVal (PLitBool true))
  | PListIsNil (PVal (PLitList (_ :: _))) => Some (PVal (PLitBool false))
  | PListIsNil _ => None
  (* Cons: literal evaluation. *)
  | PListCons (PVal v1) (PVal (PLitList vs)) =>
      Some (PVal (PLitList (v1 :: vs)))
  | PListCons _ _ => None
  (* Call: ALWAYS inline from the fn_table — whistle handles recursion. *)
  | PCall f args =>
      match assoc String.eqb F f with
      | Some (params, body) =>
          if forallb is_PVal args then
            (* All args are literals: extract values, use pl_val substitution. *)
            let vs := map (fun a => match a with PVal v => v | _ => PLitUnit end) args in
            Some (subst_many (combine params vs) body)
          else
            (* Symbolic args: use expression substitution. *)
            Some (subst_many_expr (combine params args) body)
      | None => None
      end
  end.

(** * 2. Homeomorphic embedding (the whistle) *)

Inductive he : p_expr -> p_expr -> Prop :=
  | he_var : forall x, he (PVar x) (PVar x)
  | he_val : forall v, he (PVal v) (PVal v)
  | he_dive_binop_l : forall h op e1 e2, he h e1 -> he h (PBinOp op e1 e2)
  | he_dive_binop_r : forall h op e1 e2, he h e2 -> he h (PBinOp op e1 e2)
  | he_dive_if_c : forall h e0 e1 e2, he h e0 -> he h (PIf e0 e1 e2)
  | he_dive_if_t : forall h e0 e1 e2, he h e1 -> he h (PIf e0 e1 e2)
  | he_dive_if_e : forall h e0 e1 e2, he h e2 -> he h (PIf e0 e1 e2)
  | he_dive_let_bind : forall h x e1 e2, he h e1 -> he h (PLet x e1 e2)
  | he_dive_let_body : forall h x e1 e2, he h e2 -> he h (PLet x e1 e2)
  | he_dive_call : forall h f args a, In a args -> he h a -> he h (PCall f args)
  | he_dive_head : forall h e, he h e -> he h (PListHead e)
  | he_dive_tail : forall h e, he h e -> he h (PListTail e)
  | he_dive_isnil : forall h e, he h e -> he h (PListIsNil e)
  | he_dive_cons_l : forall h e1 e2, he h e1 -> he h (PListCons e1 e2)
  | he_dive_cons_r : forall h e1 e2, he h e2 -> he h (PListCons e1 e2)
  | he_couple_cons : forall a1 b1 a2 b2, he a1 a2 -> he b1 b2 -> he (PListCons a1 b1) (PListCons a2 b2)
  | he_couple_binop : forall op a1 b1 a2 b2, he a1 a2 -> he b1 b2 -> he (PBinOp op a1 b1) (PBinOp op a2 b2)
  | he_couple_if : forall c1 t1 e1 c2 t2 e2, he c1 c2 -> he t1 t2 -> he e1 e2 -> he (PIf c1 t1 e1) (PIf c2 t2 e2)
  | he_couple_let : forall x b1 e1 b2 e2, he b1 b2 -> he e1 e2 -> he (PLet x b1 e1) (PLet x b2 e2)
  | he_couple_call : forall f args1 args2, Forall2 he args1 args2 -> he (PCall f args1) (PCall f args2).

(** * 3. Decidable homeomorphic embedding *)

Fixpoint forallb2 {A B} (f : A -> B -> bool) (xs : list A) (ys : list B) : bool :=
  match xs, ys with
  | x::xs', y::ys' => f x y && forallb2 f xs' ys'
  | [], [] => true
  | _, _ => false
  end.

Fixpoint he_dec (h t : p_expr) : bool :=
  match h, t with
  | PVar x, PVar y => String.eqb x y
  | PVal v1, PVal v2 => pl_val_eqb v1 v2
  | PBinOp op1 a1 b1, PBinOp op2 a2 b2 =>
      pl_binop_eqb op1 op2 && he_dec a1 a2 && he_dec b1 b2
  | PIf c1 t1 e1, PIf c2 t2 e2 =>
      he_dec c1 c2 && he_dec t1 t2 && he_dec e1 e2
  | PLet _ b1 e1, PLet _ b2 e2 =>
      he_dec b1 b2 && he_dec e1 e2
  | PCall f1 args1, PCall f2 args2 =>
      String.eqb f1 f2 && forallb2 he_dec args1 args2
  | PListHead e1, PListHead e2 => he_dec e1 e2
  | PListTail e1, PListTail e2 => he_dec e1 e2
  | PListIsNil e1, PListIsNil e2 => he_dec e1 e2
  | PListCons a1 b1, PListCons a2 b2 => he_dec a1 a2 && he_dec b1 b2
  | _, _ =>
      match t with
      | PBinOp _ e1 e2 => he_dec h e1 || he_dec h e2
      | PIf e0 e1 e2 => he_dec h e0 || he_dec h e1 || he_dec h e2
      | PLet _ e1 e2 => he_dec h e1 || he_dec h e2
      | PCall _ args => existsb (he_dec h) args
      | PListHead e => he_dec h e
      | PListTail e => he_dec h e
      | PListIsNil e => he_dec h e
      | PListCons e1 e2 => he_dec h e1 || he_dec h e2
      | _ => false
      end
  end.

Definition whistle_dec (history : list p_expr) (t : p_expr) : bool :=
  existsb (fun h => he_dec h t) history.

(** * 4. Expression equality (helper for generalization) *)

Fixpoint pexpr_eqb (e1 e2 : p_expr) : bool :=
  match e1, e2 with
  | PVar x1, PVar x2 => String.eqb x1 x2
  | PVal v1, PVal v2 => pl_val_eqb v1 v2
  | PBinOp op1 a1 b1, PBinOp op2 a2 b2 =>
      pl_binop_eqb op1 op2 && pexpr_eqb a1 a2 && pexpr_eqb b1 b2
  | PCall f1 args1, PCall f2 args2 =>
      String.eqb f1 f2 && forallb2 pexpr_eqb args1 args2
  | PIf c1 t1 e1, PIf c2 t2 e2 =>
      pexpr_eqb c1 c2 && pexpr_eqb t1 t2 && pexpr_eqb e1 e2
  | PLet x1 b1 e1, PLet x2 b2 e2 =>
      String.eqb x1 x2 && pexpr_eqb b1 b2 && pexpr_eqb e1 e2
  | PListHead e1, PListHead e2 => pexpr_eqb e1 e2
  | PListTail e1, PListTail e2 => pexpr_eqb e1 e2
  | PListIsNil e1, PListIsNil e2 => pexpr_eqb e1 e2
  | PListCons a1 b1, PListCons a2 b2 => pexpr_eqb a1 a2 && pexpr_eqb b1 b2
  | _, _ => false
  end.

(** * 5. Generalization of call arguments *)

Definition generalize_args (old_args new_args : list p_expr) (fuel : nat) : list p_expr :=
  new_args.

(** Guard: only case-split on user-level variables.
    Derived names contain a dot (introduced by a prior split). *)
Definition is_derived_var (x : string) : bool :=
  match String.index 0 "." x with
  | Some _ => true
  | None => false
  end.

(** Substitute head/tail projections of [x] with fresh variable
    names [hname] and [tname] in [e].  Leaves [PVar x] itself
    untouched so recursive calls retain the structural argument. *)
Fixpoint subst_projections (x hname tname : string) (e : p_expr) : p_expr :=
  match e with
  | PListHead (PVar y) =>
      if String.eqb x y then PVar hname else PListHead (PVar y)
  | PListTail (PVar y) =>
      if String.eqb x y then PVar tname else PListTail (PVar y)
  | PVar _ | PVal _ => e
  | PBinOp op e1 e2 =>
      PBinOp op (subst_projections x hname tname e1)
                (subst_projections x hname tname e2)
  | PCall f args =>
      PCall f args   (* preserve args for D1 structural whistle *)
  | PIf e0 e1 e2 =>
      PIf (subst_projections x hname tname e0)
          (subst_projections x hname tname e1)
          (subst_projections x hname tname e2)
  | PLet y e1 e2 =>
      PLet y (subst_projections x hname tname e1)
             (subst_projections x hname tname e2)
  | PListHead e => PListHead (subst_projections x hname tname e)
  | PListTail e => PListTail (subst_projections x hname tname e)
  | PListIsNil e => PListIsNil (subst_projections x hname tname e)
  | PListCons e1 e2 =>
      PListCons (subst_projections x hname tname e1)
                (subst_projections x hname tname e2)
  end.

(** * 6. Generalization *)

Definition generalize (F : fn_table) (history : list p_expr) (t : p_expr) : p_expr :=
  match history with
  | [] => t
  | h :: _ =>
      if he_dec h t then
        match h, t with
        | PCall fh argsh, PCall ft argst =>
            if String.eqb fh ft then
              let args' := generalize_args argsh argst 10%nat in
              PCall ft args'
            else t
        | _, _ => t
        end
      else t
  end.

(** * 7. The supercompiler *)

Fixpoint supercompile (F : fn_table) (fuel : nat) (history : list p_expr) (t : p_expr) : p_expr :=
  match fuel with
  | 0%nat => t
  | S fuel' =>
    match drive_step F t with
    | Some t' => supercompile F fuel' (t :: history) t'
    | None =>
        match t with
        | PVal _ | PVar _ => t
        | PBinOp op e1 e2 =>
            let e1' := supercompile F fuel' history e1 in
            let e2' := supercompile F fuel' history e2 in
            supercompile F fuel' history (PBinOp op e1' e2')
        | PIf e0 e1 e2 =>
            let e0' := supercompile F fuel' history e0 in
            match e0' with
            | PListIsNil (PVar x) =>
                (** Positive supercompilation: case-split on a structural
                    variable.  Only fire on user-level variables (no '.'
                    in the name); derived variables like xs.h / xs.t
                    introduced by a prior split are left to the whistle. *)
                if is_derived_var x then
                  let e1' := supercompile F fuel' history e1 in
                  let e2' := supercompile F fuel' history e2 in
                  PIf e0' e1' e2'
                else
                  let then' := subst x (PLitList []) e1 in
                  let then'' := supercompile F fuel' history then' in
                  let hname := String.append x ".h" in
                  let tname := String.append x ".t" in
                  let else_body_subst := subst_projections x hname tname e2 in
                  let else_body :=
                    PLet hname (PListHead (PVar x))
                      (PLet tname (PListTail (PVar x)) else_body_subst) in
                  let else' := supercompile F fuel' history else_body in
                  PIf e0' then'' else'
            | _ =>
                let t' := PIf e0' e1 e2 in
                match drive_step F t' with
                | Some driven => supercompile F fuel' history driven
                | None =>
                    let e1' := supercompile F fuel' history e1 in
                    let e2' := supercompile F fuel' history e2 in
                    PIf e0' e1' e2'
                end
            end
        | PLet x e1 e2 =>
            let e1' := supercompile F fuel' history e1 in
            let e2' := supercompile F fuel' history e2 in
            PLet x e1' e2'
        | PListHead e =>
            let e' := supercompile F fuel' history e in
            supercompile F fuel' history (PListHead e')
        | PListTail e =>
            let e' := supercompile F fuel' history e in
            supercompile F fuel' history (PListTail e')
        | PListIsNil e =>
            let e' := supercompile F fuel' history e in
            supercompile F fuel' history (PListIsNil e')
        | PListCons e1 e2 =>
            let e1' := supercompile F fuel' history e1 in
            let e2' := supercompile F fuel' history e2 in
            supercompile F fuel' history (PListCons e1' e2')
        | PCall f args =>
            let args' := map (supercompile F fuel' history) args in
            let t' := PCall f args' in
            (** D1 strict whistle: when a history entry is a PCall to
                the same function and the current args are structurally
                smaller, stop inlining — leave as residual. *)
            if existsb (fun h => match h with
                                 | PCall fh argsh =>
                                     String.eqb f fh
                                     && forallb2 he_dec argsh args'
                                 | _ => false
                                 end) history then
              t'
            else
              supercompile F fuel' history t'
        end
    end
  end.

(** * 8. Soundness *)

Lemma binop_step_ok : forall F fuel op v1 v2 v,
  binop_eval op v1 v2 = Some v ->
  p_eval F (S (S fuel)) (PBinOp op (PVal v1) (PVal v2)) = p_eval F (S fuel) (PVal v).
Proof.
  intros F fuel op v1 v2 v H. simpl. rewrite H. destruct fuel; simpl; auto.
Qed.

Lemma if_step_ok : forall F fuel e1 e2 b t',
  drive_step F (PIf (PVal (PLitBool b)) e1 e2) = Some t' ->
  p_eval F (S (S fuel)) (PIf (PVal (PLitBool b)) e1 e2) = p_eval F (S fuel) t'.
Proof.
  intros F fuel e1 e2 b t' Hdr. unfold drive_step in Hdr. simpl in Hdr.
  destruct b; inversion Hdr; subst t'; destruct fuel; simpl; auto.
Qed.

Lemma let_step_ok : forall F fuel x v e2 t',
  drive_step F (PLet x (PVal v) e2) = Some t' ->
  p_eval F (S (S fuel)) (PLet x (PVal v) e2) = p_eval F (S fuel) t'.
Proof.
  intros F fuel x v e2 t' Hdr.
  simpl in Hdr; inversion Hdr; subst. (* t' = subst x v e2 *)
  simpl. (* p_eval reduces PLet to ... subst x v e2 *)
  destruct fuel; simpl; auto.
Qed.

Lemma head_step_ok : forall F fuel v vs t',
  drive_step F (PListHead (PVal (PLitList (v :: vs)))) = Some t' ->
  p_eval F (S (S fuel)) (PListHead (PVal (PLitList (v :: vs)))) =
  p_eval F (S fuel) t'.
Proof.
  intros F fuel v vs t' Hdr.
  simpl in Hdr; inversion Hdr; subst.
  destruct fuel; simpl; auto.
Qed.

Lemma tail_step_ok : forall F fuel v vs t',
  drive_step F (PListTail (PVal (PLitList (v :: vs)))) = Some t' ->
  p_eval F (S (S fuel)) (PListTail (PVal (PLitList (v :: vs)))) =
  p_eval F (S fuel) t'.
Proof.
  intros F fuel v vs t' Hdr.
  simpl in Hdr; inversion Hdr; subst.
  destruct fuel; simpl; auto.
Qed.

Lemma nil_step_ok : forall F fuel xs t',
  drive_step F (PListIsNil (PVal (PLitList xs))) = Some t' ->
  p_eval F (S (S fuel)) (PListIsNil (PVal (PLitList xs))) =
  p_eval F (S fuel) t'.
Proof.
  intros F fuel xs t' Hdr.
  simpl in Hdr.
  destruct xs; inversion Hdr; subst; destruct fuel; simpl; auto.
Qed.

Lemma is_PVal_eval : forall F fuel args,
  forallb is_PVal args = true ->
  forallb (fun ov => match ov with Some _ => true | None => false end)
          (map (p_eval F (S fuel)) args) = true.
Proof.
  intros F fuel args H.
  induction args as [|a rest IH]; simpl in *; auto.
  destruct a; simpl in H; try discriminate.
  simpl. apply IH. exact H.
Qed.

Lemma p_eval_PCall : forall F fuel fn args,
  p_eval F (S fuel) (PCall fn args) =
  match assoc String.eqb F fn with
  | Some (params, body) =>
      if forallb (fun ov => match ov with Some _ => true | None => false end)
                 (map (p_eval F fuel) args)
      then p_eval F fuel (subst_many (combine params
             (map (fun ov => match ov with Some v => v | None => PLitUnit end)
                  (map (p_eval F fuel) args))) body)
      else None
  | None => None
  end.
Proof. intros. simpl. reflexivity. Qed.

Lemma map_is_PVal_eval : forall F fuel args,
  forallb is_PVal args = true ->
  map (fun ov => match ov with Some v => v | None => PLitUnit end)
      (map (p_eval F (S fuel)) args) =
  map (fun a => match a with PVal v => v | _ => PLitUnit end) args.
Proof.
  intros F fuel args H. induction args as [|a rest IH]; simpl in *; auto.
  destruct a; simpl in H; try discriminate. simpl. rewrite IH; auto.
Qed.

Lemma call_step_ok : forall F fuel fn args t',
  drive_step F (PCall fn args) = Some t' ->
  p_eval F (S (S fuel)) (PCall fn args) = p_eval F (S fuel) t'.
Proof.
  intros F fuel fn args t' Hdr.
  unfold drive_step in Hdr.
  destruct (assoc String.eqb F fn) as [[params body]|] eqn:Hassoc;
    [| simpl in Hdr; elim (option_None_neq_Some _ _ Hdr)].
  destruct (forallb is_PVal args) eqn:Hargs.
  - (* All literal args: old path. *)
    simpl in Hdr. inversion Hdr. subst t'.
    rewrite (p_eval_PCall F (S fuel) fn args).
    fold String.eqb in Hassoc. rewrite Hassoc.
    rewrite (is_PVal_eval F fuel args Hargs).
    rewrite (map_is_PVal_eval F fuel args Hargs). reflexivity.
  - (* Symbolic args: new path — admit for now. *)
    simpl in Hdr. inversion Hdr. subst t'. Admitted.

Lemma drive_step_sound : forall F fuel t t',
  drive_step F t = Some t' ->
  p_eval F (S (S fuel)) t = p_eval F (S fuel) t'.
Admitted.

Lemma generalize_args_is_new : forall old_args new_args fuel,
  generalize_args old_args new_args fuel = new_args.
Proof. intros. unfold generalize_args. reflexivity. Qed.

Lemma generalize_is_id : forall F history t,
  generalize F history t = t.
Proof.
  intros F history t.
  unfold generalize.
  destruct history as [|h rest]; auto.
  destruct (he_dec h t); auto.
  destruct h; auto; destruct t; auto.
  unfold generalize_args. destruct (String.eqb f f0); auto.
Qed.

Lemma generalize_sound_with_fold : forall F history t fuel,
  p_eval F fuel (generalize F history t) = p_eval F fuel t.
Proof.
  intros. rewrite generalize_is_id. reflexivity.
Qed.

Theorem supercompile_sound : forall F n history t fuel,
  p_eval F fuel t = p_eval F fuel (supercompile F n history t).
Proof.
Admitted.
