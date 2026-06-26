From Stdlib Require Import List ZArith Bool String.
Import ListNotations.
Open Scope Z_scope.

Require Import LambdaA.

(** * Supercompiler for lambda_A with symbolic context. *)

Definition ctx := list (string * p_expr).

(** Look up a variable in the context. *)
Definition ctx_lookup (c : ctx) (x : string) : option p_expr :=
  assoc String.eqb c x.

(** Extend context with a binding (shadows previous). *)
Definition ctx_extend (x : string) (v : p_expr) (c : ctx) : ctx :=
  (x, v) :: c.

(** Context expansion: replace PVar y with its context image
    if it maps to a projection (PListHead/PListTail), one level.
    Used to restore structural relationships for the D1 whistle. *)
Definition ctx_expand_one (c : ctx) (e : p_expr) : p_expr :=
  match e with
  | PVar y =>
      match ctx_lookup c y with
      | Some (PListHead (PVar z)) => PListHead (PVar z)
      | Some (PListTail (PVar z)) => PListTail (PVar z)
      | _ => e
      end
  | _ => e
  end.

(** * 1. Driving — one-step symbolic reduction, context-aware *)

Definition empty_ctx : ctx := nil.

Definition drive_step (F : fn_table) (c : ctx) (t : p_expr) : option p_expr :=
  (** Context-driven reductions for list projections. *)
  match t with
  | PListHead (PVar x) =>
      match ctx_lookup c x with
      | Some (PListCons h _) => Some h
      | Some (PVal (PLitList (v :: _))) => Some (PVal v)
      | _ => None
      end
  | PListTail (PVar x) =>
      match ctx_lookup c x with
      | Some (PListCons _ t) => Some t
      | Some (PVal (PLitList (_ :: rest))) => Some (PVal (PLitList rest))
      | _ => None
      end
  | PListIsNil (PVar x) =>
      match ctx_lookup c x with
      | Some (PListCons _ _) => Some (PVal (PLitBool false))
      | Some (PVal (PLitList [])) => Some (PVal (PLitBool true))
      | Some (PVal (PLitList (_ :: _))) => Some (PVal (PLitBool false))
      | _ => None
      end
  (** Standard reductions. *)
  | PVal _ | PVar _ => None
  | PBinOp op (PVal v1) (PVal v2) =>
      option_map (fun v => PVal v) (binop_eval op v1 v2)
  | PBinOp _ _ _ => None
  | PIf (PVal (PLitBool true)) e1 e2 => Some e1
  | PIf (PVal (PLitBool false)) e1 e2 => Some e2
  | PIf _ _ _ => None
  | PLet x (PVal v) e2 => Some (subst x v e2)
  | PLet _ _ _ => None
  | PListHead (PListCons h _) => Some h
  | PListHead (PVal v) =>
      match v with
      | PLitList (v' :: _) => Some (PVal v')
      | _ => None
      end
  | PListHead _ => None
  | PListTail (PListCons _ t) => Some t
  | PListTail (PVal v) =>
      match v with
      | PLitList (_ :: rest) => Some (PVal (PLitList rest))
      | _ => None
      end
  | PListTail _ => None
  | PListIsNil (PListCons _ _) => Some (PVal (PLitBool false))
  | PListIsNil (PVal (PLitList [])) => Some (PVal (PLitBool true))
  | PListIsNil (PVal (PLitList (_ :: _))) => Some (PVal (PLitBool false))
  | PListIsNil _ => None
  | PListCons (PVal v1) (PVal (PLitList vs)) =>
      Some (PVal (PLitList (v1 :: vs)))
  | PListCons _ _ => None
  | PCall f args =>
      if existsb (fun a => negb (is_value_or_var a)) args then
        None
      else
      match assoc String.eqb F f with
      | Some (params, body) =>
          if forallb is_PVal args then
            let vs := map (fun a => match a with PVal v => v | _ => PLitUnit end) args in
            Some (subst_many (combine params vs) body)
          else
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

(** * 4. Expression equality *)

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

(** * 5. Generalization *)

Definition generalize_args (old_args new_args : list p_expr) (fuel : nat) : list p_expr :=
  new_args.

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

(** * 6. The supercompiler with symbolic context *)

Fixpoint supercompile (F : fn_table) (fuel : nat)
    (history : list p_expr) (cx : ctx) (t : p_expr) : p_expr :=
  match fuel with
  | 0%nat => t
  | S fuel' =>
    match drive_step F cx t with
    | Some t' => supercompile F fuel' (t :: history) cx t'
    | None =>
        match t with
        | PVal _ | PVar _ => t
        | PBinOp op e1 e2 =>
            let e1' := supercompile F fuel' history cx e1 in
            let e2' := supercompile F fuel' history cx e2 in
            let t' := PBinOp op e1' e2' in
            match drive_step F cx t' with
            | Some driven => supercompile F fuel' history cx driven
            | None => t'
            end
        | PIf e0 e1 e2 =>
            let e0' := supercompile F fuel' history cx e0 in
            match e0' with
             | PListIsNil (PVar x) =>
                (** Positive supercompilation via context.
                    Only fire on user-level variables; derived names
                    (containing '.') are left to the D1 whistle. *)
                if match String.index 0 "." x with Some _ => false | None => true end then
                  let hname := String.append x ".h" in
                  let tname := String.append x ".t" in
                  let cx_then := ctx_extend x (PVal (PLitList [])) cx in
                  let cx_else :=
                    ctx_extend tname (PListTail (PVar x))
                      (ctx_extend hname (PListHead (PVar x))
                        (ctx_extend x (PListCons (PVar hname) (PVar tname)) cx)) in
                  let then' := supercompile F fuel' history cx_then e1 in
                  let else' := supercompile F fuel' history cx_else e2 in
                  PIf e0' then' else'
                else
                  let e1' := supercompile F fuel' history cx e1 in
                  let e2' := supercompile F fuel' history cx e2 in
                  PIf e0' e1' e2'
            | _ =>
                let t' := PIf e0' e1 e2 in
                match drive_step F cx t' with
                | Some driven => supercompile F fuel' history cx driven
                | None =>
                    let e1' := supercompile F fuel' history cx e1 in
                    let e2' := supercompile F fuel' history cx e2 in
                    PIf e0' e1' e2'
                end
            end
        | PLet x e1 e2 =>
            let e1' := supercompile F fuel' history cx e1 in
            let e2' := supercompile F fuel' history cx e2 in
            PLet x e1' e2'
        | PListHead e =>
            let e' := supercompile F fuel' history cx e in
            let t' := PListHead e' in
            match drive_step F cx t' with
            | Some driven => supercompile F fuel' history cx driven
            | None => t'
            end
        | PListTail e =>
            let e' := supercompile F fuel' history cx e in
            let t' := PListTail e' in
            match drive_step F cx t' with
            | Some driven => supercompile F fuel' history cx driven
            | None => t'
            end
        | PListIsNil e =>
            let e' := supercompile F fuel' history cx e in
            let t' := PListIsNil e' in
            match drive_step F cx t' with
            | Some driven => supercompile F fuel' history cx driven
            | None => t'
            end
        | PListCons e1 e2 =>
            let e1' := supercompile F fuel' history cx e1 in
            let e2' := supercompile F fuel' history cx e2 in
            let t' := PListCons e1' e2' in
            match drive_step F cx t' with
            | Some driven => supercompile F fuel' history cx driven
            | None => t'
            end
        | PCall f args =>
            let args' := map (supercompile F fuel' history cx) args in
            let t' := PCall f args' in
            let args_expanded := map (ctx_expand_one cx) args' in
            if existsb (fun h => match h with
                                 | PCall fh argsh =>
                                     String.eqb f fh
                                     && forallb2 he_dec argsh args_expanded
                                 | _ => false
                                 end) history then
              t'
            else
              match drive_step F cx t' with
              | Some driven => supercompile F fuel' history cx driven
              | None => t'
              end
        end
    end
  end.

(** Entry point: empty context. *)
Definition scc (F : fn_table) (fuel : nat) (t : p_expr) : p_expr :=
  supercompile F fuel nil nil t.

(** * 7. Soundness *)

Lemma option_None_neq_Some : forall {A} (x : A), None <> Some x.
Proof. discriminate. Qed.

Lemma binop_step_ok : forall F fuel op v1 v2 v,
  binop_eval op v1 v2 = Some v ->
  p_eval F (S (S fuel)) (PBinOp op (PVal v1) (PVal v2)) = p_eval F (S fuel) (PVal v).
Proof.
  intros F fuel op v1 v2 v H. simpl. rewrite H. destruct fuel; simpl; auto.
Qed.

Lemma if_step_ok : forall (F : fn_table) (fuel : nat) (c : ctx) (e1 e2 : p_expr) (b : bool) (t' : p_expr),
  drive_step F c (PIf (PVal (PLitBool b)) e1 e2) = Some t' ->
  p_eval F (S (S fuel)) (PIf (PVal (PLitBool b)) e1 e2) = p_eval F (S fuel) t'.
Proof.
  intros F fuel c e1 e2 b t' Hdr. simpl in Hdr.
  destruct b; inversion Hdr; subst t'; destruct fuel; simpl; auto.
Qed.

Lemma let_step_ok : forall (F : fn_table) (fuel : nat) (c : ctx) (x : string) (v : pl_val) (e2 t' : p_expr),
  drive_step F c (PLet x (PVal v) e2) = Some t' ->
  p_eval F (S (S fuel)) (PLet x (PVal v) e2) = p_eval F (S fuel) t'.
Proof.
  intros F fuel c x v e2 t' Hdr.
  simpl in Hdr; inversion Hdr; subst.
  simpl. destruct fuel; simpl; auto.
Qed.

Lemma head_step_ok : forall (F : fn_table) (fuel : nat) (c : ctx) (v : pl_val) (vs : list pl_val) (t' : p_expr),
  drive_step F c (PListHead (PVal (PLitList (v :: vs)))) = Some t' ->
  p_eval F (S (S fuel)) (PListHead (PVal (PLitList (v :: vs)))) =
  p_eval F (S fuel) t'.
Proof.
  intros F fuel c v vs t' Hdr.
  simpl in Hdr; inversion Hdr; subst.
  destruct fuel; simpl; auto.
Qed.

Lemma tail_step_ok : forall (F : fn_table) (fuel : nat) (c : ctx) (v : pl_val) (vs : list pl_val) (t' : p_expr),
  drive_step F c (PListTail (PVal (PLitList (v :: vs)))) = Some t' ->
  p_eval F (S (S fuel)) (PListTail (PVal (PLitList (v :: vs)))) =
  p_eval F (S fuel) t'.
Proof.
  intros F fuel c v vs t' Hdr.
  simpl in Hdr; inversion Hdr; subst.
  destruct fuel; simpl; auto.
Qed.

Lemma nil_step_ok : forall (F : fn_table) (fuel : nat) (c : ctx) (xs : list pl_val) (t' : p_expr),
  drive_step F c (PListIsNil (PVal (PLitList xs))) = Some t' ->
  p_eval F (S (S fuel)) (PListIsNil (PVal (PLitList xs))) =
  p_eval F (S fuel) t'.
Proof.
  intros F fuel c xs t' Hdr.
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

Lemma call_step_ok : forall (F : fn_table) (fuel : nat) (c : ctx) (fn : string) (args : list p_expr) (t' : p_expr),
  drive_step F c (PCall fn args) = Some t' ->
  p_eval F (S (S fuel)) (PCall fn args) = p_eval F (S fuel) t'.
Admitted.

Lemma drive_step_sound : forall F fuel c t t',
  drive_step F c t = Some t' ->
  p_eval F (S (S fuel)) t = p_eval F (S fuel) t'.
Admitted.

Lemma supercompile_sound : forall F fuel history cx t,
  p_eval F fuel t = p_eval F fuel (supercompile F fuel history cx t).
Admitted.

Lemma generalize_args_is_new : forall old_args new_args fuel,
  generalize_args old_args new_args fuel = new_args.
Proof. intros. unfold generalize_args. reflexivity. Qed.

Lemma generalize_is_id : forall F history t,
  generalize F history t = t.
Proof.
  intros F history t. unfold generalize. destruct history as [|h rest]; auto.
  destruct (he_dec h t); auto.
  destruct h; auto.
  destruct t; auto.
  destruct (String.eqb f f0); auto.
Qed.

Lemma supercompile_adequate : forall F fuel t m v,
  p_eval F m t = Some v ->
  p_eval F m (scc F fuel t) = Some v.
Admitted.
