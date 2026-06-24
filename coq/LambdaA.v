From Stdlib Require Import List ZArith Bool String.
From Stdlib Require Import PrimFloat.
Import ListNotations.
Open Scope Z_scope.

(** * Lambda_A: the pure, terminating fragment of the Snakelet term language.

    Defines the core calculus from fluid-contract-language-theory.md §1:
      Types    τ ::= int | bool | str | float | list τ | tuple τ | dict τ τ | set τ | unit
      Values   v ::= n | b | s | f | [v,…] | (v,…) | {v↦v,…} | {v,…} | ()
      Ops      ⊕ ::= + | − | × | / | = | < | ≤ | > | ≥ | ∧ | ∨ | …
      Terms    t ::= x | v | t ⊕ t | f(t,…,t) | if t then t else t | let x = t in t

    Bounded recursors (forallb, existsb, countb, fold_left_acc, filterb)
    from [ListPredicates.v] are the target for quantified predicates.
    Structural recursion (D1) and well-founded recursion (D2) are supported
    via named function calls ([PCall]) to a function table. *)

(** * Values *)

Inductive pl_val :=
  | PLitInt (n : Z)
  | PLitBool (b : bool)
  | PLitString (s : string)
  | PLitFloat (f : float)
  | PLitList (vs : list pl_val)
  | PLitTuple (vs : list pl_val)
  | PLitDict (kvs : list (pl_val * pl_val))
  | PLitSet (vs : list pl_val)
  | PLitUnit.

(** * Pure operators *)

Inductive pl_binop :=
  | PAddOp | PSubOp | PMulOp | PDivOp | PModOp
  | PEqOp | PLeOp | PLtOp | PGtOp | PGeOp | PNeOp
  | PAndOp | POrOp
  | PInOp | PLenOp | PAppendOp
  | PStartsWithOp | PEndsWithOp | PToLowerOp | PToUpperOp.

(** Decidable equality for operators (used in homeomorphic embedding). *)

Definition pl_binop_eqb (op1 op2 : pl_binop) : bool :=
  match op1, op2 with
  | PAddOp, PAddOp => true
  | PSubOp, PSubOp => true
  | PMulOp, PMulOp => true
  | PDivOp, PDivOp => true
  | PModOp, PModOp => true
  | PEqOp, PEqOp => true
  | PLeOp, PLeOp => true
  | PLtOp, PLtOp => true
  | PGtOp, PGtOp => true
  | PGeOp, PGeOp => true
  | PNeOp, PNeOp => true
  | PAndOp, PAndOp => true
  | POrOp, POrOp => true
  | PInOp, PInOp => true
  | PLenOp, PLenOp => true
  | PAppendOp, PAppendOp => true
  | PStartsWithOp, PStartsWithOp => true
  | PEndsWithOp, PEndsWithOp => true
  | PToLowerOp, PToLowerOp => true
  | PToUpperOp, PToUpperOp => true
  | _, _ => false
  end.

(** * Expressions *)

Inductive p_expr :=
  | PVar (x : string)
  | PVal (v : pl_val)
  | PBinOp (op : pl_binop) (e1 e2 : p_expr)
  | PCall (f : string) (args : list p_expr)
  | PIf (e0 e1 e2 : p_expr)
  | PLet (x : string) (e1 e2 : p_expr).

(** * Value equality test (conservative: compound constructors match
    by constructor only, not element-wise — safe for whistle detection). *)

Definition pl_val_eqb (v1 v2 : pl_val) : bool :=
  match v1, v2 with
  | PLitInt n1, PLitInt n2 => Z.eqb n1 n2
  | PLitBool b1, PLitBool b2 => Bool.eqb b1 b2
  | PLitString s1, PLitString s2 => String.eqb s1 s2
  | PLitFloat _, PLitFloat _ =>
      (** IEEE 754: NaN ≠ NaN, so PrimFloat.eqb is not reflexive for NaN.
          Conservative: return false — the whistle misses float coupling
          but is never unsound. *) false
  | PLitList _, PLitList _ => true
  | PLitTuple _, PLitTuple _ => true
  | PLitDict _, PLitDict _ => true
  | PLitSet _, PLitSet _ => true
  | PLitUnit, PLitUnit => true
  | _, _ => false
  end.

(** [option_None_neq_Some] works for all types, including those containing
    primitive [float].  The [f_equal] trick with a boolean discriminator
    avoids the kernel's equality scheme, which cannot be generated for
    types transitively containing [float]. *)
Lemma option_None_neq_Some : forall A (x : A), None <> Some x.
Proof.
  intros A x H.
  apply (f_equal (fun o => match o with None => true | Some _ => false end)) in H.
  simpl in H. discriminate.
Qed.

(** [pl_val_eqb_refl] holds for non-float values.
    For floats, [pl_val_eqb] conservatively returns [false] because
    IEEE 754 NaN ≠ NaN, so reflexivity would be unsound. *)
Lemma pl_val_eqb_refl_non_float : forall v, 
  (forall f, v <> PLitFloat f) ->
  pl_val_eqb v v = true.
Proof.
  destruct v; intros Hnotfloat; simpl; auto;
  try apply Z.eqb_refl; try apply Bool.eqb_reflx; try apply String.eqb_refl.
  exfalso. apply (Hnotfloat f). reflexivity.
Qed.

(** * Substitution *)

Fixpoint subst (x : string) (v : pl_val) (e : p_expr) : p_expr :=
  match e with
  | PVar y => if String.eqb x y then PVal v else PVar y
  | PVal _ => e
  | PBinOp op e1 e2 => PBinOp op (subst x v e1) (subst x v e2)
  | PCall f args => PCall f (List.map (subst x v) args)
  | PIf e0 e1 e2 => PIf (subst x v e0) (subst x v e1) (subst x v e2)
  | PLet y e1 e2 =>
      PLet y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  end.

(** * Helper list functions *)

Fixpoint combine {A B} (xs : list A) (ys : list B) : list (A * B) :=
  match xs, ys with
  | x::xs', y::ys' => (x,y) :: combine xs' ys'
  | _, _ => []
  end.

Fixpoint flat_map {A B} (f : A -> list B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: rest => f x ++ flat_map f rest
  end.

Fixpoint assoc {A B} (eqb : A -> A -> bool) (alist : list (A * B)) (k : A) : option B :=
  match alist with
  | [] => None
  | (k', v) :: rest => if eqb k k' then Some v else assoc eqb rest k
  end.

Definition option_map {A B} (f : A -> B) (x : option A) : option B :=
  match x with Some a => Some (f a) | None => None end.

(** * Free variables *)

Fixpoint fv (e : p_expr) : list string :=
  match e with
  | PVar x => [x]
  | PVal _ => []
  | PBinOp _ e1 e2 => fv e1 ++ fv e2
  | PCall _ args => flat_map fv args
  | PIf e0 e1 e2 => fv e0 ++ fv e1 ++ fv e2
  | PLet x e1 e2 => fv e1 ++ (filter (fun y => negb (String.eqb x y)) (fv e2))
  end.

Definition is_closed (e : p_expr) : bool :=
  match fv e with [] => true | _ => false end.

(** [subst_closed] — substitution does not affect closed expressions.
    Full proof deferred to [LambdaAProps.v] (needs auxiliary lemmas
    about [fv] and [flat_map] for the [PCall] case). *)

(** * Primitive operator evaluation *)

Definition binop_eval (op : pl_binop) (v1 v2 : pl_val) : option pl_val :=
  match op, v1, v2 with
  | PAddOp, PLitInt n1, PLitInt n2 => Some (PLitInt (n1 + n2))
  | PSubOp, PLitInt n1, PLitInt n2 => Some (PLitInt (n1 - n2))
  | PMulOp, PLitInt n1, PLitInt n2 => Some (PLitInt (n1 * n2))
  | PDivOp, PLitInt n1, PLitInt n2 =>
      if Z.eqb n2 0 then None else Some (PLitInt (Z.div n1 n2))
  | PModOp, PLitInt n1, PLitInt n2 =>
      if Z.eqb n2 0 then None else Some (PLitInt (Z.modulo n1 n2))
  | PEqOp, PLitInt n1, PLitInt n2 => Some (PLitBool (Z.eqb n1 n2))
  | PEqOp, PLitBool b1, PLitBool b2 => Some (PLitBool (Bool.eqb b1 b2))
  | PEqOp, PLitString s1, PLitString s2 => Some (PLitBool (String.eqb s1 s2))
  | PEqOp, PLitFloat f1, PLitFloat f2 => Some (PLitBool (PrimFloat.eqb f1 f2))
  | PNeOp, PLitInt n1, PLitInt n2 => Some (PLitBool (negb (Z.eqb n1 n2)))
  | PNeOp, PLitBool b1, PLitBool b2 => Some (PLitBool (negb (Bool.eqb b1 b2)))
  | PLeOp, PLitInt n1, PLitInt n2 => Some (PLitBool (Z.leb n1 n2))
  | PLtOp, PLitInt n1, PLitInt n2 => Some (PLitBool (Z.ltb n1 n2))
  | PGtOp, PLitInt n1, PLitInt n2 => Some (PLitBool (Z.gtb n1 n2))
  | PGeOp, PLitInt n1, PLitInt n2 => Some (PLitBool (Z.geb n1 n2))
  | PAndOp, PLitBool b1, PLitBool b2 => Some (PLitBool (b1 && b2))
  | POrOp, PLitBool b1, PLitBool b2 => Some (PLitBool (b1 || b2))
  | PAddOp, PLitString s1, PLitString s2 => Some (PLitString (String.append s1 s2))
  | PLenOp, PLitString s, _ => Some (PLitInt (Z.of_nat (String.length s)))
  | PLenOp, PLitList vs, _ => Some (PLitInt (Z.of_nat (List.length vs)))
  | PAppendOp, PLitList vs1, PLitList vs2 => Some (PLitList (vs1 ++ vs2))
  | _, _, _ => None
  end.

(** Determinism of binop_eval *)

Lemma binop_eval_det : forall op v1 v2 v v',
  binop_eval op v1 v2 = Some v ->
  binop_eval op v1 v2 = Some v' ->
  v = v'.
Proof.
  intros op v1 v2 v v' H1 H2.
  rewrite H1 in H2. inversion H2. reflexivity.
Qed.

(** * Multi-substitution *)

Fixpoint subst_many (subs : list (string * pl_val)) (e : p_expr) : p_expr :=
  match subs with
  | [] => e
  | (x, v) :: rest => subst x v (subst_many rest e)
  end.

(** * Function table type *)

Definition fn_table := list (string * (list string * p_expr)).
  (* (name, (parameter_names, body)) — explicit parentheses for right-assoc *)

(** * Pure evaluator (fuel-bounded, for closed terms)

    [p_eval F n e] evaluates closed [e] with function table [F] using
    [n] units of fuel.  Returns [None] only if fuel is exhausted or
    the term is open / calls an undefined function. *)

Fixpoint p_eval (F : fn_table) (fuel : nat) (e : p_expr) : option pl_val :=
  match fuel with
  | 0%nat => None
  | S fuel' =>
    match e with
    | PVal v => Some v
    | PVar _ => None
    | PBinOp op e1 e2 =>
        match p_eval F fuel' e1, p_eval F fuel' e2 with
        | Some v1, Some v2 => binop_eval op v1 v2
        | _, _ => None
        end
    | PIf e0 e1 e2 =>
        match p_eval F fuel' e0 with
        | Some (PLitBool true) => p_eval F fuel' e1
        | Some (PLitBool false) => p_eval F fuel' e2
        | _ => None
        end
    | PLet x e1 e2 =>
        match p_eval F fuel' e1 with
        | Some v => p_eval F fuel' (subst x v e2)
        | None => None
        end
     | PCall f args =>
        match assoc String.eqb F f with
        | Some (params, body) =>
            if forallb (fun ov => match ov with Some _ => true | None => false end)
                       (map (p_eval F fuel') args) then
              p_eval F fuel' (subst_many (combine params
                (map (fun ov => match ov with Some v => v | None => PLitUnit end)
                     (map (p_eval F fuel') args))) body)
            else None
        | None => None
        end
    end
  end.

(** * Expression-level utilities *)

Definition is_PVal (e : p_expr) : bool :=
  match e with PVal _ => true | _ => false end.

Definition is_PVar (e : p_expr) : bool :=
  match e with PVar _ => true | _ => false end.

Definition is_value_or_var (e : p_expr) : bool :=
  is_PVal e || is_PVar e.

(** Sub-expressions of a compound expression. *)

Definition subexprs (e : p_expr) : list p_expr :=
  match e with
  | PVal _ | PVar _ => []
  | PBinOp _ e1 e2 => [e1; e2]
  | PCall _ args => args
  | PIf e0 e1 e2 => [e0; e1; e2]
  | PLet _ e1 e2 => [e1; e2]
  end.

(** Rebuild a compound expression from its sub-expressions. *)

Definition rebuild (shape : p_expr) (subs : list p_expr) : p_expr :=
  match shape, subs with
  | PBinOp op _ _, [e1; e2] => PBinOp op e1 e2
  | PCall f _, args => PCall f args
  | PIf _ _ _, [e0; e1; e2] => PIf e0 e1 e2
  | PLet x _ _, [e1; e2] => PLet x e1 e2
  | _, _ => shape
  end.

(** * Value classification predicates *)

Definition is_pl_int (v : pl_val) : bool :=
  match v with PLitInt _ => true | _ => false end.

Definition is_pl_bool (v : pl_val) : bool :=
  match v with PLitBool _ => true | _ => false end.

Definition is_pl_list (v : pl_val) : bool :=
  match v with PLitList _ => true | _ => false end.
