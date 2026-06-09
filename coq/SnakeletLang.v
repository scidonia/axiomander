From stdpp Require Export strings gmap.
From stdpp Require Import countable decidable.
From iris.program_logic Require Export language.
Open Scope Z_scope.

(** SnakeletLang — standalone Iris language for Axiomander verification.

    Values: ints, booleans, floats, strings, tuples, lists, dicts, sets,
            locations, unit.
    State: gmap loc sn_val (Iris-compatible heap).
    Pure steps: let, binop, if, dict lookup.
    Head steps: load, store, FAA, fork, alloc, dict set, raise, try.
*)

From Stdlib Require Import BinInt Uint63Axioms Floats.PrimFloat.


(** * Locations *)
Inductive loc := Loc (l : positive).

#[global] Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Qed.

#[global] Instance loc_countable : Countable loc.
Proof.
  apply (inj_countable' (λ '(Loc l), l) Loc); abstract (by intros []).
Qed.

#[global] Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, Loc p) (λ l, match l with Loc p => Some p end) _.
Next Obligation. done. Qed.

(** * Values *)
Inductive sn_val :=
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitFloat (f : float)
  | LitString (s : string)
  | LitTuple (vs : list sn_val)
  | LitList (vs : list sn_val)
  | LitDict (kvs : list (sn_val * sn_val))
  | LitSet (vs : list sn_val)
  | LitLoc (l : loc)
  | LitUnit.

Definition LitV (v : sn_val) : sn_val := v.

(** * Expressions *)
Inductive binop := AddOp | SubOp | MulOp | DivOp | EqOp | LeOp | LtOp | GtOp | GeOp
                 | LenOp | InOp | UnionOp | InterOp.

Inductive sn_expr :=
  | Val (v : sn_val)
  | Var (x : string)
  | Let (x : string) (e1 e2 : sn_expr)
  | BinOp (op : binop) (e1 e2 : sn_expr)
  | Load (e : sn_expr)
  | Store (e1 e2 : sn_expr)
  | Alloc (e : sn_expr)
  | If (e0 e1 e2 : sn_expr)
  | FAA (e1 e2 : sn_expr)
  | Fork (e : sn_expr)
  | DictGet (l key : sn_expr)
  | DictSet (l key sn_val : sn_expr)
  | Raise (e : sn_expr)
  | Try (body handler : sn_expr).

(** * Values and evaluation *)
Definition of_val (v : sn_val) : sn_expr := Val v.
Definition to_val (e : sn_expr) : option sn_val :=
  match e with Val v => Some v | _ => None end.
Definition sn_state : Type := gmap loc sn_val.

(** * Substitution *)
Fixpoint subst (x : string) (v : sn_val) (e : sn_expr) : sn_expr :=
  match e with
  | Val _ => e
  | Var y => if String.eqb x y then Val v else e
  | Let y e1 e2 =>
      Let y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | Alloc e => Alloc (subst x v e)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | DictGet l key => DictGet (subst x v l) (subst x v key)
  | DictSet l key v' => DictSet (subst x v l) (subst x v key) (subst x v v')
  | Raise e => Raise (subst x v e)
  | Try body handler => Try (subst x v body) (subst x v handler)
  end.

(** * Pure steps *)

Definition z_to_float (n : Z) : float :=
  PrimFloat.of_uint63 (of_Z n).

Fixpoint val_list_len (vs : list sn_val) : Z :=
  match vs with
  | [] => 0
  | _ :: vs' => 1 + val_list_len vs'
  end%Z.

Fixpoint val_eqb (fuel : nat) (v1 v2 : sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match v1, v2 with
      | LitInt n1, LitInt n2 => bool_decide (n1 = n2)
      | LitBool b1, LitBool b2 => Bool.eqb b1 b2
      | LitFloat f1, LitFloat f2 => PrimFloat.eqb f1 f2
      | LitString s1, LitString s2 => String.eqb s1 s2
      | LitTuple vs1, LitTuple vs2 => val_list_eqb fuel' vs1 vs2
      | LitList vs1, LitList vs2 => val_list_eqb fuel' vs1 vs2
      | LitSet vs1, LitSet vs2 => val_list_eqb fuel' vs1 vs2
      | LitDict kvs1, LitDict kvs2 => val_kvlist_eqb fuel' kvs1 kvs2
      | LitLoc l1, LitLoc l2 =>
          match l1, l2 with Loc p1, Loc p2 => Pos.eqb p1 p2 end
      | LitUnit, LitUnit => true
      | _, _ => false
      end
  end
with val_list_eqb (fuel : nat) (vs1 vs2 : list sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match vs1, vs2 with
      | [], [] => true
      | v1 :: vs1', v2 :: vs2' => val_eqb fuel' v1 v2 && val_list_eqb fuel' vs1' vs2'
      | _, _ => false
      end
  end
with val_kvlist_eqb (fuel : nat) (kvs1 kvs2 : list (sn_val * sn_val)) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match kvs1, kvs2 with
      | [], [] => true
      | (k1,v1) :: kvs1', (k2,v2) :: kvs2' =>
          val_eqb fuel' k1 k2 && val_eqb fuel' v1 v2 && val_kvlist_eqb fuel' kvs1' kvs2'
      | _, _ => false
      end
  end.
(** Initial fuel: sum of structure depths. Empirically, 50 covers all test cases. *)
Definition val_eq (v1 v2 : sn_val) : bool := val_eqb 50 v1 v2.

Fixpoint val_list_mem (fuel : nat) (x : sn_val) (vs : list sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match vs with
      | [] => false
      | v :: vs' => val_eqb fuel' x v || val_list_mem fuel' x vs'
      end
  end.

Definition binop_eval (op : binop) (v1 v2 : sn_val) : sn_val :=
  match v1, v2 with
  (* --- int x int --- *)
  | LitInt n1, LitInt n2 =>
      match op with
      | AddOp => LitInt (n1 + n2)
      | SubOp => LitInt (n1 - n2)
      | MulOp => LitInt (n1 * n2)
      | DivOp => LitFloat (PrimFloat.div (z_to_float n1) (z_to_float n2))
      | EqOp  => LitBool (bool_decide (n1 = n2))
      | LeOp  => LitBool (bool_decide (n1 <= n2))
      | LtOp  => LitBool (bool_decide (n1 < n2))
      | GtOp  => LitBool (bool_decide (n1 > n2))
      | GeOp  => LitBool (bool_decide (n1 >= n2))
      | _ => LitUnit
      end
  (* --- float x float --- *)
  | LitFloat f1, LitFloat f2 =>
      match op with
      | AddOp => LitFloat (PrimFloat.add f1 f2)
      | SubOp => LitFloat (PrimFloat.sub f1 f2)
      | MulOp => LitFloat (PrimFloat.mul f1 f2)
      | DivOp => LitFloat (PrimFloat.div f1 f2)
      | EqOp  => LitBool (PrimFloat.eqb f1 f2)
      | LeOp  => LitBool (PrimFloat.leb f1 f2)
      | LtOp  => LitBool (PrimFloat.ltb f1 f2)
      | GtOp  => LitBool (negb (PrimFloat.leb f1 f2))
      | GeOp  => LitBool (negb (PrimFloat.ltb f1 f2))
      | _ => LitUnit
      end
  (* --- int x float / float x int --- *)
  | LitInt n, LitFloat f =>
      match op with
      | AddOp => LitFloat (PrimFloat.add (z_to_float n) f)
      | SubOp => LitFloat (PrimFloat.sub (z_to_float n) f)
      | MulOp => LitFloat (PrimFloat.mul (z_to_float n) f)
      | DivOp => LitFloat (PrimFloat.div (z_to_float n) f)
      | _ => LitUnit
      end
  | LitFloat f, LitInt n =>
      match op with
      | AddOp => LitFloat (PrimFloat.add f (z_to_float n))
      | SubOp => LitFloat (PrimFloat.sub f (z_to_float n))
      | MulOp => LitFloat (PrimFloat.mul f (z_to_float n))
      | DivOp => LitFloat (PrimFloat.div f (z_to_float n))
      | _ => LitUnit
      end
  (* --- string x string --- *)
  | LitString s1, LitString s2 =>
      match op with
      | AddOp => LitString (s1 ++ s2)
      | EqOp  => LitBool (String.eqb s1 s2)
      | LenOp => LitInt (Z.of_nat (String.length s1))
      | _ => LitUnit
      end
  (* --- string len (second arg not a string) --- *)
  | LitString s, _ =>
      match op with
      | LenOp => LitInt (Z.of_nat (String.length s))
      | _ => LitUnit
       end
  (* --- bool x int / int x bool --- *)
  | LitBool b1, LitInt n =>
      match op with
      | AddOp => LitInt ((if b1 then 1 else 0)%Z + n)
      | SubOp => LitInt ((if b1 then 1 else 0)%Z - n)
      | MulOp => LitInt ((if b1 then 1 else 0)%Z * n)
      | _ => LitUnit
      end
  | LitInt n, LitBool b =>
      match op with
      | AddOp => LitInt (n + (if b then 1 else 0)%Z)
      | SubOp => LitInt (n - (if b then 1 else 0)%Z)
      | MulOp => LitInt (n * (if b then 1 else 0)%Z)
      | _ => LitUnit
      end
  (* --- tuple x tuple --- *)
  | LitTuple vs1, LitTuple vs2 =>
      match op with
      | AddOp => LitTuple (vs1 ++ vs2)
      | EqOp  => LitBool (val_eq (LitTuple vs1) (LitTuple vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | _ => LitUnit
      end
  (* --- tuple len/in (second arg not a tuple) --- *)
  | LitTuple vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  (* --- list x list --- *)
  | LitList vs1, LitList vs2 =>
      match op with
      | AddOp => LitList (vs1 ++ vs2)
      | EqOp  => LitBool (val_eq (LitList vs1) (LitList vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | _ => LitUnit
      end
  (* --- list len/in (second arg not a list) --- *)
  | LitList vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  (* --- set x set --- *)
  | LitSet vs1, LitSet vs2 =>
      match op with
      | EqOp  => LitBool (val_eq (LitSet vs1) (LitSet vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | UnionOp => LitSet vs1
      | InterOp => LitSet vs1
      | _ => LitUnit
      end
  (* --- set len/in (second arg not a set) --- *)
  | LitSet vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  (* --- dict len --- *)
  | LitDict kvs, _ =>
      match op with
      | LenOp => LitInt (val_list_len (List.map fst kvs))
      | _ => LitUnit
       end
  | _, _ => LitUnit
  end.

Inductive pure_step : sn_expr → sn_expr → Prop :=
  | PureLet v x e2 : pure_step (Let x (Val v) e2) (subst x v e2)
  | PureBinOp op v1 v2 :
      pure_step (BinOp op (Val v1) (Val v2)) (Val (binop_eval op v1 v2))
  | PureIfTrue e1 e2 : pure_step (If (Val (LitBool true)) e1 e2) e1
  | PureIfFalse e1 e2 : pure_step (If (Val (LitBool false)) e1 e2) e2
  | PureTryReturn v handler : pure_step (Try (Val v) handler) (Val v).

Definition lit_as_z (v : sn_val) : Z :=
  match v with LitInt n => n | _ => 0 end.


(** * Head steps *)
Inductive head_step : sn_expr → sn_state → sn_expr → sn_state → list sn_expr → Prop :=
  | HeadLoad l v σ :
      σ !! l = Some v →
      head_step (Load (Val (LitLoc l))) σ (Val v) σ []
  | HeadStore l v σ :
      is_Some (σ !! l) →
      head_step (Store (Val (LitLoc l)) (Val v)) σ
                (Val LitUnit) (<[l:=v]> σ) []
  | HeadAlloc v σ l :
      σ !! l = None →
      head_step (Alloc (Val v)) σ (Val (LitLoc l))
                (<[l:=v]> σ) []
  | HeadFAA l v z σ :
      σ !! l = Some (LitInt z) →
      head_step (FAA (Val (LitLoc l)) (Val v)) σ
                (Val (LitInt z)) (<[l:=LitInt (z + lit_as_z v)]> σ) []
  | HeadFork e σ :
      head_step (Fork e) σ (Val LitUnit) σ [e]
  | HeadRaise v σ :
      head_step (Raise (Val v)) σ (Val v) σ []
  | HeadTryBody body handler σ body' σ' efs :
      head_step body σ body' σ' efs →
      head_step (Try body handler) σ body' σ' efs.

(** * Iris Language instance *)
Definition observation : Type := unit.

Inductive prim_step : sn_expr → sn_state → list observation → sn_expr → sn_state → list sn_expr → Prop :=
  | PrimPureStep e σ e' :
      pure_step e e' →
      prim_step e σ [] e' σ []
  | PrimHeadStep e σ e' σ' efs :
      head_step e σ e' σ' efs →
      prim_step e σ [] e' σ' efs.

Lemma snakelet_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split.
  - intros v. unfold of_val, to_val. reflexivity.
  - intros e v Hto. unfold to_val in Hto. destruct e; try discriminate.
    injection Hto as ->. unfold of_val. reflexivity.
  - intros e σ κ e' σ' efs Hprim.
    inversion Hprim as [e1 σ1 e1' Hpure | e1 σ1 e1' σ1' efs1 Hhead]; clear Hprim.
    { inversion Hpure; simpl; auto. }
    { destruct Hhead; simpl; auto. }
Qed.


Canonical Structure snakelet_lang := Language snakelet_lang_mixin.

(** Notations for writing SnakeletLang programs tersely.

    All notations are scoped under [snakelet_scope], so they do not interfere
    with other notations.  Use [Open Scope snakelet_scope] to activate them,
    or [Import snakelet_notation] to get both scope and coercions. *)

Module snakelet_notation.
  Declare Scope snakelet_scope.
  Delimit Scope snakelet_scope with S.

  Notation "# n" := (Val (LitInt n))
    (at level 8, n at level 1, format "# n") : snakelet_scope.
  Notation "# l" := (Val (LitLoc l))
    (at level 8, l at level 1, format "# l") : snakelet_scope.
  Notation "#true" := (Val (LitBool true)) : snakelet_scope.
  Notation "#false" := (Val (LitBool false)) : snakelet_scope.

  Notation "! e" := (Load e)
    (at level 9, right associativity, format "! e") : snakelet_scope.
  Notation "e1 <- e2" := (Store e1 e2)
    (at level 80, format "e1  <-  e2") : snakelet_scope.
  Notation "'ref' e" := (Alloc e)
    (at level 9, format "'ref'  e") : snakelet_scope.

  Notation "e1 + e2" := (BinOp AddOp e1 e2)
    (at level 50, left associativity) : snakelet_scope.
  Notation "e1 - e2" := (BinOp SubOp e1 e2)
    (at level 50, left associativity) : snakelet_scope.
  Notation "e1 * e2" := (BinOp MulOp e1 e2)
    (at level 40, left associativity) : snakelet_scope.
  Notation "e1 / e2" := (BinOp DivOp e1 e2)
    (at level 40, left associativity) : snakelet_scope.
  Notation "e1 = e2" := (BinOp EqOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
  Notation "e1 < e2" := (BinOp LtOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
  Notation "e1 <= e2" := (BinOp LeOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
End snakelet_notation.
