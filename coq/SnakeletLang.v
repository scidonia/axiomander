From stdpp Require Export strings gmap.
From stdpp Require Import countable decidable.
From iris.program_logic Require Export language.
From Stdlib Require Import PrimFloat.
Open Scope Z_scope.

(** SnakeletLang — standalone Iris language for Axiomander verification.

    Values: ints, bools, locations, unit.
    State: gmap loc val (Iris-compatible heap).
    Pure steps: let, binop, if, dict lookup.
    Head steps: load, store, FAA, fork, alloc, dict set, raise, try.
*)

Module SnakeletLang.

(** * Locations *)
Inductive loc := Loc (l : positive).

#[global] Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Qed.

#[global] Instance loc_countable : Countable loc.
Proof.
  apply (inj_countable' (λ '(Loc l), l) Loc); abstract (by intros []).
Qed.

(** * Values *)
Inductive val :=
  | LitInt (n : Z)
  | LitFloat (f : float)      (* IEEE 754 — conservative Python float model *)
  | LitBool (b : bool)
  | LitLoc (l : loc)
  | LitString (s : string)
  | LitUnit.

Definition LitV (v : val) : val := v.

(** * Expressions *)
Inductive binop := AddOp | SubOp | MulOp | DivOp | EqOp | LeOp | LtOp.

Inductive expr :=
  | Val (v : val)
  | Var (x : string)
  | Let (x : string) (e1 e2 : expr)
  | BinOp (op : binop) (e1 e2 : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | Alloc (e : expr)
  | If (e0 e1 e2 : expr)
  | FAA (e1 e2 : expr)
  | Fork (e : expr)
  (* Strings *)
  | StringEq (e1 e2 : expr)
  | StringConcat (e1 e2 : expr)
  | StringLength (e : expr)
  (* Sets *)
  | SetAdd (l e : expr)
  | SetHas (l e : expr)
  (* Dicts *)
  | DictGet (l key : expr)
  | DictSet (l key val : expr)
  (* Exceptions *)
  | Raise (e : expr)
  | Try (body handler : expr).

(** * Values and evaluation *)
Definition of_val (v : val) : expr := Val v.
Definition to_val (e : expr) : option val :=
  match e with Val v => Some v | _ => None end.
Definition state : Type := gmap loc val.

(** * Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
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
  | StringEq e1 e2 => StringEq (subst x v e1) (subst x v e2)
  | StringConcat e1 e2 => StringConcat (subst x v e1) (subst x v e2)
  | StringLength e => StringLength (subst x v e)
  | SetAdd l e => SetAdd (subst x v l) (subst x v e)
  | SetHas l e => SetHas (subst x v l) (subst x v e)
  | Raise e => Raise (subst x v e)
  | Try body handler => Try (subst x v body) (subst x v handler)
  end.

(** * Pure steps *)

Definition binop_eval (op : binop) (v1 v2 : val) : val :=
  match v1, v2 with
  | LitInt n1, LitInt n2 =>
      match op with
      | AddOp => LitInt (n1 + n2)
      | SubOp => LitInt (n1 - n2)
      | MulOp => LitInt (n1 * n2)
      | DivOp => LitInt (Z.div n1 n2)
      | EqOp  => LitBool (bool_decide (n1 = n2))
      | LeOp  => LitBool (bool_decide (n1 <= n2))
      | LtOp  => LitBool (bool_decide (n1 < n2))
      end
  | _, _ => LitUnit
  end.

Inductive pure_step : expr → expr → Prop :=
  | PureLet v x e2 : pure_step (Let x (Val v) e2) (subst x v e2)
  | PureBinOp op v1 v2 :
      pure_step (BinOp op (Val v1) (Val v2)) (Val (binop_eval op v1 v2))
  | PureIfTrue e1 e2 : pure_step (If (Val (LitBool true)) e1 e2) e1
  | PureIfFalse e1 e2 : pure_step (If (Val (LitBool false)) e1 e2) e2
  | PureTryReturn v handler : pure_step (Try (Val v) handler) (Val v).
  (* String operations are pure — functional, no heap mutation *)
  | PureStringEq s1 s2 :
      pure_step (StringEq (Val s1) (Val s2))
                (Val (LitBool (bool_decide (s1 = s2))))
  | PureStringConcat s1 s2 :
      pure_step (StringConcat (Val s1) (Val s2))
                (Val (LitString (s1 ++ s2)))
  | PureStringLength s :
      pure_step (StringLength (Val s)) (Val (LitInt (Z.of_nat (String.length s)))).

Definition binop_eval (op : binop) (v1 v2 : val) : val :=
  match v1, v2 with
  | LitInt n1, LitInt n2 =>
      match op with
      | AddOp => LitInt (n1 + n2)
      | SubOp => LitInt (n1 - n2)
      | MulOp => LitInt (n1 * n2)
      | DivOp => LitInt (Z.div n1 n2)
      | EqOp  => LitBool (bool_decide (n1 = n2))
      | LeOp  => LitBool (bool_decide (n1 <= n2))
      | LtOp  => LitBool (bool_decide (n1 < n2))
      end
  | _, _ => LitUnit
  end.

(** * Head steps *)
Inductive head_step : expr → state → expr → state → list expr → Prop :=
  | HeadLoad l v σ :
      σ !! l = Some v →
      head_step (Load (Val (LitLoc l))) σ (Val v) σ []
  | HeadStore l v w σ :
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
  | HeadDictSet l k v σ :
      is_Some (σ !! l) →   (* TODO: proper gmap encoding *)
      head_step (DictSet (Val l) (Val k) (Val v)) σ
                (Val LitUnit) σ []
  | HeadRaise v σ :
      head_step (Raise (Val v)) σ (Val v) σ []
  | HeadTryBody body σ body' σ' efs :
      head_step body σ body' σ' efs →
      head_step (Try body handler) σ body' σ' efs.

Definition lit_as_z (v : val) : Z :=
  match v with LitInt n => n | _ => 0 end.

(** * Language mixin *)
Lemma snakelet_mixin : LanguageMixin of_val to_val pure_step
  (λ e σ e' σ' efs, head_step e σ e' σ' efs).
Proof.
  split.
  - intros ?; apply: to_of_val.
  - intros ? ? []; simplify_eq; auto.
  - intros ? ? ?; apply: val_base_stuck.
  - intros ? ? ?; apply: of_to_val.
  - intros ??; inversion 1; subst; auto.
  - intros ????. inversion 1; simplify_eq; eauto.
  - intros ????. inversion 1; simplify_eq; auto.
Qed.

Global Instance snakelet_lang : language := Language snakelet_mixin.

End SnakeletLang.
