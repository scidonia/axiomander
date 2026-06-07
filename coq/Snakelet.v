From Stdlib Require Import String ZArith List.
From iris.program_logic Require Import language ectx_language.
From iris.prelude Require Import prelude.

(** Snakelet — a minimal verification IR targeting Iris.

    ~12 expression constructors, each with a direct Iris WP lemma.
    Exceptions (Raise/Try) are first-class.  Early returns use exceptions
    internally (Raise("__return__")).  Fork provides concurrency.

    Values are tagged: LitInt, LitBool, LitLoc, LitUnit, LitString.
*)

Module snakelet.

Inductive lit : Set :=
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitLoc (l : loc)
  | LitUnit
  | LitString (s : string).

Inductive bin_op : Set :=
  | AddOp | SubOp | MulOp | DivOp | ModOp
  | EqOp | LeOp | LtOp | GeOp | GtOp.

Inductive expr : Type :=
  | Val (v : lit)
  | Var (x : string)
  | Let (x : string) (e1 e2 : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | Return (e : expr)
  | Raise (e : expr)
  | Try (body : expr) (exc : string) (handler : expr)
  | Fork (e : expr)
  | CmpXchg (e0 e1 e2 : expr)
  | FAA (e1 e2 : expr)
  | App (f e : expr)
  | Rec (f x : binder) (e : expr).

(** Values *)
Definition val := lit.
Definition of_val (v : val) : expr := Val v.
Definition to_val (e : expr) : option val :=
  match e with Val v => Some v | _ => None end.

(** State: finite map from locations to values.
    Locals are named bindings (handled by substitution).
    Heap is a gmap from loc to val (Iris-compatible). *)
Definition state : Type := gmap loc val.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if String.eqb x y then Val v else e
  | Let y e1 e2 =>
      Let y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Return e => Return (subst x v e)
  | Raise e => Raise (subst x v e)
  | Try body exc handler =>
      Try (subst x v body) exc
          (if String.eqb x exc then handler else subst x v handler)
  | Fork e => Fork (subst x v e)
  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)
  | App f e => App (subst x v f) (subst x v e)
  | Rec f y e =>
      if String.eqb x y || binder_as_var x v then e    (* don't subst bound *)
      else Rec f y (subst x v e)
  end.

(** Outcomes: Return, Exception, or Fork (deferred). *)
Inductive outcome : Type :=
  | OReturn (v : val) (σ : state)
  | ORaise (v : val) (σ : state)
  | OFork (e : expr) (σ : state).

(** Step relation: single small-step on pure sub-expressions.
    Config = (expr, state). *)
Inductive pure_step : expr → expr → Prop :=
  | PureLet v x e2 : pure_step (Let x (Val v) e2) (subst x v e2)
  | PureBinOp op v1 v2 :
      pure_step (BinOp op (Val v1) (Val v2)) (Val (bin_op_eval op v1 v2))
  | PureIfTrue e1 e2 : pure_step (If (Val (LitBool true)) e1 e2) e1
  | PureIfFalse e1 e2 : pure_step (If (Val (LitBool false)) e1 e2) e2
  | PureRec f x e : pure_step (Rec f x e) (Val (LitUnit))  (* closure not modeled yet *)
  | PureBeta f x e v : pure_step (App (Rec f x e) (Val v)) (subst x v e).

(** Head step: stateful operations that read/write the heap. *)
Inductive head_step : expr → state → outcome → Prop :=
  | HeadLoad l v σ :
      σ !! l = Some v →
      head_step (Load (Val (LitLoc l))) σ (OReturn v σ)
  | HeadStore l v w σ :
      σ !! l ≠ None →
      head_step (Store (Val (LitLoc l)) (Val v)) σ
                (OReturn LitUnit (<[l:=v]> σ))
  | HeadCmpXchg l v1 v2 σ v :
      σ !! l = Some v →
      head_step (CmpXchg (Val (LitLoc l)) (Val v1) (Val v2)) σ
                (OReturn (LitBool (bool_decide (v = v1))) (if bool_decide (v = v1) then <[l:=v2]> σ else σ))
  | HeadFAA l v z σ :
      σ !! l = Some (LitInt z) →
      head_step (FAA (Val (LitLoc l)) (Val v)) σ
                (OReturn (LitInt z) (<[l:=LitInt (z + lit_as_z v)]> σ))
  | HeadFork e σ :
      head_step (Fork e) σ (OFork e σ)
  | HeadReturn v σ :
      head_step (Return (Val v)) σ (ORaise (LitString "__return__") σ)
  | HeadRaise v σ :
      head_step (Raise (Val v)) σ (ORaise v σ)
  | HeadTryReturn body exc handler v σ :
      head_step (Try (Return (Val v)) exc handler) σ (OReturn v σ)
  | HeadTryRaise body exc handler e σ σ' :
      head_step body σ (ORaise e σ') →
      e ≠ LitString "__return__" →
      head_step (Try body exc handler) σ
                (OReturn (LitUnit) σ')  (* body raised → handler runs *)
  | HeadTryPurePure body body' exc handler :
      pure_step body body' →
      head_step (Try body exc handler) σ (OReturn (LitUnit) σ).  (* TODO: correct semantics *)

(** The bin_op_eval function — pure arithmetic *)
Definition bin_op_eval (op : bin_op) (v1 v2 : lit) : lit :=
  LitInt 0.  (* TODO *)

Definition lit_as_z (v : lit) : Z :=
  match v with LitInt n => n | _ => 0 end.

Definition binder_as_var (x : binder) (v : val) : bool :=
  false.  (* TODO *)

End snakelet.
