From Stdlib Require Import List ZArith Bool String.
From Stdlib Require Import PrimFloat.
Import ListNotations.

Require Import LambdaA.
Require Import SnakeletExnLang.

(** * LambdaA ↔ SnakeletExnLang Embedding

    LambdaA's [p_expr] is the pure fragment of SnakeletExnLang's [sn_expr]:
    every constructor maps directly except for [Load], [Store], [Alloc],
    [Raise], [Try], [While], [For] which have no pure counterpart.

    We provide:
    - [pl_val_to_sn_val] : total injection
    - [sn_val_to_pl_val] : partial projection ([LitLoc]/[LitExn] → [None])
    - [of_p_expr] : total injection
    - [to_p_expr] : partial projection (impure nodes → [None])
    - Round-trip lemmas: injection then projection is identity. *)

(* ── Utilities ──────────────────────────────────────────────────── *)

Definition map_option {A B : Type} (f : A -> option B) (xs : list A) : option (list B) :=
  fold_right (fun x acc =>
    match f x, acc with
    | Some y, Some ys => Some (y :: ys)
    | _, _ => None
    end) (Some []) xs.

Definition map2_option {A B C : Type} (f : A -> B -> option C) (xs : list A) (ys : list B) : option (list C) :=
  fold_right2 (fun x y acc =>
    match acc with
    | None => None
    | Some zs => match f x y with Some z => Some (z :: zs) | None => None end
    end) (Some []) xs ys.

(* ── Values ─────────────────────────────────────────────────────── *)

Fixpoint pl_val_to_sn_val (v : pl_val) : sn_val :=
  match v with
  | PLitInt n => LitInt n
  | PLitBool b => LitBool b
  | PLitString s => LitString s
  | PLitFloat f => LitFloat f
  | PLitList vs => LitList (List.map pl_val_to_sn_val vs)
  | PLitTuple vs => LitTuple (List.map pl_val_to_sn_val vs)
  | PLitDict kvs => LitDict (List.map (fun '(k,v) => (pl_val_to_sn_val k, pl_val_to_sn_val v)) kvs)
  | PLitSet vs => LitSet (List.map pl_val_to_sn_val vs)
  | PLitUnit => LitUnit
  end.

Fixpoint sn_val_to_pl_val (v : sn_val) : option pl_val :=
  match v with
  | LitInt n => Some (PLitInt n)
  | LitBool b => Some (PLitBool b)
  | LitString s => Some (PLitString s)
  | LitFloat f => Some (PLitFloat f)
  | LitList vs => option_map PLitList (map_option sn_val_to_pl_val vs)
  | LitTuple vs => option_map PLitTuple (map_option sn_val_to_pl_val vs)
  | LitDict kvs =>
      option_map PLitDict (map_option
        (fun '(k,v) =>
          match sn_val_to_pl_val k, sn_val_to_pl_val v with
          | Some k', Some v' => Some (k', v')
          | _, _ => None
          end) kvs)
  | LitSet vs => option_map PLitSet (map_option sn_val_to_pl_val vs)
  | LitUnit => Some PLitUnit
  | LitLoc _ | LitExn _ _ => None
  end.

Lemma pl_val_roundtrip : forall v, sn_val_to_pl_val (pl_val_to_sn_val v) = Some v.
Proof.
  induction v; simpl; auto.
  - rewrite map_option_map_Some. rewrite IHv. reflexivity.
    (* Need lemma: map_option f (map g xs) = map_option (fun x => f (g x)) xs
       when f (g x) succeeds for all x *)
Admitted.

(* ── Operators ──────────────────────────────────────────────────── *)

Definition pl_binop_to_binop (op : pl_binop) : binop :=
  match op with
  | PAddOp => AddOp | PSubOp => SubOp | PMulOp => MulOp | PDivOp => DivOp
  | PModOp => ModOp
  | PEqOp => EqOp | PLeOp => LeOp | PLtOp => LtOp | PGtOp => GtOp | PGeOp => GeOp
  | PNeOp => NeOp | PAndOp => AndOp | POrOp => OrOp
  | PInOp => InOp | PLenOp => LenOp | PAppendOp => AppendOp
  | PStartsWithOp => StartsWithOp | PEndsWithOp => EndsWithOp
  | PToLowerOp => ToLowerOp | PToUpperOp => ToUpperOp
  end.

Definition binop_to_pl_binop (op : binop) : option pl_binop :=
  match op with
  | AddOp => Some PAddOp | SubOp => Some PSubOp | MulOp => Some PMulOp
  | DivOp => Some PDivOp | ModOp => Some PModOp
  | EqOp => Some PEqOp | LeOp => Some PLeOp | LtOp => Some PLtOp
  | GtOp => Some PGtOp | GeOp => Some PGeOp | NeOp => Some PNeOp
  | AndOp => Some PAndOp | OrOp => Some POrOp
  | InOp => Some PInOp | LenOp => Some PLenOp | AppendOp => Some PAppendOp
  | StartsWithOp => Some PStartsWithOp | EndsWithOp => Some PEndsWithOp
  | ToLowerOp => Some PToLowerOp | ToUpperOp => Some PToUpperOp
  | UnionOp | InterOp | LengthOp | DictGetOp | DictGetIntOp
  | MkKeyErrOp | SetAddOp | StrIndexOp | DictSetOp | TupleOp => None
  end.

Lemma pl_binop_roundtrip : forall op, binop_to_pl_binop (pl_binop_to_binop op) = Some op.
Proof. destruct op; reflexivity. Qed.

(* ── Expressions ────────────────────────────────────────────────── *)

Fixpoint of_p_expr (e : p_expr) : sn_expr :=
  match e with
  | PVar x => Var x
  | PVal v => Val (pl_val_to_sn_val v)
  | PBinOp op e1 e2 => BinOp (pl_binop_to_binop op) (of_p_expr e1) (of_p_expr e2)
  | PCall f args => Call f (List.map of_p_expr args)
  | PIf e0 e1 e2 => If (of_p_expr e0) (of_p_expr e1) (of_p_expr e2)
  | PLet x e1 e2 => Let x (of_p_expr e1) (of_p_expr e2)
  end.

Fixpoint to_p_expr (e : sn_expr) : option p_expr :=
  match e with
  | Var x => Some (PVar x)
  | Val v => option_map PVal (sn_val_to_pl_val v)
  | BinOp op e1 e2 =>
      match binop_to_pl_binop op, to_p_expr e1, to_p_expr e2 with
      | Some op', Some e1', Some e2' => Some (PBinOp op' e1' e2')
      | _, _, _ => None
      end
  | Let x e1 e2 =>
      match to_p_expr e1, to_p_expr e2 with
      | Some e1', Some e2' => Some (PLet x e1' e2')
      | _, _ => None
      end
  | Call f args =>
      match map_option to_p_expr args with
      | Some args' => Some (PCall f args')
      | None => None
      end
  | If e0 e1 e2 =>
      match to_p_expr e0, to_p_expr e1, to_p_expr e2 with
      | Some e0', Some e1', Some e2' => Some (PIf e0' e1' e2')
      | _, _, _ => None
      end
  | Load _ | Store _ _ | Alloc _ | Raise _ | Try _ _ _ | While _ _ | For _ _ _ => None
  end.

(** [of_p_expr] followed by [to_p_expr] is the identity. *)
Lemma of_p_expr_roundtrip : forall e, to_p_expr (of_p_expr e) = Some e.
Proof.
  induction e; simpl.
  - (* PVar *) reflexivity.
  - (* PVal *) rewrite pl_val_roundtrip. reflexivity.
  - (* PBinOp *) rewrite pl_binop_roundtrip. rewrite IHe1, IHe2. reflexivity.
  - (* PCall *)
    induction args; simpl.
    + reflexivity.
    + rewrite IHe. destruct IHargs as [->]. simpl. reflexivity.
    (* Need to be more careful with map_option and IHe/IHe *)
Admitted.

(* ── Function table embedding ───────────────────────────────────── *)

Definition of_fn_entry (entry : string * (list string * p_expr)) : string * (list string * sn_expr) :=
  let '(fname, (params, body)) := entry in
  (fname, (params, of_p_expr body)).

Definition of_fn_table (F : LambdaA.fn_table) : list (string * (list string * sn_expr)) :=
  List.map of_fn_entry F.
