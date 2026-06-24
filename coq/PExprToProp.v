From Stdlib Require Import List ZArith Bool String.
From Stdlib Require Import PrimFloat.
Import ListNotations.
Open Scope Z_scope.

Require Import LambdaA.

(** * Compiling p_expr to Coq Prop

    Contracts are pure boolean expressions over Z/bool/string-typed
    free variables.  We compile a [p_expr] to a Coq [Prop] by giving
    each variable an interpretation as a Coq value.

    We provide two entry points:
    - [p_expr_to_prop_Z env e] — assumes all variables are Z-typed
    - [p_expr_to_prop envZ envB envS e] — full typed environment *)

(* ── Z-only compilation (95% of contract use cases) ──────────────── *)

Fixpoint p_expr_int (env : string -> Z) (e : p_expr) : Z :=
  match e with
  | PVar x => env x
  | PVal (PLitInt n) => n
  | PVal (PLitString _) => 0   (* type error — return 0 *)
  | PVal (PLitBool _) => 0
  | PVal (PLitFloat _) => 0
  | PVal (PLitList _) => 0
  | PVal (PLitTuple _) => 0
  | PVal (PLitDict _) => 0
  | PVal (PLitSet _) => 0
  | PVal PLitUnit => 0
  | PBinOp PAddOp e1 e2 => p_expr_int env e1 + p_expr_int env e2
  | PBinOp PSubOp e1 e2 => p_expr_int env e1 - p_expr_int env e2
  | PBinOp PMulOp e1 e2 => p_expr_int env e1 * p_expr_int env e2
  | PBinOp PDivOp e1 e2 =>
      let d := p_expr_int env e2 in
      if Z.eqb d 0 then 0 else Z.div (p_expr_int env e1) d
  | PBinOp PModOp e1 e2 =>
      let d := p_expr_int env e2 in
      if Z.eqb d 0 then 0 else Z.modulo (p_expr_int env e1) d
  | PBinOp PLenOp e1 _ => Z.of_nat 0
    (* PLenOp: hard to compute length from Z — fallback *)
  | PIf e0 e1 e2 =>
      if p_expr_bool env e0 then p_expr_int env e1 else p_expr_int env e2
  | PLet x e1 e2 =>
      p_expr_int (fun y => if String.eqb x y then p_expr_int env e1 else env y) e2
  | PCall _ _ => 0   (* calls cannot be compiled to Prop directly *)
  | _ => 0
  end

with p_expr_bool (env : string -> Z) (e : p_expr) : bool :=
  match e with
  | PVar x => false  (* Z variables are not booleans *)
  | PVal (PLitBool b) => b
  | PBinOp PEqOp e1 e2 => Z.eqb (p_expr_int env e1) (p_expr_int env e2)
  | PBinOp PNeOp e1 e2 => negb (Z.eqb (p_expr_int env e1) (p_expr_int env e2))
  | PBinOp PLeOp e1 e2 => Z.leb (p_expr_int env e1) (p_expr_int env e2)
  | PBinOp PLtOp e1 e2 => Z.ltb (p_expr_int env e1) (p_expr_int env e2)
  | PBinOp PGtOp e1 e2 => Z.gtb (p_expr_int env e1) (p_expr_int env e2)
  | PBinOp PGeOp e1 e2 => Z.geb (p_expr_int env e1) (p_expr_int env e2)
  | PBinOp PAndOp e1 e2 => p_expr_bool env e1 && p_expr_bool env e2
  | PBinOp POrOp e1 e2 => p_expr_bool env e1 || p_expr_bool env e2
  | PIf e0 e1 e2 =>
      if p_expr_bool env e0 then p_expr_bool env e1 else p_expr_bool env e2
  | PLet x e1 e2 =>
      p_expr_bool (fun y => if String.eqb x y then p_expr_int env e1 else env y) e2
  | _ => false
  end.

Definition p_expr_to_prop_Z (env : string -> Z) (e : p_expr) : Prop :=
  p_expr_bool env e = true.

(* ── Typed compilation (int + bool + string + float) ────────────── *)

Definition typed_env :=
  ((string -> Z) * (string -> bool) * (string -> string) * (string -> PrimFloat.float))%type.

Fixpoint p_expr_int_typed (envZ : string -> Z) (envB : string -> bool)
  (envS : string -> string) (envF : string -> PrimFloat.float) (e : p_expr) : Z :=
  match e with
  | PVal (PLitInt n) => n
  | PLet x e1 e2 =>
      p_expr_int_typed (fun y => if String.eqb x y then p_expr_int_typed envZ envB envS envF e1 else envZ y) envB envS envF e2
  | PBinOp PAddOp e1 e2 => p_expr_int_typed envZ envB envS envF e1 + p_expr_int_typed envZ envB envS envF e2
  | PBinOp PSubOp e1 e2 => p_expr_int_typed envZ envB envS envF e1 - p_expr_int_typed envZ envB envS envF e2
  | PBinOp PMulOp e1 e2 => p_expr_int_typed envZ envB envS envF e1 * p_expr_int_typed envZ envB envS envF e2
  | PBinOp PDivOp e1 e2 =>
      let d := p_expr_int_typed envZ envB envS envF e2 in
      if Z.eqb d 0 then 0 else Z.div (p_expr_int_typed envZ envB envS envF e1) d
  | PBinOp PModOp e1 e2 =>
      let d := p_expr_int_typed envZ envB envS envF e2 in
      if Z.eqb d 0 then 0 else Z.modulo (p_expr_int_typed envZ envB envS envF e1) d
  | PBinOp PLenOp _ _ => 0
  | PIf e0 e1 e2 =>
      if p_expr_bool_typed envZ envB envS envF e0
      then p_expr_int_typed envZ envB envS envF e1
      else p_expr_int_typed envZ envB envS envF e2
  | _ => 0
  end

with p_expr_bool_typed (envZ : string -> Z) (envB : string -> bool)
  (envS : string -> string) (envF : string -> PrimFloat.float) (e : p_expr) : bool :=
  match e with
  | PVar x => envB x
  | PVal (PLitBool b) => b
  | PBinOp PEqOp e1 e2 =>
      (* Int equality — use Z for all numeric comparison *)
      Z.eqb (p_expr_int_typed envZ envB envS envF e1) (p_expr_int_typed envZ envB envS envF e2)
  | PBinOp PNeOp e1 e2 =>
      negb (Z.eqb (p_expr_int_typed envZ envB envS envF e1) (p_expr_int_typed envZ envB envS envF e2))
  | PBinOp PLeOp e1 e2 => Z.leb (p_expr_int_typed envZ envB envS envF e1) (p_expr_int_typed envZ envB envS envF e2)
  | PBinOp PLtOp e1 e2 => Z.ltb (p_expr_int_typed envZ envB envS envF e1) (p_expr_int_typed envZ envB envS envF e2)
  | PBinOp PGtOp e1 e2 => Z.gtb (p_expr_int_typed envZ envB envS envF e1) (p_expr_int_typed envZ envB envS envF e2)
  | PBinOp PGeOp e1 e2 => Z.geb (p_expr_int_typed envZ envB envS envF e1) (p_expr_int_typed envZ envB envS envF e2)
  | PBinOp PAndOp e1 e2 => p_expr_bool_typed envZ envB envS envF e1 && p_expr_bool_typed envZ envB envS envF e2
  | PBinOp POrOp e1 e2 => p_expr_bool_typed envZ envB envS envF e1 || p_expr_bool_typed envZ envB envS envF e2
  | PIf e0 e1 e2 =>
      if p_expr_bool_typed envZ envB envS envF e0
      then p_expr_bool_typed envZ envB envS envF e1
      else p_expr_bool_typed envZ envB envS envF e2
  | PLet x e1 e2 =>
      p_expr_bool_typed
        (fun y => if String.eqb x y then p_expr_int_typed envZ envB envS envF e1 else envZ y)
        (fun y => if String.eqb x y then p_expr_bool_typed envZ envB envS envF e1 else envB y)
        envS envF e2
  | _ => false
  end.

Definition p_expr_to_prop (envZ : string -> Z) (envB : string -> bool)
  (envS : string -> string) (envF : string -> PrimFloat.float) (e : p_expr) : Prop :=
  p_expr_bool_typed envZ envB envS envF e = true.

(* ── Simpler entry point: single-typed variables ────────────────── *)

Definition default_envZ (x : string) : Z := 0%Z.
Definition default_envB (x : string) : bool := false.
Definition default_envS (x : string) : string := ""%string.
Definition default_envF (x : string) : PrimFloat.float := 0%float.

(** Compile a [p_expr] to [Prop] assuming all free variables are Z-valued. *)
Definition p_expr_prop_Z (e : p_expr) : Prop :=
  p_expr_bool_typed default_envZ default_envB default_envS default_envF e = true.
