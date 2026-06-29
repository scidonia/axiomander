From Stdlib Require Import List ZArith Bool String.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Require Import LambdaA.

(** * Supercompiler for lambda_A with symbolic context. *)

Definition ctx := list (string * p_expr).

(** Look up a variable in the context. *)
Definition ctx_lookup (c : ctx) (x : string) : option p_expr :=
  assoc String.eqb c x.

(** Extend context with a binding (shadows previous). *)
Definition ctx_extend (x : string) (v : p_expr) (c : ctx) : ctx :=
  (x, v) :: c.

(** Context expansion: replace PVar y with its context image,
    or a PCall expression with its reduced form. *)
Definition ctx_expand_one (c : ctx) (e : p_expr) : p_expr :=
  match e with
  | PVar y =>
      match ctx_lookup c y with
      | Some (PListHead (PVar z)) => PListHead (PVar z)
      | Some (PListTail (PVar z)) => PListTail (PVar z)
      | _ => e
      end
  | PCall f args =>
      let key := String.concat "_" (f :: map (fun a => match a with PVar v => v | _ => "_"%string end) args) in
      match ctx_lookup c key with
      | Some v => v
      | None => e
      end
  | _ => e
  end.

(** Store a reduced form for a PCall in the context, keyed by the call pattern. *)
Definition ctx_memo_call (f : string) (args : list p_expr) (res : p_expr) (c : ctx) : ctx :=
  let key := String.concat "_" (f :: map (fun a => match a with PVar v => v | _ => "_"%string end) args) in
  ctx_extend key res c.

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
      if String.eqb f1 f2 then forallb2 he_dec args1 args2
      else existsb (he_dec h) args2
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

(** * 4. Least General Generalization (anti-unification) *)

Fixpoint lgg_args (args1 args2 : list p_expr) (n : nat)
    : list p_expr * list (string * p_expr) * list (string * p_expr) :=
  match args1, args2 with
  | a1 :: rest1, a2 :: rest2 =>
      if pexpr_eqb a1 a2 then
        let '(gens, s1, s2) := lgg_args rest1 rest2 n in
        (a1 :: gens, s1, s2)
      else
        (** Fresh name: zgN where N = n mod 10 *)
        let digit :=
          match Nat.modulo n 10 with
          | 0%nat => "0" | 1%nat => "1" | 2%nat => "2" | 3%nat => "3" | 4%nat => "4"
          | 5%nat => "5" | 6%nat => "6" | 7%nat => "7" | 8%nat => "8" | 9%nat => "9"
          | _ => "0"
          end in
        let fresh := "zg" ++ digit in
        let '(gens, s1, s2) := lgg_args rest1 rest2 (S n) in
        (PVar fresh :: gens,
         (fresh, a1) :: s1,
         (fresh, a2) :: s2)
  | [], [] => ([], [], [])
  | _, _ => (args1, [], [])
  end.

(** * 5. Fold definitions (D1) *)

Record fold_def := MkFoldDef {
  fd_name   : string;
  fd_params : list string;
  fd_body   : p_expr;
}.

Definition fold_fn_table (defs : list fold_def) : fn_table :=
  map (fun d => (fd_name d, (fd_params d, fd_body d))) defs.

(** * 5b. LGG of two full expressions (Glück-style process-tree MSG) *)

Fixpoint lgg_expr (e1 e2 : p_expr) (n : nat)
    : p_expr * list (string * p_expr) * list (string * p_expr) :=
  let fresh_name m := "lgg" ++
    match m with | 0%nat => "0" | 1%nat => "1" | 2%nat => "2" | _ => "3" end in
  let lgg_fresh := (PVar (fresh_name n), [(fresh_name n, e1)], [(fresh_name n, e2)]) in
  match e1, e2 with
  | PVal v1, PVal v2 =>
      if pl_val_eqb v1 v2 then (PVal v1, [], []) else lgg_fresh
  | PVar x1, PVar x2 =>
      if String.eqb x1 x2 then (PVar x1, [], []) else lgg_fresh
  | PBinOp op1 a1 b1, PBinOp op2 a2 b2 =>
      if pl_binop_eqb op1 op2 then
        let '(ga, s1a, s2a) := lgg_expr a1 a2 (S n) in
        let '(gb, s1b, s2b) := lgg_expr b1 b2 (S (S n)) in
        (PBinOp op1 ga gb, (s1a ++ s1b)%list, (s2a ++ s2b)%list)
      else lgg_fresh
  | PCall f1 args1, PCall f2 args2 =>
      if String.eqb f1 f2 && Nat.eqb (List.length args1) (List.length args2) then
        let '(gars, s1, s2) := lgg_args args1 args2 n in
        (PCall f1 gars, s1, s2)
      else lgg_fresh
  | PIf c1 t1 e1, PIf c2 t2 e2 =>
      let '(gc, s1c, s2c) := lgg_expr c1 c2 n in
      let '(gt, s1t, s2t) := lgg_expr t1 t2 (S n) in
      let '(ge, s1e, s2e) := lgg_expr e1 e2 (S (S n)) in
      (PIf gc gt ge, (s1c ++ s1t ++ s1e)%list, (s2c ++ s2t ++ s2e)%list)
  | PLet x1 b1 e1, PLet x2 b2 e2 =>
      if String.eqb x1 x2 then
        let '(gb, s1b, s2b) := lgg_expr b1 b2 n in
        let '(ge, s1e, s2e) := lgg_expr e1 e2 (S n) in
        (PLet x1 gb ge, (s1b ++ s1e)%list, (s2b ++ s2e)%list)
      else lgg_fresh
  | PListHead e1, PListHead e2 =>
      let '(ge, s1, s2) := lgg_expr e1 e2 n in (PListHead ge, s1, s2)
  | PListTail e1, PListTail e2 =>
      let '(ge, s1, s2) := lgg_expr e1 e2 n in (PListTail ge, s1, s2)
  | PListIsNil e1, PListIsNil e2 =>
      let '(ge, s1, s2) := lgg_expr e1 e2 n in (PListIsNil ge, s1, s2)
  | PListCons a1 b1, PListCons a2 b2 =>
      let '(ga, s1a, s2a) := lgg_expr a1 a2 n in
      let '(gb, s1b, s2b) := lgg_expr b1 b2 (S n) in
      (PListCons ga gb, (s1a ++ s1b)%list, (s2a ++ s2b)%list)
  | _, _ => lgg_fresh
  end.

(** * 6. Generalization *)

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

(** Recursively expand PVars in [e] through context, bounded. *)
Fixpoint ctx_expand_n (c : ctx) (e : p_expr) (bound : nat) : p_expr :=
  match bound with
  | 0%nat => e
  | S n =>
      match e with
      | PVar y =>
          match ctx_lookup c y with
          | Some v => ctx_expand_n c v n
          | None => e
          end
      | PVal _ => e
      | PBinOp op e1 e2 => PBinOp op (ctx_expand_n c e1 n) (ctx_expand_n c e2 n)
      | PCall f args => PCall f (map (fun a => ctx_expand_n c a n) args)
      | PIf e0 e1 e2 => PIf (ctx_expand_n c e0 n) (ctx_expand_n c e1 n) (ctx_expand_n c e2 n)
      | PLet x e1 e2 => PLet x (ctx_expand_n c e1 n) (ctx_expand_n c e2 n)
      | PListHead e => PListHead (ctx_expand_n c e n)
      | PListTail e => PListTail (ctx_expand_n c e n)
      | PListIsNil e => PListIsNil (ctx_expand_n c e n)
      | PListCons e1 e2 => PListCons (ctx_expand_n c e1 n) (ctx_expand_n c e2 n)
      end
  end.

(** Replace all calls to function [fn] with calls to [new_name] in [e]. *)
Fixpoint replace_calls (fn new_name : string) (e : p_expr) : p_expr :=
  match e with
  | PVal _ | PVar _ => e
  | PBinOp op e1 e2 => PBinOp op (replace_calls fn new_name e1) (replace_calls fn new_name e2)
  | PCall g args =>
      let args' := map (replace_calls fn new_name) args in
      if String.eqb g fn then PCall new_name args'
      else PCall g args'
  | PIf e0 e1 e2 => PIf (replace_calls fn new_name e0) (replace_calls fn new_name e1) (replace_calls fn new_name e2)
  | PLet x e1 e2 => PLet x (replace_calls fn new_name e1) (replace_calls fn new_name e2)
  | PListHead e => PListHead (replace_calls fn new_name e)
  | PListTail e => PListTail (replace_calls fn new_name e)
  | PListIsNil e => PListIsNil (replace_calls fn new_name e)
  | PListCons e1 e2 => PListCons (replace_calls fn new_name e1) (replace_calls fn new_name e2)
  end.

(** Check if [t] represents a structural recurrence — only fire
    when some history entry is a PCall to the SAME function with
    structurally smaller args (D1 condition).
    Creates a fold with the driven-and-replaced ancestor body,
    and returns [fold_f(args)] as the residual. *)
Definition try_fold (F : fn_table) (history : list p_expr) (cx : ctx)
    (t : p_expr) (f : string) (args : list p_expr)
    : option fold_def * p_expr :=
  let args_full := map (fun a => ctx_expand_n cx a 5) args in
  let ancestor_args :=
    fold_left (fun acc h =>
      match h with
      | PCall fh argsh =>
          if (String.eqb f fh && forallb2 he_dec argsh args_full)%bool
          then Some argsh else acc
      | _ => acc
      end) history None in
  match ancestor_args with
  | Some argsh =>
      let '(gen_args, _, _) := lgg_args argsh args 0%nat in
      let fold_name := String.append "fold_" f in
      (** Drive the ancestor call one step to get the fold body. *)
      let ancestor_body :=
        match drive_step F cx (PCall f gen_args) with
        | Some body => body
        | None => PCall f gen_args  (* fallback: raw call *)
        end in
      let fold_body := replace_calls f fold_name ancestor_body in
      let params := map (fun a => match a with PVar v => v | _ => "p"%string end) gen_args in
      let residual := PCall fold_name args in
      (Some (MkFoldDef fold_name params fold_body), residual)
  | None => (None, t)
  end.

Fixpoint supercompile (F : fn_table) (fuel : nat)
    (history : list p_expr) (cx : ctx) (t : p_expr) : ctx * list fold_def * p_expr :=
  match fuel with
  | 0%nat => (cx, [], t)
  | S fuel' =>
    match drive_step F cx t with
    | Some t' =>
        let '(cx', defs, r) := supercompile F fuel' (t :: history) cx t' in
        (** Memoize: store the reduced form if [t] is a PCall. *)
        let cx'' := match t with
          | PCall f args => ctx_memo_call f args r cx'
          | _ => cx'
          end in
        (cx'', defs, r)
    | None =>
        match t with
        | PVal _ | PVar _ => (cx, [], t)
        | PBinOp op e1 e2 =>
            let '(cx1, ds1, e1') := supercompile F fuel' history cx e1 in
            let '(cx2, ds2, e2') := supercompile F fuel' history cx1 e2 in
            let defs := (ds1 ++ ds2)%list in
            let t' := PBinOp op e1' e2' in
            match drive_step F cx2 t' with
            | Some driven =>
                let '(cx3, ds3, r) := supercompile F fuel' history cx2 driven in
                (cx3, (defs ++ ds3)%list, r)
            | None => (cx2, defs, t')
            end
        | PIf e0 e1 e2 =>
            let '(cx0, ds0, e0') := supercompile F fuel' history cx e0 in
            match e0' with
             | PListIsNil (PVar x) =>
                if match String.index 0 "." x with Some _ => false | None => true end then
                  let hname := String.append x ".h" in
                  let tname := String.append x ".t" in
                  let cx_then := ctx_extend x (PVal (PLitList [])) cx0 in
                  let cx_else :=
                    ctx_extend tname (PListTail (PVar x))
                      (ctx_extend hname (PListHead (PVar x))
                        (ctx_extend x (PListCons (PVar hname) (PVar tname)) cx0)) in
                  let '(cx_t, ds_then, then') := supercompile F fuel' history cx_then e1 in
                  let '(cx_e, ds_else, else') := supercompile F fuel' history cx_else e2 in
                  (cx_e, (ds0 ++ ds_then ++ ds_else)%list, PIf e0' then' else')
                else
                  let '(cx1, ds1, e1') := supercompile F fuel' history cx0 e1 in
                  let '(cx2, ds2, e2') := supercompile F fuel' history cx1 e2 in
                  (cx2, (ds0 ++ ds1 ++ ds2)%list, PIf e0' e1' e2')
            | _ =>
                let t' := PIf e0' e1 e2 in
                match drive_step F cx0 t' with
                | Some driven =>
                    let '(cx_dr, ds_dr, r) := supercompile F fuel' history cx0 driven in
                    (cx_dr, (ds0 ++ ds_dr)%list, r)
                | None =>
                    let '(cx1, ds1, e1') := supercompile F fuel' history cx0 e1 in
                    let '(cx2, ds2, e2') := supercompile F fuel' history cx1 e2 in
                  (cx2, (ds0 ++ ds1 ++ ds2)%list, PIf e0' e1' e2')
                end
            end
        | PLet x e1 e2 =>
            let '(cx1, ds1, e1') := supercompile F fuel' history cx e1 in
            let '(cx2, ds2, e2') := supercompile F fuel' history cx1 e2 in
            (cx2, (ds1 ++ ds2)%list, PLet x e1' e2')
        | PListHead e =>
            let '(cx1, ds, e') := supercompile F fuel' history cx e in
            let t' := PListHead e' in
            match drive_step F cx1 t' with
            | Some driven =>
                let '(cx2, ds2, r) := supercompile F fuel' history cx1 driven in
                (cx2, (ds ++ ds2)%list, r)
            | None => (cx1, ds, t')
            end
        | PListTail e =>
            let '(cx1, ds, e') := supercompile F fuel' history cx e in
            let t' := PListTail e' in
            match drive_step F cx1 t' with
            | Some driven =>
                let '(cx2, ds2, r) := supercompile F fuel' history cx1 driven in
                (cx2, (ds ++ ds2)%list, r)
            | None => (cx1, ds, t')
            end
        | PListIsNil e =>
            let '(cx1, ds, e') := supercompile F fuel' history cx e in
            let t' := PListIsNil e' in
            match drive_step F cx1 t' with
            | Some driven =>
                let '(cx2, ds2, r) := supercompile F fuel' history cx1 driven in
                (cx2, (ds ++ ds2)%list, r)
            | None => (cx1, ds, t')
            end
        | PListCons e1 e2 =>
            let '(cx1, ds1, e1') := supercompile F fuel' history cx e1 in
            let '(cx2, ds2, e2') := supercompile F fuel' history cx1 e2 in
            let defs := (ds1 ++ ds2)%list in
            let t' := PListCons e1' e2' in
            match drive_step F cx2 t' with
            | Some driven =>
                let '(cx3, ds3, r) := supercompile F fuel' history cx2 driven in
                (cx3, (defs ++ ds3)%list, r)
            | None => (cx2, defs, t')
            end
        | PCall f args =>
            let process_one acc a :=
              let '(cx, acc_defs, acc_args) := acc in
              let '(cx', ds_a, a') := supercompile F fuel' history cx a in
              (cx', (acc_defs ++ ds_a)%list, a' :: acc_args) in
            let '(cx_args, ds_args, args'_rev) :=
              fold_left process_one args (cx, [], []) in
            let args' := rev args'_rev in
            let t' := PCall f args' in
            let '(fold_opt, t_folded) := try_fold F history cx_args t' f args' in
            match fold_opt with
            | Some d => (cx_args, (ds_args ++ [d])%list, t_folded)
            | None =>
                match drive_step F cx_args t_folded with
                | Some driven =>
                    let '(cx_dr, ds_dr, r) := supercompile F fuel' history cx_args driven in
                    let cx_memo := ctx_memo_call f args' r cx_dr in
                    (cx_memo, (ds_args ++ ds_dr)%list, r)
                | None => (cx_args, ds_args, t_folded)
                end
            end
        end
    end
  end.

(** Entry point: force-inline the top-level call to start the
    process tree, then run the standard supercompiler. *)
Definition scc (F : fn_table) (fuel : nat) (t : p_expr) : p_expr :=
  match t with
  | PCall f args =>
      match assoc String.eqb F f with
      | Some (params, body) =>
          let inlined := subst_many_expr (combine params args) body in
          let '(_, _, t') := supercompile F fuel [t] nil inlined in
          t'
      | None =>
          let '(_, _, t') := supercompile F fuel nil nil t in
          t'
      end
  | _ =>
      let '(_, _, t') := supercompile F fuel nil nil t in
      t'
  end.

Definition scc_full (F : fn_table) (fuel : nat) (t : p_expr) : list fold_def * p_expr :=
  match t with
  | PCall f args =>
      match assoc String.eqb F f with
      | Some (params, body) =>
          let inlined := subst_many_expr (combine params args) body in
          let '(_, defs, t') := supercompile F fuel [t] nil inlined in
          (defs, t')
      | None =>
          let '(_, defs, t') := supercompile F fuel nil nil t in
          (defs, t')
      end
  | _ =>
      let '(_, defs, t') := supercompile F fuel nil nil t in
      (defs, t')
  end.

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
  p_eval F fuel t = p_eval F fuel (snd (supercompile F fuel history cx t)).
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
