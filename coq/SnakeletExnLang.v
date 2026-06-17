From stdpp Require Export strings gmap.
From stdpp Require Import countable decidable.
Open Scope Z_scope.

(** SnakeletExnLang -- parallel development of SnakeletLang with first-class
    exceptions, following van Collem / de Vilhena / Krebbers, "Backwards-
    Compatible Row-Based Exceptions in ML" (PLDI 2026).

    Design:
    - [Raise (Val v)] is a STUCK terminal expression (uncaught exception),
      not a value.  [to_val (Raise (Val v)) = None].
    - [Result := RVal v | RExn label payload] captures the two ways a
      program terminates.  The (hand-rolled) WP postcondition ranges over
      [Result], split into the two-postcondition form (Phi_E | Phi_V).
    - Exceptions are label + payload: [LitExn label payload], matching the
      paper's [l v].  [raises(ValueError, cond)] dispatches on [label].
    - [Try] is an evaluation context (so the body reduces inside it), but
      has NO head step.  Pure rules:
        try (Val v) h          -> v                 (normal: handler skipped)
        try (Raise (Val ev)) h -> App-of-handler    (exception: handler runs)
    - Raise unwinding: for any NON-try context item Ki,
        fill_item Ki (Raise (Val v)) -> Raise (Val v)
      i.e. [K[raise v] -> raise v] when K is neutral (paper's rule).

    This file is standalone; it does not touch SnakeletLang.v.  Once the
    8-lemma gate in SnakeletExnDemo.v is Qed, we wire the Python pipeline. *)

From Stdlib Require Import BinInt.

(** * Locations *)
Inductive loc := Loc (l : positive).

#[global] Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Qed.

#[global] Instance loc_countable : Countable loc.
Proof.
  apply (inj_countable' (fun '(Loc l) => l) Loc); abstract (by intros []).
Qed.

#[global] Program Instance loc_infinite : Infinite loc :=
  inj_infinite (fun p => Loc p) (fun l => match l with Loc p => Some p end) _.
Next Obligation. done. Qed.

(** * Values *)
Inductive sn_val :=
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitString (s : string)
  | LitLoc (l : loc)
  | LitUnit
  | LitExn (label : string) (payload : sn_val)    (* exception object: label + value *)
  | LitList (vs : list sn_val)                    (* immutable list value *)
  | LitTuple (vs : list sn_val)                   (* immutable tuple value *)
  | LitDict (kvs : list (sn_val * sn_val))        (* immutable dict value *)
  | LitSet (vs : list sn_val).                    (* immutable set value *)

(** * Expressions *)
Inductive binop := AddOp | SubOp | MulOp | EqOp | LeOp | LtOp | GtOp | GeOp
  | AndOp | OrOp | NeOp | ModOp | InOp | LenOp | UnionOp | InterOp
  | AppendOp | LengthOp.

Inductive sn_expr :=
  | Val (v : sn_val)
  | Var (x : string)
  | Let (x : string) (e1 e2 : sn_expr)
  | BinOp (op : binop) (e1 e2 : sn_expr)
  | Load (e : sn_expr)
  | Store (e1 e2 : sn_expr)
  | Alloc (e : sn_expr)
  | If (e0 e1 e2 : sn_expr)
  | Raise (e : sn_expr)
  | Try (body : sn_expr) (x : string) (handler : sn_expr)
  | While (e1 e2 : sn_expr)
  | For (x : string) (e1 e2 : sn_expr)
  | Call (f : string) (args : list sn_expr).

(** * Evaluation contexts.  Try IS a context (body reduces inside it). *)
Inductive sn_ectx_item :=
  | LetCtx (x : string) (e2 : sn_expr)
  | BinOpLCtx (op : binop) (v2 : sn_val)
  | BinOpRCtx (op : binop) (e1 : sn_expr)
  | LoadCtx
  | StoreLCtx (v2 : sn_val)
  | StoreRCtx (e1 : sn_expr)
  | AllocCtx
  | IfCtx (e1 e2 : sn_expr)
  | RaiseCtx
  | TryCtx (x : string) (handler : sn_expr)
  | ForCtx (x : string) (e2 : sn_expr).

(** Is this context item neutral (i.e. NOT a try frame)?  Raise unwinds
    through neutral contexts but is caught by try frames. *)
Definition neutral (Ki : sn_ectx_item) : bool :=
  match Ki with TryCtx _ _ => false | _ => true end.

Definition fill_item (Ki : sn_ectx_item) (x : sn_expr) : sn_expr :=
  match Ki with
  | LetCtx x0 e2 => Let x0 x e2
  | BinOpLCtx op v2 => BinOp op x (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 x
  | LoadCtx => Load x
  | StoreLCtx v2 => Store x (Val v2)
  | StoreRCtx e1 => Store e1 x
  | AllocCtx => Alloc x
  | IfCtx e1 e2 => If x e1 e2
  | RaiseCtx => Raise x
  | TryCtx x0 h => Try x x0 h
  | ForCtx x0 e2 => For x0 x e2
  end.

Definition fill_K (K : list sn_ectx_item) (x : sn_expr) : sn_expr :=
  foldr fill_item x K.

(** * Values and to_val.  CRUCIAL: Raise (Val v) is NOT a value. *)
Definition of_val (v : sn_val) : sn_expr := Val v.
Definition to_val (e : sn_expr) : option sn_val :=
  match e with Val v => Some v | _ => None end.
Definition sn_state : Type := gmap loc sn_val.

(** * Results: the two ways a program terminates. *)
Inductive Result :=
  | RVal (v : sn_val)
  | RExn (label : string) (payload : sn_val).

(** A terminal expression is either a value or an uncaught [Raise (Val v)].
    [result_of] reads off the Result; it is None for reducible expressions. *)
Definition result_of (e : sn_expr) : option Result :=
  match e with
  | Val v => Some (RVal v)
  | Raise (Val (LitExn lbl pay)) => Some (RExn lbl pay)
  | _ => None
  end.

(** * Foundational fill / to_val lemmas (FC-independent). *)
Lemma fill_not_val K (x : sn_expr) : to_val x = None -> to_val (fill_K K x) = None.
Proof.
  induction K as [|Ki K IH]; simpl; [auto|].
  intros H. destruct Ki; simpl; reflexivity.
Qed.

Lemma fill_K_val K (x : sn_expr) (v : sn_val) : fill_K K x = Val v <-> K = [] /\ x = Val v.
Proof.
  split.
  - intros H. induction K as [|Ki K IH]; simpl in H.
    + split; auto.
    + destruct Ki; simpl in H; discriminate H.
  - intros [-> ->]; reflexivity.
Qed.

Lemma fill_item_inj Ki (a b : sn_expr) : fill_item Ki a = fill_item Ki b -> a = b.
Proof. destruct Ki; simpl; injection 1; auto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None -> to_val e2 = None ->
  fill_item Ki1 e1 = fill_item Ki2 e2 -> Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; simpl; intros Hn1 Hn2 Heq;
    first [discriminate Heq | idtac];
    injection Heq; intros; subst; simpl in *; try discriminate; auto.
Qed.

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
  | Raise e => Raise (subst x v e)
  | Try body y h =>
      Try (subst x v body) y (if String.eqb x y then h else subst x v h)
  | While e1 e2 => While (subst x v e1) (subst x v e2)
  | For y e1 e2 =>
      For y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | Call f args => Call f (List.map (subst x v) args)
  end.

Fixpoint subst_list (xs : list string) (vs : list sn_val) (e : sn_expr) : sn_expr :=
  match xs, vs with
  | x :: xs', v :: vs' => subst_list xs' vs' (subst x v e)
  | _, _ => e
  end.

(** * Binary operation evaluation (minimal: ints + comparisons). *)
Definition binop_eval (op : binop) (v1 v2 : sn_val) : sn_val :=
  match v1, v2 with
  | LitInt n1, LitInt n2 =>
      match op with
      | AddOp => LitInt (n1 + n2)
      | SubOp => LitInt (n1 - n2)
      | MulOp => LitInt (n1 * n2)
      | EqOp  => LitBool (Z.eqb n1 n2)
      | LeOp  => LitBool (Z.leb n1 n2)
      | LtOp  => LitBool (Z.ltb n1 n2)
      | GtOp  => LitBool (Z.ltb n2 n1)
      | GeOp  => LitBool (Z.leb n2 n1)
      | NeOp  => LitBool (negb (Z.eqb n1 n2))
      | ModOp => LitInt (Z.rem n1 n2)
      | _ => LitUnit
      end
  | LitBool b1, LitBool b2 =>
      match op with
      | AndOp => LitBool (b1 && b2)
      | OrOp  => LitBool (b1 || b2)
       | EqOp  => LitBool (Bool.eqb b1 b2)
       | _ => LitUnit
       end
  | LitList vs, v =>
      match op with
      | AppendOp => LitList (vs ++ [v])
      | LengthOp => LitInt (Z.of_nat (List.length vs))
      | _ => LitUnit
      end
  | LitString s1, LitString s2 =>
      match op with
      | AddOp => LitString (String.append s1 s2)
      | EqOp  => LitBool (String.eqb s1 s2)
      | NeOp  => LitBool (negb (String.eqb s1 s2))
      | LenOp => LitInt (Z.of_nat (String.length s1))
      | _ => LitUnit
      end
  | LitString s, _ =>
      match op with
      | LenOp => LitInt (Z.of_nat (String.length s))
      | _ => LitUnit
      end
  | _, _ => LitUnit
  end.

(** * Function context (opaque specs + transparent defs). *)
Inductive fun_entry :=
  | FunSpec (pre : list sn_val -> Prop) (post : list sn_val -> sn_val -> Prop)
  | FunDef (params : list string) (body : sn_expr).

Class FunCtx := {
  fun_entries : string -> option fun_entry;
  fun_specs_total : forall f pre post vs,
    fun_entries f = Some (FunSpec pre post) ->
    pre vs -> exists v, post vs v;
}.

(** * Pure steps. *)
Inductive pure_step : sn_expr -> sn_expr -> Prop :=
  | PureLet v x e2 : pure_step (Let x (Val v) e2) (subst x v e2)
  | PureBinOp op v1 v2 :
      pure_step (BinOp op (Val v1) (Val v2)) (Val (binop_eval op v1 v2))
  | PureIfTrue e1 e2 : pure_step (If (Val (LitBool true)) e1 e2) e1
  | PureIfFalse e1 e2 : pure_step (If (Val (LitBool false)) e1 e2) e2
  (* Try, normal: body is a value, handler skipped *)
  | PureTryVal v x h : pure_step (Try (Val v) x h) (Val v)
  (* Try, exception: body raised, run handler with x bound to the exn object *)
  | PureTryCatch ev x h :
      pure_step (Try (Raise (Val ev)) x h) (subst x ev h)
  (* Raise unwinding through a neutral context item *)
  | PureRaiseUnwind Ki v :
      neutral Ki = true ->
      pure_step (fill_item Ki (Raise (Val v))) (Raise (Val v))
  (* While unfolds to a guarded body-then-loop *)
  | PureWhile e1 e2 :
      pure_step (While e1 e2)
                (If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit))
  (* For over an empty list terminates *)
  | PureForNil x body :
      pure_step (For x (Val (LitList [])) body) (Val LitUnit)
  (* For over a cons peels the head: bind it, then recurse on the tail *)
  | PureForCons x v vs body :
      pure_step (For x (Val (LitList (v :: vs))) body)
                (Let "_" (subst x v body) (For x (Val (LitList vs)) body)).

(** A pure redex is never a value. *)
Lemma to_val_pure_step x x' : pure_step x x' -> to_val x = None.
Proof.
  intros H; inversion H; subst; simpl; auto.
  destruct Ki; simpl; reflexivity.
Qed.

(** Map value-arguments-to-expressions injection helper. *)
Lemma map_Val_inj (vs1 vs2 : list sn_val) :
  map Val vs1 = map Val vs2 -> vs1 = vs2.
Proof.
  revert vs2. induction vs1 as [|v1 vs1 IH]; intros [|v2 vs2] H;
    simpl in H; try discriminate.
  - reflexivity.
  - injection H as Hv Hvs. f_equal; [exact Hv | apply IH, Hvs].
Qed.

(** * Head steps, prim_step, and the Iris language instance.
    Wrapped in a section with [Context {FC : FunCtx}] so the call
    head steps use the ambient FC. *)
Section with_fun_ctx.
Context `{FC : FunCtx}.

Inductive head_step : sn_expr -> sn_state -> sn_expr -> sn_state -> list sn_expr -> Prop :=
  | HeadLoad l v sigma :
      sigma !! l = Some v ->
      head_step (Load (Val (LitLoc l))) sigma (Val v) sigma []
  | HeadStore l v sigma :
      is_Some (sigma !! l) ->
      head_step (Store (Val (LitLoc l)) (Val v)) sigma
                (Val LitUnit) (<[l:=v]> sigma) []
  | HeadAlloc v sigma l :
      sigma !! l = None ->
      head_step (Alloc (Val v)) sigma (Val (LitLoc l)) (<[l:=v]> sigma) []
  | HeadCallSpec : forall (f : string) (vs : list sn_val) (sigma : sn_state)
      (pre : list sn_val -> Prop) (post : list sn_val -> sn_val -> Prop) (v : sn_val),
      fun_entries f = Some (FunSpec pre post) ->
      pre vs ->
      post vs v ->
      head_step (Call f (map Val vs)) sigma (Val v) sigma []
  | HeadCallUnfold : forall (f : string) (vs : list sn_val) (sigma : sn_state)
      (params : list string) (body : sn_expr),
      fun_entries f = Some (FunDef params body) ->
      length vs = length params ->
      head_step (Call f (map Val vs)) sigma (subst_list params vs body) sigma [].

(** A head redex is never a value. *)
Lemma to_val_head_step x sigma x' sigma' efs :
  head_step x sigma x' sigma' efs -> to_val x = None.
Proof. intros H; inversion H; subst; simpl; auto. Qed.

(** * Primitive step: decompose into an evaluation context + a redex. *)
Definition observation : Type := unit.

Inductive prim_step : sn_expr -> sn_state -> list observation -> sn_expr -> sn_state -> list sn_expr -> Prop :=
  | PrimPureStep K x sigma x' :
      pure_step x x' ->
      prim_step (fill_K K x) sigma [] (fill_K K x') sigma []
  | PrimHeadStep K x sigma x' sigma' efs :
      head_step x sigma x' sigma' efs ->
      prim_step (fill_K K x) sigma [] (fill_K K x') sigma' efs.

Definition reducible (e : sn_expr) (sigma : sn_state) : Prop :=
  exists kappa e' sigma' efs, prim_step e sigma kappa e' sigma' efs.

(** * GATE LEMMA 1: [Raise (Val v)] is a stuck terminal expression.

    An uncaught raise reduces to nothing: it sits in evaluation position
    as the program's exceptional result.  This is the foundational
    encoding -- [Raise (Val v)] is observable but irreducible. *)
Lemma raise_val_irreducible v sigma : ~ reducible (Raise (Val v)) sigma.
Proof.
  intros (kappa & e2 & sigma2 & efs & Hstep).
  inversion Hstep as [K x sg x2 Hpure Heq | K x sg x2 sg2 efs2 Hhead Heq]; subst.
  2: { (* PrimHeadStep *)
       destruct K as [|Ki K2]; simpl in Heq;
       [ subst x; inversion Hhead
       | destruct Ki; simpl in Heq; try discriminate Heq;
         injection Heq as Hin; apply fill_K_val in Hin as [-> ->]; inversion Hhead ]. }
  (* PrimPureStep *)
  destruct K as [|Ki K2]; simpl in Heq.
  2: { destruct Ki; simpl in Heq; try discriminate Heq.
       injection Heq as Hin. apply fill_K_val in Hin as [-> ->].
       apply to_val_pure_step in Hpure. simpl in Hpure. discriminate. }
  subst x.
  inversion Hpure; subst.
  destruct Ki; simpl in H; try discriminate H.
Qed.

End with_fun_ctx.
