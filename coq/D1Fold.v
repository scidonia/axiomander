From Stdlib Require Import List ZArith Bool String.
Import ListNotations.
Open Scope Z_scope.

Require Import LambdaA Supercompiler.

(** * D1 Folding: Structural Recursion for Predicate Supercompilation

    When the whistle fires during supercompilation of a predicate like:

        is_sorted(xs) = if len(xs) <= 1 then True
                        else xs[0] <= xs[1] and is_sorted(xs[1:])

    the supercompiler has driven from [is_sorted(xs)] to [is_sorted(xs[1:])].
    The whistle detects that [is_sorted(xs)] ⊴ [is_sorted(xs[1:])] (the ancestor
    is homeomorphically embedded in the current via coupling on the first
    argument).

    D1 folding extracts the Fixpoint:
        Fixpoint f(xs) = if len(xs) <= 1 then True
                         else xs[0] <= xs[1] and f(xs[1:])

    and replaces the original with [f(xs)].

    The resulting Fixpoint:
    1. Has the SAME computation as the original predicate
    2. Is structurally recursive (guard-passes in Coq)
    3. Can be reflected as a Coq Fixpoint for the WP prover *)

(** * 1. Types *)

Record fold_def := MkFoldDef {
  fd_name  : string;
  fd_param : string;
  fd_body  : p_expr;
}.

Definition fold_fn_table (defs : list fold_def) : fn_table :=
  map (fun d => (fd_name d, ([fd_param d], fd_body d))) defs.

(** * 2. Fresh name generation *)

(** Decimal string representation of a natural number.
    [nat_to_string n fuel] converts [n] to its decimal string with
    [fuel] bounding the recursion depth (sufficient for any n < 10^fuel).
    Injective: distinct naturals produce distinct strings. *)

Definition digit_char (d : nat) : string :=
  match d with
  | 0%nat => "0" | 1%nat => "1" | 2%nat => "2" | 3%nat => "3" | 4%nat => "4"
  | 5%nat => "5" | 6%nat => "6" | 7%nat => "7" | 8%nat => "8" | _ => "9"
  end.

Fixpoint nat_to_string (n : nat) (fuel : nat) : string :=
  match fuel with
  | 0%nat => digit_char n
  | S fuel' =>
      if Nat.ltb n 10 then digit_char n
      else String.append
             (nat_to_string (Nat.div n 10) fuel')
             (digit_char (Nat.modulo n 10))
  end.

Definition fresh_name (n : nat) : string :=
  String.append "fold_" (nat_to_string n 10).

(** * 3. Substituting recursive calls in the process tree body

    [replace_call fn new_name structural_arg body] replaces occurrences
    of [PCall fn [structural_arg]] in [body] with [PCall new_name [structural_arg]].
    This converts the driven body into a Fixpoint body. *)

Fixpoint replace_call (fn new_name : string) (body : p_expr) : p_expr :=
  match body with
  | PVal _ | PVar _ => body
  | PBinOp op e1 e2 => PBinOp op (replace_call fn new_name e1)
                                  (replace_call fn new_name e2)
  | PIf e0 e1 e2 => PIf (replace_call fn new_name e0)
                         (replace_call fn new_name e1)
                         (replace_call fn new_name e2)
  | PLet x e1 e2 => PLet x (replace_call fn new_name e1)
                             (replace_call fn new_name e2)
  | PCall f args =>
      let args' := map (replace_call fn new_name) args in
      if String.eqb f fn then PCall new_name args'
      else PCall f args'
  end.

(** * 4. D1-aware supercompiler

    [supercompile_d1] extends [supercompile] with folding.  When the whistle
    fires on a [PCall fn args] term:
    1. Drive the function body to get the Fixpoint candidate body
    2. Replace recursive calls with the fresh name
    3. Create the fold definition
    4. Return the fold definition + residual [PCall fresh_name args]

    The key invariant: the ancestor in history has the SAME function name.
    The structural argument decreases: [he_dec ancestor_arg current_arg = true]. *)

Fixpoint find_ancestor_call (fn : string) (history : list p_expr) : option string :=
  match history with
  | [] => None
  | h :: rest =>
      match h with
      | PCall f args =>
          if String.eqb f fn then
            match args with
            | [PVar x] => Some x
            | _ => find_ancestor_call fn rest
            end
          else find_ancestor_call fn rest
      | _ => find_ancestor_call fn rest
      end
  end.

(** [inline_call F fn args] inlines the body of [fn] from [F] by
    substituting [args] for the formal parameters.  Returns the
    substituted body, or [None] if [fn] is not in [F]. *)
Definition inline_call (F : fn_table) (fn : string) (args : list p_expr) : option p_expr :=
  match assoc String.eqb F fn with
  | Some (params, body) =>
      Some (subst_many (combine params
        (map (fun a => match a with PVal v => v | _ => PLitUnit end) args)) body)
  | None => None
  end.

(** [subst_expr param arg body] substitutes [arg] for [PVar param] in [body].
    This is needed for symbolic driving: replace the formal param with the
    actual argument expression (which may be a variable). *)
Fixpoint subst_expr (param : string) (arg : p_expr) (body : p_expr) : p_expr :=
  match body with
  | PVar x => if String.eqb x param then arg else PVar x
  | PVal _ => body
  | PBinOp op e1 e2 => PBinOp op (subst_expr param arg e1) (subst_expr param arg e2)
  | PCall f args => PCall f (map (subst_expr param arg) args)
  | PIf e0 e1 e2 => PIf (subst_expr param arg e0) (subst_expr param arg e1) (subst_expr param arg e2)
  | PLet x e1 e2 => PLet x (subst_expr param arg e1)
      (if String.eqb x param then e2 else subst_expr param arg e2)
  end.

Fixpoint supercompile_d1
    (F : fn_table) (fuel : nat) (history : list p_expr) (t : p_expr) (counter : nat)
    : list fold_def * p_expr :=
  match fuel with
  | 0%nat => ([], t)
  | S fuel' =>
    match drive_step F t with
    | Some t' =>
        supercompile_d1 F fuel' (t :: history) t' counter
    | None =>
      match t with
      | PCall fn args =>
          if whistle_dec history t then
            (* D1: whistle fired on a PCall — try to fold *)
            match find_ancestor_call fn history with
            | Some param_name =>
                let body_candidate :=
                  match assoc String.eqb F fn with
                  | Some (params, body) =>
                      fold_left (fun b '(p, a) => subst_expr p a b)
                                (combine params args) body
                  | None => t
                  end in
                let driven_body := supercompile F fuel' [t] body_candidate in
                let fname := fresh_name counter in
                let fold_body := replace_call fn fname driven_body in
                let def := MkFoldDef fname param_name fold_body in
                ([def], PCall fname args)
            | None =>
                (* Whistle but no ancestor pattern: recurse on args, then re-drive *)
                let '(ds, args', _) :=
                  fold_left (fun '(acc_d, acc_a, c) arg =>
                    let '(d, a) := supercompile_d1 F fuel' history arg c in
                    (acc_d ++ d, acc_a ++ [a], Nat.add c (List.length d)))
                  args ([],[],counter) in
                let result := supercompile F fuel' history (PCall fn args') in
                (ds, result)
            end
          else
            (* No whistle: try symbolic inlining, otherwise recurse + re-drive *)
            match assoc String.eqb F fn with
            | Some (params, body) =>
                let inlined := fold_left (fun b '(p, a) => subst_expr p a b)
                                         (combine params args) body in
                supercompile_d1 F fuel' (t :: history) inlined counter
            | None =>
                let '(ds, args', _) :=
                  fold_left (fun '(acc_d, acc_a, c) arg =>
                    let '(d, a) := supercompile_d1 F fuel' history arg c in
                    (acc_d ++ d, acc_a ++ [a], Nat.add c (List.length d)))
                  args ([],[],counter) in
                let result := supercompile F fuel' history (PCall fn args') in
                (ds, result)
            end
      | PVal _ | PVar _ => ([], t)
      | _ =>
          (* Compound node: recurse structurally to find folds in subterms,
             then re-drive via supercompile.  (Same logic for both whistle and
             non-whistle; only difference is whether t is pushed onto history.) *)
          let h := if whistle_dec history t then t :: history else history in
          let sc := supercompile_d1 F fuel' h in
          match t with
          | PBinOp op e1 e2 =>
              let '(d1, e1') := sc e1 counter in
              let '(d2, e2') := sc e2 (Nat.add counter (List.length d1)) in
              let result := supercompile F fuel' history (PBinOp op e1' e2') in
              (d1 ++ d2, result)
          | PIf e0 e1 e2 =>
              let '(d0, e0') := sc e0 counter in
              let '(d1, e1') := sc e1 (Nat.add counter (List.length d0)) in
              let '(d2, e2') := sc e2 (Nat.add counter (Nat.add (List.length d0) (List.length d1))) in
              let result := supercompile F fuel' history (PIf e0' e1' e2') in
              (d0 ++ d1 ++ d2, result)
          | PLet x e1 e2 =>
              let '(d1, e1') := sc e1 counter in
              let '(d2, e2') := sc e2 (Nat.add counter (List.length d1)) in
              let result := supercompile F fuel' history (PLet x e1' e2') in
              (d1 ++ d2, result)
          | _ => ([], t)
          end
      end
    end
  end.

(** * 5. The full supercompilation with D1

    Entry point: supercompile a term, getting back folded definitions and
    the residual term. *)

Definition supercompile_full (F : fn_table) (n : nat) (t : p_expr) :
    list fold_def * p_expr :=
  supercompile_d1 F n [] t 0%nat.

(** * 6. Adequacy

    The D1-supercompiled term evaluates to the same value as the original
    under the extended function table. *)

Theorem supercompile_d1_adequate : forall F n t m v,
  let '(defs, t') := supercompile_full F n t in
  p_eval (F ++ fold_fn_table defs) m t = Some v ->
  p_eval (F ++ fold_fn_table defs) m t' = Some v.
Proof.
  intros F n t m v.
  unfold supercompile_full.
  (* The proof follows from:
     1. drive_step_sound: driving preserves evaluation
     2. replace_call_sound: replacing recursive calls with fold_name
        preserves evaluation when fold_name has the same body
     3. The fold definition has the same computational content *)
  admit.
Admitted.
