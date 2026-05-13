Require Import ZArith String List.
Import ListNotations.

Open Scope Z_scope.

(** * IMP Language — Syntax and Semantics *)

(** Variable names are strings. *)
Definition var := string.

(** State: a total mapping from variables to integers. *)
Definition state := var -> Z.

(** Empty state maps everything to 0. *)
Definition empty_state : state := fun _ => 0%Z.

(** State update: [upd s x v] is [s] with [x] mapped to [v]. *)
Definition upd (s : state) (x : var) (v : Z) : state :=
  fun y => if String.eqb x y then v else s y.

(** We assume functional extensionality for state equality. *)
Axiom functional_extensionality : forall {A B} (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Lemma upd_eq : forall s x v, upd s x v x = v.
Proof.
  intros s x v. unfold upd. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma upd_ne : forall s x y v, x <> y -> upd s x v y = s y.
Proof.
  intros s x y v Hne. unfold upd.
  apply String.eqb_neq in Hne.
  rewrite Hne. reflexivity.
Qed.

Lemma upd_same : forall s x v1 v2, upd (upd s x v1) x v2 = upd s x v2.
Proof.
  intros s x v1 v2. apply functional_extensionality. intros y.
  unfold upd. destruct (String.eqb x y) eqn:Heq; reflexivity.
Qed.

Lemma upd_swap : forall s x y vx vy, x <> y ->
  upd (upd s x vx) y vy = upd (upd s y vy) x vx.
Proof.
  intros s x y vx vy Hne. apply functional_extensionality. intros z.
  unfold upd.
  destruct (String.eqb x z) eqn:Exz; destruct (String.eqb y z) eqn:Eyz; auto.
  apply String.eqb_eq in Exz. apply String.eqb_eq in Eyz.
  subst x. subst y. exfalso. apply Hne. reflexivity.
Qed.

(** ** Arithmetic Expressions *)
Inductive aexp : Type :=
  | ANum (n : Z)
  | AVar (x : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | AMod (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp)
  | ALen (name : var)
  | AIndex (name : var) (idx : aexp)
  | ADictLen (name : var) (key_e : aexp).

(** Convert Z to string for array key encoding. *)
Fixpoint pos_to_string (p : positive) : string :=
  match p with
  | xH => "1"%string
  | xO p' => ("0" ++ pos_to_string p')%string
  | xI p' => ("1" ++ pos_to_string p')%string
  end.

Definition z_to_string (z : Z) : string :=
  match z with
  | Z0 => "0"%string
  | Zpos p => pos_to_string p
  | Zneg p => ("-" ++ pos_to_string p)%string
  end.

Definition parray_key (name : var) (idx : Z) : var :=
  (name ++ "." ++ z_to_string idx)%string.

Definition parray_len_key (name : var) : var :=
  (name ++ "._len")%string.

Definition dict_key (name : var) (key : Z) : var :=
  (name ++ ".v." ++ z_to_string key)%string.

(** Evaluation of arithmetic expressions. *)
Fixpoint aeval (a : aexp) (s : state) : Z :=
  match a with
  | ANum n => n
  | AVar x => s x
  | APlus a1 a2 => (aeval a1 s) + (aeval a2 s)
  | AMinus a1 a2 => (aeval a1 s) - (aeval a2 s)
  | AMult a1 a2 => (aeval a1 s) * (aeval a2 s)
  | AMod a1 a2 => Z.modulo (aeval a1 s) (aeval a2 s)
  | ADiv a1 a2 => (aeval a1 s) / (aeval a2 s)
  | ALen name => s (parray_len_key name)
  | AIndex name idx_e => s (parray_key name (aeval idx_e s))
  | ADictLen name key_e => s (parray_len_key (dict_key name (aeval key_e s)))
  end.

(** ** Boolean Expressions *)
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
  | BOr (b1 b2 : bexp).

(** Evaluation of boolean expressions. *)
Fixpoint beval (b : bexp) (s : state) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Z.eqb (aeval a1 s) (aeval a2 s)
  | BLe a1 a2 => Z.leb (aeval a1 s) (aeval a2 s)
  | BNot b' => negb (beval b' s)
  | BAnd b1 b2 => (beval b1 s) && (beval b2 s)
  | BOr b1 b2 => (beval b1 s) || (beval b2 s)
  end.

(** ** Commands *)
Inductive com : Type :=
  | CSkip
  | CAss (x : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (inv : state -> Prop) (c : com)
  | CHavoc (vars : list var)
  | CListNew (name : var)
  | CListAppend (name : var) (val : aexp)
  | CListSet (name : var) (idx val : aexp)
  | CDictSet (name : var) (key val : aexp)
  | CDictGet (name : var) (key : aexp) (target : var)
  | CDictEnsureList (name : var) (key : aexp)
  | CDictAppend (name : var) (key val : aexp).

(** Big-step operational semantics: [(c, s) ⇓ s']. *)
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall s,
      ceval CSkip s s
  | E_Ass : forall s x a,
      ceval (CAss x a) s (upd s x (aeval a s))
  | E_Seq : forall c1 c2 s s' s'',
      ceval c1 s s' ->
      ceval c2 s' s'' ->
      ceval (CSeq c1 c2) s s''
  | E_IfTrue : forall b c1 c2 s s',
      beval b s = true ->
      ceval c1 s s' ->
      ceval (CIf b c1 c2) s s'
  | E_IfFalse : forall b c1 c2 s s',
      beval b s = false ->
      ceval c2 s s' ->
      ceval (CIf b c1 c2) s s'
  | E_WhileFalse : forall b inv c s,
      beval b s = false ->
      ceval (CWhile b inv c) s s
  | E_WhileTrue : forall b inv c s s' s'',
      beval b s = true ->
      ceval c s s' ->
      ceval (CWhile b inv c) s' s'' ->
      ceval (CWhile b inv c) s s''
  | E_Havoc : forall A s s',
      (forall x, ~ In x A -> s' x = s x) ->
      ceval (CHavoc A) s s'
  | E_ListNew : forall name s,
      ceval (CListNew name) s (upd s (parray_len_key name) 0)
  | E_ListAppend : forall name val s,
      ceval (CListAppend name val) s
            (upd (upd s (parray_key name (s (parray_len_key name))) (aeval val s))
                 (parray_len_key name) (s (parray_len_key name) + 1))
  | E_ListSet : forall name idx_e val_e s,
      ceval (CListSet name idx_e val_e) s
            (upd s (parray_key name (aeval idx_e s)) (aeval val_e s))
  | E_DictSet : forall name key_e val_e s,
      ceval (CDictSet name key_e val_e) s
            (upd (upd s (dict_key name (aeval key_e s)) (aeval val_e s))
                 (parray_len_key (dict_key name (aeval key_e s))) 1)
  | E_DictGet : forall name key_e target s,
      ceval (CDictGet name key_e target) s
            (upd s target (s (dict_key name (aeval key_e s))))
  | E_DictEnsureList : forall name key_e s,
      let dk := dict_key name (aeval key_e s) in
      ceval (CDictEnsureList name key_e) s
            (upd s (parray_len_key dk) (s (parray_len_key dk)))
  | E_DictAppend : forall name key_e val_e s,
      let dk := dict_key name (aeval key_e s) in
      ceval (CDictAppend name key_e val_e) s
            (upd (upd s (parray_key dk (s (parray_len_key dk))) (aeval val_e s))
                 (parray_len_key dk) (s (parray_len_key dk) + 1)).

(** ** Notation *)
(** Scope for IMP notation (opened locally, not globally). *)
Open Scope Z_scope.
