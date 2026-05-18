Require Import ZArith String List Bool.
Import ListNotations.

Open Scope Z_scope.

(** * IMP Language — Syntax and Semantics *)

(** Variable names are strings. *)
Definition var := string.

(** Tagged value type — every state entry has a type tag. *)
Inductive value : Type :=
  | VZ (z : Z)
  | VBool (b : bool)
  | VUnit
  | VString (s : string)
  | VFloat (f : Z)   (* float value encoded as scaled integer *)
  | VNone
  | VTuple (ts : list value)
  | VList (xs : list value)
  | VDict (kvs : list (value * value))
  | VBytes (bs : list value)
  | VSet (xs : list value).

(** State: a total mapping from variables to values. *)
Definition state := var -> value.

(** Empty state maps everything to VZ 0. *)
Definition empty_state : state := fun _ => VZ 0%Z.

(** State update: [upd s x v] is [s] with [x] mapped to [v]. *)
Definition upd (s : state) (x : var) (v : value) : state :=
  fun y => if String.eqb x y then v else s y.

(** Convenience: update with a Z value, wrapped in VZ. *)
Definition updZ (s : state) (x : var) (v : Z) : state := upd s x (VZ v).

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

(** Extract Z from a value, defaulting to 0 for non-Z. *)
Definition asZ (v : value) : Z :=
  match v with
  | VZ z => z
  | _ => 0%Z
  end.

(** Extract string from a value, defaulting to empty for non-string. *)
Definition asString (v : value) : string :=
  match v with
  | VString s => s
  | _ => ""%string
  end.

(** Extract float (as Z encoding) from a value, defaulting to 0. *)
Definition asFloat (v : value) : Z :=
  match v with
  | VFloat f => f
  | _ => 0%Z
  end.

(** Inject bool as Z for ABool compatibility. *)
Definition boolToZ (b : bool) : Z := if b then 1%Z else 0%Z.

(** Structural equality on values — dispatches on type tags. *)
Fixpoint value_eqb (v1 v2 : value) : bool :=
  match v1, v2 with
  | VZ z1, VZ z2 => Z.eqb z1 z2
  | VBool b1, VBool b2 => Bool.eqb b1 b2
  | VString s1, VString s2 => String.eqb s1 s2
  | VFloat f1, VFloat f2 => Z.eqb f1 f2
  | VNone, VNone => true
  | VTuple ts1, VTuple ts2 =>
      (fix list_eqb vs1 vs2 :=
         match vs1, vs2 with
         | nil, nil => true
         | v1'::vs1', v2'::vs2' => value_eqb v1' v2' && list_eqb vs1' vs2'
         | _, _ => false
         end) ts1 ts2
  | VList xs1, VList xs2 =>
      (fix list_eqb vs1 vs2 :=
         match vs1, vs2 with
         | nil, nil => true
         | v1'::vs1', v2'::vs2' => value_eqb v1' v2' && list_eqb vs1' vs2'
         | _, _ => false
         end) xs1 xs2
  | VDict kvs1, VDict kvs2 =>
      (fix list_eqb ps1 ps2 :=
         match ps1, ps2 with
         | nil, nil => true
         | (k1,v1)::ps1', (k2,v2)::ps2' => value_eqb k1 k2 && value_eqb v1 v2 && list_eqb ps1' ps2'
         | _, _ => false
         end) kvs1 kvs2
  | VBytes bs1, VBytes bs2 =>
      (fix list_eqb vs1 vs2 :=
         match vs1, vs2 with
         | nil, nil => true
         | v1'::vs1', v2'::vs2' => value_eqb v1' v2' && list_eqb vs1' vs2'
         | _, _ => false
         end) bs1 bs2
  | VSet xs1, VSet xs2 =>
      (fix list_eqb vs1 vs2 :=
         match vs1, vs2 with
         | nil, nil => true
         | v1'::vs1', v2'::vs2' => value_eqb v1' v2' && list_eqb vs1' vs2'
         | _, _ => false
         end) xs1 xs2
  | _, _ => false
  end.

(** ** Arithmetic and Boolean Expressions (mutually recursive) *)
Inductive aexp : Type :=
  | ANum (n : Z)
  | AVar (x : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | AMod (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp)
  | ALen (name : var)              (* length of a heap list/string *)
  | AIndex (name : var) (idx : aexp)  (* nth element of a heap list *)
  | AAppend (a : aexp) (e : aexp)   (* append element, returns new VList *)
  | APop (a : aexp)             (* pop last element, returns new VList *)
  | ASet (a : aexp) (idx : aexp) (val : aexp)  (* set element, returns new VList *)
  | ADictLen (name : var) (key_e : aexp)
  | ADictCount (name : var)
  | ABool (b : bexp)
  | AString (s : string)
  | AFloat (f : Z)   (* float literal, Z-encoded *)
  | ANone            (* None literal *)
  | ATuple (es : list aexp)  (* tuple literal *)
  | AList (es : list aexp)   (* list literal *)
  | ADict (kvs : list (aexp * aexp))  (* dict literal *)
  | ABytes (es : list aexp)  (* bytes literal *)
  | ASetLit (es : list aexp)  (* set literal *)
with bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
  | BOr (b1 b2 : bexp)
  | BIsNone (x : var).

(** Extract list from a value, defaulting to empty. *)
Definition asList (v : value) : list value :=
  match v with VList xs => xs | _ => nil end.

(** Convert Z to string for dict key encoding. *)
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

(** Remove the last element of a list. *)
Fixpoint removelast (xs : list value) : list value :=
  match xs with
  | nil => nil
  | _ :: nil => nil
  | x :: xs' => x :: removelast xs'
  end.

(** Set element at index in a list. *)
Fixpoint set_nth (xs : list value) (n : nat) (v : value) : list value :=
  match xs, n with
  | nil, _ => nil
  | _ :: xs', O => v :: xs'
  | x :: xs', S n' => x :: set_nth xs' n' v
  end.

Definition dict_key (name : var) (key : Z) : var :=
  (name ++ ".v." ++ z_to_string key)%string.

Definition parray_key (name : var) (idx : Z) : var :=
  (name ++ "." ++ z_to_string idx)%string.

Definition parray_len_key (name : var) : var :=
  (name ++ "._len")%string.

Definition dict_count_key (name : var) : var :=
  (name ++ "._count")%string.

Definition dict_keys_key (name : var) : var :=
  (name ++ "._keys")%string.

Definition dict_vals_key (name : var) : var :=
  (name ++ "._vals")%string.

(** Evaluation of arithmetic and boolean expressions. *)

(** Float scale factor: Python floats → Z encoding.  3.14 → 314, 1.5 → 150. *)
Definition float_scale : Z := 100.

Fixpoint aeval (a : aexp) (s : state) : value :=
  match a with
  | ANum n => VZ n
  | AVar x => s x
  | AString lit => VString lit
  | AFloat f => VFloat f
  | ANone => VNone
  | ATuple es => VTuple (map (fun e => aeval e s) es)
  | AList es => VList (map (fun e => aeval e s) es)
  | ADict kvs => VDict (map (fun '(k, v) => (aeval k s, aeval v s)) kvs)
  | ABytes es => VBytes (map (fun e => aeval e s) es)
  | ASetLit es => VSet (map (fun e => aeval e s) es)
  | APlus a1 a2 =>
      match aeval a1 s, aeval a2 s with
      | VFloat f1, VFloat f2 => VFloat (f1 + f2)
      | VFloat f, VZ z => VFloat (f + z * float_scale)
      | VZ z, VFloat f => VFloat (z * float_scale + f)
      | v1, v2 => VZ (asZ v1 + asZ v2)
      end
  | AMinus a1 a2 =>
      match aeval a1 s, aeval a2 s with
      | VFloat f1, VFloat f2 => VFloat (f1 - f2)
      | VFloat f, VZ z => VFloat (f - z * float_scale)
      | VZ z, VFloat f => VFloat (z * float_scale - f)
      | v1, v2 => VZ (asZ v1 - asZ v2)
      end
  | AMult a1 a2 =>
      match aeval a1 s, aeval a2 s with
      | VFloat f1, VFloat f2 => VFloat (f1 * f2 / float_scale)
      | VFloat f, VZ z => VFloat (f * z)
      | VZ z, VFloat f => VFloat (z * f)
      | v1, v2 => VZ (asZ v1 * asZ v2)
      end
  | AMod a1 a2 => VZ (Z.modulo (asZ (aeval a1 s)) (asZ (aeval a2 s)))
  | ADiv a1 a2 => VZ (asZ (aeval a1 s) / asZ (aeval a2 s))
  | ALen name => VZ (asZ (s (parray_len_key name)))
  | AIndex name idx_e => VZ (asZ (s (parray_key name (asZ (aeval idx_e s)))))
  | AAppend a e => VList (asList (aeval a s) ++ [aeval e s])
  | APop a => VList (removelast (asList (aeval a s)))
  | ASet a idx val =>
      VList (set_nth (asList (aeval a s)) (Z.to_nat (asZ (aeval idx s))) (aeval val s))
  | ADictLen name key_e => VZ (asZ (s (parray_len_key (dict_key name (asZ (aeval key_e s))))))
  | ADictCount name => VZ (asZ (s (dict_count_key name)))
  | ABool b => VZ (if beval b s then 1%Z else 0%Z)
  end
with beval (b : bexp) (s : state) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => value_eqb (aeval a1 s) (aeval a2 s)
  | BLe a1 a2 =>
      match aeval a1 s, aeval a2 s with
      | VFloat f1, VFloat f2 => Z.leb f1 f2
      | _, _ => Z.leb (asZ (aeval a1 s)) (asZ (aeval a2 s))
      end
  | BIsNone x => match s x with VNone => true | _ => false end
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
  | CListPop (name : var)
  | CListSet (name : var) (idx val : aexp)
  | CDictSet (name : var) (key val : aexp)
  | CDictGet (name : var) (key : aexp) (target : var)
  | CDictEnsureList (name : var) (key : aexp)
  | CDictAppend (name : var) (key val : aexp)
  | CDictAppendKv (name : var) (key val : aexp)
  | CCall (name : var) (args : list aexp) (pre post : state -> Prop) (writes : list var) (target : var).

(** Havoc a list of variables — set each to VZ 0. *)
Definition clobber (s : state) (vars : list var) : state :=
  fold_left (fun st v => upd st v (VZ 0)) vars s.

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
      ceval (CListNew name) s (upd s (parray_len_key name) (VZ 0))
  | E_ListAppend : forall name val s,
      let len := asZ (s (parray_len_key name)) in
      ceval (CListAppend name val) s
            (upd (upd s (parray_key name len) (aeval val s))
                 (parray_len_key name) (VZ (len + 1)))
  | E_ListPop : forall name s,
      let len := asZ (s (parray_len_key name)) in
      ceval (CListPop name) s
            (upd s (parray_len_key name) (VZ (len - 1)))
  | E_ListSet : forall name idx_e val_e s,
      ceval (CListSet name idx_e val_e) s
            (upd s (parray_key name (asZ (aeval idx_e s))) (aeval val_e s))
  | E_DictSet : forall name key_e val_e s,
      let dk := dict_key name (asZ (aeval key_e s)) in
      let is_new := Z.eqb 0 (asZ (s (parray_len_key dk))) in
      let old_count := asZ (s (dict_count_key name)) in
      let new_count := old_count + (if is_new then 1 else 0) in
      ceval (CDictSet name key_e val_e) s
            (upd (upd (upd s dk (aeval val_e s))
                      (parray_len_key dk) (VZ 1))
                 (dict_count_key name) (VZ new_count))
  | E_DictGet : forall name key_e target s,
      ceval (CDictGet name key_e target) s
            (upd s target (s (dict_key name (asZ (aeval key_e s)))))
  | E_DictEnsureList : forall name key_e s,
      let dk := dict_key name (asZ (aeval key_e s)) in
      ceval (CDictEnsureList name key_e) s
            (if Z.eqb (asZ (s (parray_len_key dk))) 0
             then upd s (parray_len_key dk) (VZ 0)
             else s)
  | E_DictAppend : forall name key_e val_e s,
      let dk := dict_key name (asZ (aeval key_e s)) in
      let len := asZ (s (parray_len_key dk)) in
      ceval (CDictAppend name key_e val_e) s
            (upd (upd s (parray_key dk len) (aeval val_e s))
                 (parray_len_key dk) (VZ (len + 1)))
  | E_DictAppendKv : forall name key_e val_e s,
      let dk := dict_key name (asZ (aeval key_e s)) in
      let is_new := Z.eqb 0 (asZ (s (parray_len_key dk))) in
      let c := asZ (s (dict_count_key name)) in
      let new_c := c + (if is_new then 1 else 0) in
      let s1 := upd (upd (upd s dk (aeval val_e s))
                         (parray_len_key dk) (VZ 1))
                    (parray_key (dict_vals_key name) c) (aeval val_e s) in
      ceval (CDictAppendKv name key_e val_e) s
            (upd (upd s1 (parray_key (dict_keys_key name) c) (aeval key_e s))
                 (dict_count_key name) (VZ new_c))
  | E_Call : forall name args pre post writes target s r,
      pre s ->
      post (upd s target (VZ r)) ->
      ceval (CCall name args pre post writes target) s
            (clobber (upd s target (VZ r)) writes).

(** ** Notation *)
Open Scope Z_scope.
