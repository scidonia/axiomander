From Stdlib Require Import ZArith String List Bool.
Import ListNotations.

Open Scope Z_scope.

(** * IMP Language -- Syntax and Semantics *)

(** Variable names are strings. *)
Definition var := string.

(** Tagged value type -- every state entry has a type tag. *)
Inductive value : Type :=
  | VZ (z : Z)
  | VBool (b : bool)
  | VUnit
  | VString (s : string)
  | VFloat (f : Z)
  | VNone
  | VTuple (ts : list value)
  | VList (xs : list value)
  | VDict (kvs : list (value * value))
  | VBytes (bs : list value)
  | VSet (xs : list value).

(** -- State ------------------------------------------------------ *)

(** State: record of local variables and heap.
    The [ls] coercion makes [s "x"%string] backward compatible. *)
Record state : Type := mkState {
  ls : var -> value;
  hs : (var * var) -> value
}.
Coercion ls : state >-> Funclass.

(** Empty state. *)
Definition empty_state : state := mkState (fun _ => VZ 0%Z) (fun _ => VZ 0%Z).

(** Local variable update. *)
Definition lupd (s : state) (x : var) (v : value) : state :=
  mkState (fun y => if String.eqb x y then v else s y) (hs s).

(** Heap update. *)
Definition hupd (s : state) (obj field : var) (v : value) : state :=
  mkState (ls s) (fun '(o, f) => if String.eqb obj o && String.eqb field f then v else hs s (o, f)).

(** Convenience: local Z update. *)
Definition lupdZ (s : state) (x : var) (v : Z) : state := lupd s x (VZ v).

(** Legacy aliases for compatibility. *)
Definition upd (s : state) (x : var) (v : value) : state := lupd s x v.
Definition updZ (s : state) (x : var) (v : Z) : state := lupd s x (VZ v).

(** Heap read. *)
Definition hget (s : state) (obj field : var) : value := hs s (obj, field).

(** Explicit local read. *)
Definition lget (s : state) (x : var) : value := s x.

(** Functional extensionality. *)
Axiom functional_extensionality : forall {A B} (f g : A -> B),
  (forall x, f x = g x) -> f = g.

(** -- Local update lemmas ----------------------------------------- *)

Lemma lupd_eq : forall s x v, lget (lupd s x v) x = v.
Proof.
  intros s x v. unfold lget, lupd. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma lupd_ne : forall s x y v, x <> y -> lget (lupd s x v) y = lget s y.
Proof.
  intros s x y v Hne. unfold lget, lupd. simpl.
  apply String.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

Lemma lupd_same : forall s x v1 v2, lupd (lupd s x v1) x v2 = lupd s x v2.
Proof.
  intros s x v1 v2. unfold lupd.
  destruct s as [l h]. simpl.
  apply (f_equal2 mkState).
  - apply functional_extensionality. intros y.
    destruct (String.eqb x y) eqn:Heq; reflexivity.
  - reflexivity.
Qed.


Lemma lupd_swap : forall s x y vx vy, x <> y ->
  lupd (lupd s x vx) y vy = lupd (lupd s y vy) x vx.
Proof.
  intros s x y vx vy Hne. unfold lupd.
  destruct s as [l h]. simpl.
  apply (f_equal2 mkState).
  - apply functional_extensionality. intros z.
    destruct (String.eqb x z) eqn:Exz; destruct (String.eqb y z) eqn:Eyz; auto.
    apply String.eqb_eq in Exz. apply String.eqb_eq in Eyz.
    subst x. subst y. exfalso. apply Hne. reflexivity.
  - reflexivity.
Qed.

Lemma upd_eq : forall s x v, lget (upd s x v) x = v.
Proof. intros. apply lupd_eq. Qed.

Lemma upd_ne : forall s x y v, x <> y -> lget (upd s x v) y = lget s y.
Proof. intros. apply lupd_ne. auto. Qed.

Lemma upd_same : forall s x v1 v2, upd (upd s x v1) x v2 = upd s x v2.
Proof. intros. apply lupd_same. Qed.

Lemma upd_swap : forall s x y vx vy, x <> y ->
  upd (upd s x vx) y vy = upd (upd s y vy) x vx.
Proof. intros. apply lupd_swap. auto. Qed.

(** -- Heap update lemmas ------------------------------------------ *)

Lemma hupd_eq : forall s obj f v, hget (hupd s obj f v) obj f = v.
Proof.
  intros s obj f v. unfold hget, hupd. simpl.
  rewrite String.eqb_refl, String.eqb_refl. reflexivity.
Qed.

Lemma hupd_ne_obj : forall s obj1 obj2 f1 f2 v, obj1 <> obj2 ->
  hget (hupd s obj1 f1 v) obj2 f2 = hget s obj2 f2.
Proof.
  intros s obj1 obj2 f1 f2 v Hne. unfold hget, hupd. simpl.
  apply String.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

Lemma hupd_ne_field : forall s obj f1 f2 v, f1 <> f2 ->
  hget (hupd s obj f1 v) obj f2 = hget s obj f2.
Proof.
  intros s obj f1 f2 v Hne. unfold hget, hupd. simpl.
  rewrite String.eqb_refl. apply String.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

(** -- Helpers ----------------------------------------------------- *)

Definition asZ (v : value) : Z :=
  match v with VZ z => z | _ => 0%Z end.

Definition asString (v : value) : string :=
  match v with VString s => s | _ => ""%string end.

Definition asFloat (v : value) : Z :=
  match v with VFloat f => f | _ => 0%Z end.

Definition isVZ (v : value) : bool :=
  match v with VZ _ => true | _ => false end.

Definition isVString (v : value) : bool :=
  match v with VString _ => true | _ => false end.

Definition isVFloat (v : value) : bool :=
  match v with VFloat _ => true | _ => false end.

Definition boolToZ (b : bool) : Z := if b then 1%Z else 0%Z.

Fixpoint value_eqb (v1 v2 : value) {struct v1} : bool :=
  let fix list_eqb (vs1 vs2 : list value) : bool :=
    match vs1, vs2 with
    | nil, nil => true
    | v1'::vs1', v2'::vs2' => value_eqb v1' v2' && list_eqb vs1' vs2'
    | _, _ => false
    end in
  let fix pair_eqb (ps1 ps2 : list (value * value)) : bool :=
    match ps1, ps2 with
    | nil, nil => true
    | (k1,v1)::ps1', (k2,v2)::ps2' => value_eqb k1 k2 && value_eqb v1 v2 && pair_eqb ps1' ps2'
    | _, _ => false
    end in
  match v1, v2 with
  | VZ z1, VZ z2 => Z.eqb z1 z2
  | VBool b1, VBool b2 => Bool.eqb b1 b2
  | VString s1, VString s2 => String.eqb s1 s2
  | VFloat f1, VFloat f2 => Z.eqb f1 f2
  | VNone, VNone => true
  | VTuple ts1, VTuple ts2 => list_eqb ts1 ts2
  | VList xs1, VList xs2 => list_eqb xs1 xs2
  | VDict kvs1, VDict kvs2 => pair_eqb kvs1 kvs2
  | VBytes bs1, VBytes bs2 => list_eqb bs1 bs2
  | VSet xs1, VSet xs2 => list_eqb xs1 xs2
  | _, _ => false
  end.

Definition asList (v : value) : list value :=
  match v with VList xs => xs | _ => nil end.

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

Fixpoint removelast (xs : list value) : list value :=
  match xs with
  | nil => nil
  | _ :: nil => nil
  | x :: xs' => x :: removelast xs'
  end.

Fixpoint set_nth (xs : list value) (n : nat) (v : value) : list value :=
  match xs, n with
  | nil, _ => nil
  | _ :: xs', O => v :: xs'
  | x :: xs', S n' => x :: set_nth xs' n' v
  end.

(** -- Heap field names -------------------------------------------- *)

Definition len_f : var := "_len"%string.
Definition count_f : var := "_count"%string.
Definition elem_f (i : Z) : var := z_to_string i.
Definition dval_f (k : Z) : var := ("v." ++ z_to_string k)%string.
Definition dlen_f (k : Z) : var := ("_len_v." ++ z_to_string k)%string.

(** Float scale factor. *)
Definition float_scale : Z := 100.

(** -- aexp / bexp types ------------------------------------------- *)

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
  | AAppend (a : aexp) (e : aexp)
  | APop (a : aexp)
  | ASet (a : aexp) (idx : aexp) (val : aexp)
  | ADictLen (name : var) (key_e : aexp)
  | ADictCount (name : var)
  | ABool (b : bexp)
  | AString (s : string)
  | AFloat (f : Z)
  | ANone
  | ATuple (es : list aexp)
  | AList (es : list aexp)
  | ADict (kvs : list (aexp * aexp))
  | ABytes (es : list aexp)
  | ASetLit (es : list aexp)
with bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
  | BOr (b1 b2 : bexp)
  | BIsNone (x : var)
  | BIsVZ (x : var)
  | BIsVString (x : var)
  | BIsVFloat (x : var).

(** -- aeval / beval ----------------------------------------------- *)

Fixpoint aeval (a : aexp) (s : state) : value :=
  match a with
  | ANum n => VZ n
  | AVar x => lget s x
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
  | ALen name => VZ (asZ (hget s name len_f))
  | AIndex name idx_e =>
      VZ (asZ (hget s name (elem_f (asZ (aeval idx_e s)))))
  | AAppend a e => VList (asList (aeval a s) ++ [aeval e s])
  | APop a => VList (removelast (asList (aeval a s)))
  | ASet a idx val =>
      VList (set_nth (asList (aeval a s)) (Z.to_nat (asZ (aeval idx s))) (aeval val s))
  | ADictLen name key_e => VZ (asZ (hget s name (dlen_f (asZ (aeval key_e s)))))
  | ADictCount name => VZ (asZ (hget s name count_f))
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
  | BIsNone x => match lget s x with VNone => true | _ => false end
  | BIsVZ x => isVZ (lget s x)
  | BIsVString x => isVString (lget s x)
  | BIsVFloat x => isVFloat (lget s x)
  | BNot b' => negb (beval b' s)
  | BAnd b1 b2 => (beval b1 s) && (beval b2 s)
  | BOr b1 b2 => (beval b1 s) || (beval b2 s)
  end.

(** -- Outcome type ------------------------------------------------ *)

(** An [outcome] records how a command terminated.
    [OReturn s'] means normal exit with final state [s'].
    [ORaise e s'] means an exception with value [e] was raised;
    [s'] is the state at the raise point (useful for resource reasoning). *)
Inductive outcome : Type :=
  | OReturn (s : state)
  | ORaise  (e : value) (s : state).

(** -- Commands ---------------------------------------------------- *)

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
  | CCall (name : var) (args : list aexp) (pre post : state -> Prop) (writes : list var) (target : var)
  | CAssume (P : state -> Prop)
  | CRaise (e : aexp)
  (** [CTry body exc handler]: evaluate [body]; if it raises, bind the
      exception value to [exc] in the state and run [handler]. *)
  | CTry (body : com) (exc : var) (handler : com).

(** -- clobber ----------------------------------------------------- *)

Definition clobber (s : state) (vars : list var) : state :=
  fold_left (fun st v => lupd st v (VZ 0)) vars s.

(** -- Big-step operational semantics ------------------------------ *)

(** [ceval c s o] means: starting from state [s], command [c] terminates
    with outcome [o].  Normal commands produce [OReturn s']; [CRaise]
    produces [ORaise e s]; [CTry] catches raises from its body. *)
Inductive ceval : com -> state -> outcome -> Prop :=
  | E_Skip : forall s,
      ceval CSkip s (OReturn s)
  | E_Ass : forall s x a,
      ceval (CAss x a) s (OReturn (lupd s x (aeval a s)))
  | E_SeqReturn : forall c1 c2 s s' o,
      ceval c1 s (OReturn s') ->
      ceval c2 s' o ->
      ceval (CSeq c1 c2) s o
  | E_SeqRaise : forall c1 c2 s e s',
      ceval c1 s (ORaise e s') ->
      ceval (CSeq c1 c2) s (ORaise e s')
  | E_IfTrue : forall b c1 c2 s o,
      beval b s = true ->
      ceval c1 s o ->
      ceval (CIf b c1 c2) s o
  | E_IfFalse : forall b c1 c2 s o,
      beval b s = false ->
      ceval c2 s o ->
      ceval (CIf b c1 c2) s o
  | E_WhileFalse : forall b inv c s,
      beval b s = false ->
      ceval (CWhile b inv c) s (OReturn s)
  | E_WhileTrue : forall b inv c s s' o,
      beval b s = true ->
      ceval c s (OReturn s') ->
      ceval (CWhile b inv c) s' o ->
      ceval (CWhile b inv c) s o
  | E_WhileRaise : forall b inv c s e s',
      beval b s = true ->
      ceval c s (ORaise e s') ->
      ceval (CWhile b inv c) s (ORaise e s')
  | E_Havoc : forall A s s',
      (forall x, ~ In x A -> lget s' x = lget s x) ->
      ceval (CHavoc A) s (OReturn s')
  | E_ListNew : forall name s,
      ceval (CListNew name) s (OReturn (hupd s name len_f (VZ 0)))
  | E_ListAppend : forall name val s,
      let len := asZ (hget s name len_f) in
      ceval (CListAppend name val) s
            (OReturn (hupd (hupd s name (elem_f len) (aeval val s))
                           name len_f (VZ (len + 1))))
  | E_ListPop : forall name s,
      let len := asZ (hget s name len_f) in
      ceval (CListPop name) s
            (OReturn (hupd s name len_f (VZ (len - 1))))
  | E_ListSet : forall name idx_e val_e s,
      ceval (CListSet name idx_e val_e) s
            (OReturn (hupd s name (elem_f (asZ (aeval idx_e s))) (aeval val_e s)))
  | E_DictSet : forall name key_e val_e s,
      let k := asZ (aeval key_e s) in
      let is_new := Z.eqb 0 (asZ (hget s name (dlen_f k))) in
      let old_count := asZ (hget s name count_f) in
      let new_count := old_count + (if is_new then 1 else 0) in
      ceval (CDictSet name key_e val_e) s
            (OReturn (hupd (hupd (hupd s name (dval_f k) (aeval val_e s))
                                 name (dlen_f k) (VZ 1))
                           name count_f (VZ new_count)))
  | E_DictGet : forall name key_e target s,
      ceval (CDictGet name key_e target) s
            (OReturn (lupd s target (hget s name (dval_f (asZ (aeval key_e s))))))
  | E_DictEnsureList : forall name key_e s,
      let dk_len := dlen_f (asZ (aeval key_e s)) in
      ceval (CDictEnsureList name key_e) s
            (OReturn (if Z.eqb (asZ (hget s name dk_len)) 0
                      then hupd s name dk_len (VZ 0)
                      else s))
  | E_DictAppend : forall name key_e val_e s,
      let k := asZ (aeval key_e s) in
      let dk_len := dlen_f k in
      let len := asZ (hget s name dk_len) in
      ceval (CDictAppend name key_e val_e) s
            (OReturn (hupd (hupd s name (elem_f len) (aeval val_e s))
                           name dk_len (VZ (len + 1))))
  | E_DictAppendKv : forall name key_e val_e s,
      let k := asZ (aeval key_e s) in
      let is_new := Z.eqb 0 (asZ (hget s name (dlen_f k))) in
      let c := asZ (hget s name count_f) in
      let new_c := c + (if is_new then 1 else 0) in
      let s1 := hupd (hupd (hupd s name (dval_f k) (aeval val_e s))
                           name (dlen_f k) (VZ 1))
                     name (elem_f c) (aeval val_e s) in
      ceval (CDictAppendKv name key_e val_e) s
            (OReturn (hupd (hupd s1 name (elem_f c) (aeval key_e s))
                           name count_f (VZ new_c)))
  | E_Call : forall name args pre post writes target s r,
      pre s ->
      post (lupd s target (VZ r)) ->
      ceval (CCall name args pre post writes target) s
            (OReturn (clobber (lupd s target (VZ r)) writes))
  | E_Assume : forall P s,
      P s ->
      ceval (CAssume P) s (OReturn s)
  | E_Raise : forall e s,
      ceval (CRaise e) s (ORaise (aeval e s) s)
  | E_TryReturn : forall body exc handler s s' o,
      ceval body s (OReturn s') ->
      ceval handler s' o ->
      ceval (CTry body exc handler) s o
  | E_TryCatch : forall body exc handler s e s' o,
      ceval body s (ORaise e s') ->
      ceval handler (lupd s' exc e) o ->
      ceval (CTry body exc handler) s o.

(** ** Notation *)
Open Scope Z_scope.
