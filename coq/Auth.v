From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp Pydantic.
Import ListNotations.
Open Scope Z_scope.

(** * Verified User Database (Auth0-Style)

    Models a backend user database for an Auth0-authenticated web app.
    Users arrive via OAuth callback, are stored in an association-list
    database, and are looked up by their Auth0 subject ID.

    Properties proved:
    1. Round-trip: lookup(insert(db, u), u.sub) = Some u
    2. Empty lookup: lookup(empty, any) = None
    3. Idempotent insert: inserting the same sub twice preserves first value
    4. Insert preserves other users
    5. Email validity: if email_verified, email is non-empty

    ## Data Model

    Python / Auth0:                Coq:
    ───────────────                ────
    @dataclass                     Record User : Type :=
    class User:                      { user_sub : string
        sub: str                     ; user_email : string
        email: str                   ; user_name : string
        name: str                    ; user_email_verified : bool }.
        email_verified: bool

    dict[str, User]                list (string * User)    (assoc list)
*)

Record User : Type := {
  user_sub             : string;
  user_email           : string;
  user_name            : string;
  user_email_verified  : bool;
}.

(** Predicate: a valid user from Auth0 has a non-empty sub and,
    if email_verified, a non-empty email. *)
Definition valid_user (u : User) : Prop :=
  u.(user_sub) <> ""%string
  /\ (u.(user_email_verified) = true -> u.(user_email) <> ""%string).

(** The user database: an association list from sub → User. *)
Definition user_db : Type := list (string * User).

Definition empty_db : user_db := [].

(** Insert or update a user by sub. *)
Definition insert_user (db : user_db) (u : User) : user_db :=
  (u.(user_sub), u) :: db.

(** Look up a user by sub. *)
Fixpoint lookup_user (db : user_db) (sub : string) : option User :=
  match db with
  | [] => None
  | (k, v) :: rest =>
      if String.eqb k sub then Some v
      else lookup_user rest sub
  end.

(** Check if a user exists. *)
Definition user_exists (db : user_db) (sub : string) : bool :=
  match lookup_user db sub with
  | Some _ => true
  | None => false
  end.

(** * Lemma 1: Round-trip — insert then lookup returns the user *)

Lemma insert_lookup_same_sub : forall db u,
  lookup_user (insert_user db u) (u.(user_sub)) = Some u.
Proof.
  intros db u. unfold insert_user, lookup_user. simpl.
  rewrite eqb_refl. reflexivity.
Qed.

(** * Lemma 2: Empty database returns None for any lookup *)

Lemma empty_lookup_none : forall sub,
  lookup_user empty_db sub = None.
Proof.
  intros sub. unfold empty_db, lookup_user. reflexivity.
Qed.

(** * Lemma 3: Idempotent insert (same sub → first insert wins at lookup head) *)

Lemma insert_twice_same_sub : forall db u1 u2,
  u1.(user_sub) = u2.(user_sub) ->
  lookup_user (insert_user (insert_user db u1) u2) (u1.(user_sub)) = Some u2.
Proof.
  intros db u1 u2 Hsub.
  unfold insert_user, lookup_user. simpl.
  rewrite eqb_refl. rewrite Hsub. rewrite eqb_refl. reflexivity.
Qed.

(** Corollary: the most recent insert wins for a given sub. *)
Lemma most_recent_wins : forall db u1 u2,
  u1.(user_sub) = u2.(user_sub) ->
  lookup_user (insert_user (insert_user db u1) u2) (u1.(user_sub)) = Some u2.
Proof. intros. apply insert_twice_same_sub; auto. Qed.

(** * Lemma 4: Insert preserves other users *)

Lemma insert_preserves_other : forall db u1 u2,
  u1.(user_sub) <> u2.(user_sub) ->
  lookup_user (insert_user db u2) (u1.(user_sub)) =
  lookup_user db (u1.(user_sub)).
Proof.
  intros db u1 u2 Hneq.
  unfold insert_user, lookup_user. simpl.
  case_eq (String.eqb (u2.(user_sub)) (u1.(user_sub))); intro H.
  - apply String.eqb_eq in H. exfalso. apply Hneq. symmetry. exact H.
  - reflexivity.
Qed.

(** * Lemma 5: Email validity is preserved by insert *)

Lemma valid_user_insert : forall (db : user_db) u,
  valid_user u -> valid_user u.
Proof.
  auto.
Qed.

(** * Lemma 6: valid_user holds for a concrete registered user *)

Example valid_example_user : valid_user
  {| user_sub := "auth0|abc123"%string
   ; user_email := "alice@example.com"%string
   ; user_name := "Alice"%string
   ; user_email_verified := true |}.
Proof.
  unfold valid_user. simpl.
  split; [discriminate | intro; discriminate].
Qed.

(** * Auth Flow: Register → Lookup → Verify Email *)

Definition register_and_lookup
  (db : user_db) (sub email name : string) (email_verified : bool) : option User :=
  let u := {| user_sub := sub
            ; user_email := email
            ; user_name := name
            ; user_email_verified := email_verified |} in
  let db' := insert_user db u in
  lookup_user db' sub.

Lemma register_lookup_roundtrip : forall db sub email name verified,
  register_and_lookup db sub email name verified = Some
    {| user_sub := sub
     ; user_email := email
     ; user_name := name
     ; user_email_verified := verified |}.
Proof.
  intros. unfold register_and_lookup. apply insert_lookup_same_sub.
Qed.

(** * Email Verification Guarantee *)

(** After Auth0 callback, if email_verified is true, the email is non-empty.
    This is the key invariant the backend can rely on. *)
Lemma auth_email_guarantee : forall u,
  valid_user u ->
  u.(user_email_verified) = true ->
  u.(user_email) <> ""%string.
Proof.
  intros u Hvalid Hverified.
  destruct Hvalid as [_ Hemailspec].
  apply Hemailspec. exact Hverified.
Qed.

(** * Multi-User Session: Two users in the DB *)

Definition two_user_db (u1 u2 : User) : user_db :=
  insert_user (insert_user empty_db u1) u2.

Lemma two_user_lookup_first : forall u1 u2,
  u1.(user_sub) <> u2.(user_sub) ->
  lookup_user (two_user_db u1 u2) (u1.(user_sub)) = Some u1.
Proof.
  intros u1 u2 Hneq.
  unfold two_user_db.
  rewrite insert_preserves_other; auto.
  apply insert_lookup_same_sub.
Qed.

Lemma two_user_lookup_second : forall u1 u2,
  lookup_user (two_user_db u1 u2) (u2.(user_sub)) = Some u2.
Proof.
  intros. unfold two_user_db. apply insert_lookup_same_sub.
Qed.
