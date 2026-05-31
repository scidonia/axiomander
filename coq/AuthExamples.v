From Stdlib Require Import ZArith String List micromega.Lia.
Require Import Imp Wp Pydantic Auth.
Import ListNotations.

(** * Auth0-Style Backend: Verified Properties

    Using the User model and user_db from Auth.v, we prove
    key backend invariants for a web application.

    These are the guarantees a verified backend provides. *)

(** ** 1. Round-trip: register then lookup *)
Theorem rt_register_lookup : forall db sub email name verified,
  lookup_user (insert_user db {|
    user_sub := sub;
    user_email := email;
    user_name := name;
    user_email_verified := verified |})
    sub
  = Some {| user_sub := sub
          ; user_email := email
          ; user_name := name
          ; user_email_verified := verified |}.
Proof. intros. apply insert_lookup_same_sub. Qed.

(** ** 2. Session isolation: user A cannot read user B *)
Theorem session_isolation : forall uA uB,
  valid_user uA -> valid_user uB ->
  uA.(user_sub) <> uB.(user_sub) ->
  lookup_user (insert_user empty_db uB) (uA.(user_sub)) = None.
Proof.
  intros uA uB HA HB Hneq.
  unfold insert_user, lookup_user. simpl.
  case_eq (String.eqb (uB.(user_sub)) (uA.(user_sub))); intro H.
  - apply String.eqb_eq in H. exfalso. apply Hneq. symmetry. exact H.
  - reflexivity.
Qed.

(** ** 3. Email trust: Auth0 verified → email is non-empty *)
Theorem email_trust : forall u,
  valid_user u -> u.(user_email_verified) = true ->
  u.(user_email) <> ""%string.
Proof. intros. apply auth_email_guarantee; assumption. Qed.

(** ** 4. Safe registration: existing users untouched *)
Theorem registration_safe : forall db u_old u_new,
  u_old.(user_sub) <> u_new.(user_sub) ->
  lookup_user (insert_user db u_new) (u_old.(user_sub)) =
  lookup_user db (u_old.(user_sub)).
Proof. intros. apply insert_preserves_other. assumption. Qed.

(** ** 5. Empty DB: no user is found *)
Theorem empty_db_safe : forall sub,
  lookup_user empty_db sub = None.
Proof. intros. apply empty_lookup_none. Qed.

(** ** 6. Concrete example: a valid Auth0 user *)
Fact alice_is_valid : valid_user
  {| user_sub := "auth0|abc123"%string
   ; user_email := "alice@example.com"%string
   ; user_name := "Alice"%string
   ; user_email_verified := true |}.
Proof. split; compute; discriminate. Qed.
