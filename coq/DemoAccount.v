Require Import ZArith String List Lia.
Require Import Imp Wp Pydantic WpTactics.
Import ListNotations.
Open Scope Z_scope.

(** * Verified Withdraw — Pydantic Contract Demo

    Python:
      class Account:
          balance: int
          overdraft_limit: int

      def withdraw(account, amount):
          assert isinstance(account, Account)
          assert amount >= 0
          assert account.balance + account.overdraft_limit >= amount
          account.balance = account.balance - amount
          result = account.balance
          assert account.balance == result
          return result

    Coq translation of contracts:
      - isinstance → True (type system guarantees)
      - amount >= 0 → precondition
      - balance + overdraft >= amount → sufficient funds
      - balance == result → postcondition
*)

Record Account : Type := {
  account_balance : Z;
  account_overdraft : Z;
}.

Definition init_account_state (bal overdraft amt : Z) : state :=
  let s := store_field "account"%string "overdraft_limit"%string (VZ overdraft) empty_state in
  let s := store_field "account"%string "balance"%string (VZ bal) s in
  upd s "amount"%string (VZ amt).

Definition withdraw_body : com :=
  CSeq
    (CAss "account.balance"%string
          (AMinus (AVar "account.balance"%string) (AVar "amount"%string)))
    (CAss "result"%string (AVar "account.balance"%string)).

Theorem withdraw_correct : forall (balance overdraft amount : Z),
  (* Preconditions (from asserts): *)
  amount >= 0 ->
  balance + overdraft >= amount ->
  (* Postconditions: *)
  wp withdraw_body
     (fun s => s "result"%string = VZ (balance - amount)
            /\ asZ (s "result"%string) >= -overdraft)
     (init_account_state balance overdraft amount).
Proof.
  intros balance overdraft amount Hamt Hfunds.
  wp_prove.
Qed.
