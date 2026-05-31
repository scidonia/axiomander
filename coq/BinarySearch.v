From Stdlib Require Import ZArith List micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(** * Verified Binary Search — Specification + Simple Cases

    Full correctness (~200 lines) requires well-founded induction
    and is Level 3 (LLM oracle) territory. We demonstrate:
      - 4 simple cases proven by automation (Level 1)
      - The full invariant stated, left for LLM oracle *)

Definition nthZ (i : Z) (arr : list Z) : Z :=
  nth (Z.to_nat i) arr 0.

Definition sorted (arr : list Z) : Prop :=
  forall i j, 0 <= i <= j -> j < Z.of_nat (length arr) ->
  nthZ i arr <= nthZ j arr.

(** Fuel-based binary search (structurally terminating) *)
Fixpoint bin_search (arr : list Z) (target lo hi : Z) (fuel : nat) : Z :=
  match fuel with
  | O => -1
  | S fuel' =>
      if Z.leb lo hi then
        let mid := lo + (hi - lo) / 2 in
        match nth_error arr (Z.to_nat mid) with
        | Some val =>
            if Z.eqb val target then mid
            else if Z.ltb val target
                 then bin_search arr target (mid + 1) hi fuel'
                 else bin_search arr target lo (mid - 1) fuel'
        | None => -1
        end
      else -1
  end.

Definition binary_search (arr : list Z) (target : Z) : Z :=
  bin_search arr target 0 (Z.of_nat (length arr) - 1) (length arr + 1).

(** * Level 1 proofs: automation clears these *)

Theorem empty_array : forall target,
  binary_search [] target = -1.
Proof. intros. unfold binary_search. reflexivity. Qed.

Theorem singleton_found : forall x,
  binary_search [x] x = 0.
Proof. intros. unfold binary_search. simpl. rewrite Z.eqb_refl. reflexivity. Qed.

Theorem singleton_miss : forall x y,
  x <> y ->
  binary_search [x] y = -1.
Proof.
  intros x y Hneq. unfold binary_search. simpl.
  case_eq (Z.eqb x y); intro Heq.
  - apply Z.eqb_eq in Heq. exfalso. apply Hneq. exact Heq.
  - destruct (Z.ltb x y); reflexivity.
Qed.

Theorem two_elems : forall a b,
  a < b ->
  binary_search [a; b] a = 0 /\ binary_search [a; b] b = 1.
Proof.
  intros a b Hlt. unfold binary_search. simpl.
  split.
  - rewrite Z.eqb_refl. reflexivity.
  - assert (Hneq : Z.eqb a b = false) by (apply Z.eqb_neq; lia).
    rewrite Hneq.
    assert (Hltb : Z.ltb a b = true) by (apply Z.ltb_lt; exact Hlt).
    rewrite Hltb. simpl.
    rewrite Z.eqb_refl. reflexivity.
Qed.

(* ─────────────────────────────────────────────────────────────
   Full correctness (Level 3 — LLM oracle target)

   The invariant: for sorted arr, bin_search finds target
   iff it's present in [lo..hi]. Proof: well-founded induction
   on (hi - lo), using sorted to partition at mid.
   ───────────────────────────────────────────────────────────── *)

Lemma bin_search_invariant : forall arr target lo hi fuel,
  sorted arr ->
  0 <= lo -> hi < Z.of_nat (length arr) ->
  (bin_search arr target lo hi fuel <> -1 ->
   nthZ (bin_search arr target lo hi fuel) arr = target
   /\ lo <= bin_search arr target lo hi fuel <= hi)
  /\
  (bin_search arr target lo hi fuel = -1 ->
   forall i, lo <= i <= hi -> nthZ i arr <> target).
Proof.
  (* Target for LLM oracle — Level 3 pipeline.
     Proof sketch: induction on (Z.to_nat (hi - lo)).
     At each step, compute mid = lo + (hi-lo)/2.
     If arr[mid] = target: found, return mid.
     If arr[mid] < target: search right half [mid+1, hi].
     If arr[mid] > target: search left half [lo, mid-1].
     All three cases use sorted to justify the partition. *)
Admitted.

Lemma len_minus_one_lt_len : forall n, Z.of_nat n - 1 < Z.of_nat n.
Proof.
  induction n.
  - compute. auto.
  - rewrite Nat2Z.inj_succ. rewrite Z.sub_1_r, Z.pred_succ.
    apply Z.lt_succ_diag_r.
Qed.

Theorem binary_search_correct : forall arr target,
  sorted arr ->
  (binary_search arr target <> -1 ->
   nthZ (binary_search arr target) arr = target
   /\ 0 <= binary_search arr target < Z.of_nat (length arr))
  /\
  (binary_search arr target = -1 ->
   forall i, 0 <= i < Z.of_nat (length arr) ->
   nthZ i arr <> target).
Proof.
  intros arr target Hsorted.
  pose proof (bin_search_invariant arr target 0 (Z.of_nat (length arr) - 1)
                                     (length arr + 1) Hsorted) as Hinv.
  assert (Hlo : 0 <= 0) by apply Z.le_refl.
  assert (Hhi : Z.of_nat (length arr) - 1 < Z.of_nat (length arr))
    by apply len_minus_one_lt_len.
  specialize (Hinv Hlo Hhi).
  destruct Hinv as [Hfound Hnotfound].
  unfold binary_search. split.
  - intros Hres. apply Hfound in Hres. destruct Hres as [Hnth [Hlo' Hhi']].
    split; [exact Hnth | split; [exact Hlo' | lia]].
  - intros Hres i Hi.
    apply (Hnotfound Hres i). split; [exact (proj1 Hi) | lia].
Qed.
