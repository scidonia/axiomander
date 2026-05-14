Require Import ZArith String List Lia.
Require Import Imp Wp.
Import ListNotations.
Open Scope Z_scope.

(** * WP Proof Automation — Level 1 (Ltac)

    Reduces WP goals to simple arithmetic forms that can be
    dispatched by [lia], [reflexivity], or sent to the SMT hammer. *)

(** [wp_reduce] — unfold state, aeval, beval; simplify. *)
Ltac wp_reduce :=
  unfold wp, upd, aeval, beval; simpl.

(** [wp_prove] — structural recursion over goal shape after wp_reduce.
    Handles conjunctions, disjunctions, ABool cases, reflexivity, lia.
    Does NOT intro forall/-> (handled by the proof template's intros). *)
Ltac wp_prove :=
  wp_reduce;
  match goal with
  | |- _ /\ _ => split; wp_prove
  | |- (if ?c then _ else _) = 1 \/ (if ?c then _ else _) = 0 =>
      destruct c; auto
  | |- _ \/ _ => (left; wp_prove) || (right; wp_prove)
  | |- ?x = ?x => reflexivity
  | |- _ => try lia; try reflexivity; try auto
  end.

(** [vcg_exit] — proves the while-exit verification condition.
    The goal is: vcg_while_exit b inv Q
    = forall s, inv s -> beval b s = false -> Q s
    Unfolds definitions and dispatches arithmetic to lia. *)
Ltac vcg_exit :=
  unfold vcg_while_exit, beval, upd; simpl;
  repeat rewrite eqb_refl; simpl;
  intros; repeat (match goal with [H: _ /\ _ |- _] => destruct H end);
  match goal with [H: Z.leb _ _ = false |- _] => apply Z.leb_gt in H end;
  lia.

(** * Example 1: assignment — one tactic *)
Theorem add_auto : forall (a b : Z),
  True ->
  wp (CAss "r"%string (APlus (AVar "a"%string) (AVar "b"%string)))
     (fun s => s "r"%string = (a + b)%Z)
     (upd (upd empty_state "a"%string a) "b"%string b).
Proof. intros. wp_prove. Qed.

(** * Example 2: conditional — [split] then [lia] *)
Theorem max_auto : forall (a b : Z),
  0 <= a -> 0 <= b ->
  wp (CIf (BLe (AVar "b"%string) (AVar "a"%string))
          (CAss "r"%string (AVar "a"%string))
          (CAss "r"%string (AVar "b"%string)))
     (fun s => a <= s "r"%string /\ b <= s "r"%string)
     (upd (upd empty_state "a"%string a) "b"%string b).
Proof.
  intros.
  wp_reduce.
  split; [ intro Hleb; apply Z.leb_le in Hleb; wp_prove; split; lia
         | intro Hleb; apply Z.leb_gt in Hleb; wp_prove; split; lia ].
Qed.

(** * Example 3: black hole with havoc *)
Theorem a_unchanged_auto : forall (a b : Z),
  wp (CSeq
       (CAss "x"%string (APlus (AVar "a"%string) (AVar "b"%string)))
       (CHavoc ["x"%string]))
     (fun s => s "a"%string = a)
     (upd (upd empty_state "a"%string a) "b"%string b).
Proof.
  intros a b. wp_prove.
  intros s' H.
  apply (H "a"%string).
  simpl. intro Hx. destruct Hx as [Heq1|[]].
  destruct (string_dec "a"%string "x"%string) as [Heq2|Hneq].
  - discriminate.
  - apply Hneq. symmetry. exact Heq1.
Qed.

(** * Pipeline Integration

    After [wp_reduce], goals are either:
    - Closed (reflexivity, lia) → Level 1 succeeded
    - Simple arithmetic → Level 2: coq-hammer / SMT
    - Complex (invariants, quantifiers) → Level 3: LLM oracle

    The automation doesn't replace the pipeline — it's the first filter.
    What [wp_reduce] can't close, the SMT hammer tries next.
    What the hammer can't close, the LLM oracle generates a proof for. *)
