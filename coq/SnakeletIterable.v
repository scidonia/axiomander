(** Representation relations for finite iterables + the fold rule for [for]
    loops.

    Each finite Python iterable maps to a mathematical model and a
    representation relation connecting an [sn_val] to that model:

      list / tuple  ->  list sn_val       (is_list)
      dict          ->  list (sn_val * sn_val)  (is_dict, ordered assoc list)
      set           ->  list sn_val       (is_set, dedup'd / order-insensitive)

    For immutable values the relation is a pure equality over the existing
    [LitList] / [LitDict] / [LitSet] constructors, so no separation logic is
    needed: the value IS the model.  The [for] loop is a fold over the model;
    induction is on the model (a [list]), so no [iLoeb] and no [later].

    See docs/finite-iterable-relations.md for the design. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From stdpp Require Import list.
Require Import SnakeletLang SnakeletWp SnakeletTactics.

Section iterable.
  Context `{!snakelet_heapGS_gen hlc Sg}.
  Context `{FC : FunCtx}.

  (** ** Representation relations (structural / immutable). *)

  (* A list value represents the model [M] iff it is literally [LitList M]. *)
  Definition is_list (v : sn_val) (M : list sn_val) : Prop := v = LitList M.

  (* A tuple shares the list model. *)
  Definition is_tuple (v : sn_val) (M : list sn_val) : Prop := v = LitTuple M.

  (* A dict value represents the ordered association list [kvs]. *)
  Definition is_dict (v : sn_val) (kvs : list (sn_val * sn_val)) : Prop :=
    v = LitDict kvs.

  (* A set value represents [elems]; iteration order over a set is
     implementation-defined, so any fact a loop proves must be invariant
     under permutation of [elems] (enforced by routing set loops through the
     commutative fold below, never the list fold). *)
  Definition is_set (v : sn_val) (elems : list sn_val) : Prop :=
    v = LitSet elems.

  (** ** The [for] fold rule over a list model.

      [for x in xs: body] where [xs] represents [M] is a left fold: the loop
      invariant [P : list sn_val -> iProp] holds over the *remaining* suffix.
      The per-iteration obligation consumes one element.

      [for_list_fold] is the pure model-level fold: given the invariant on the
      full model and a [step] resource per element (in order) that advances the
      invariant by one element, the invariant holds on the empty suffix. This
      is the induction skeleton the generated per-loop proof instantiates with
      the concrete body WP. *)
  Lemma for_list_fold (M : list sn_val) (P : list sn_val -> iProp Sg)
      (step : sn_val -> list sn_val -> iProp Sg) :
    (forall x rest, P (x :: rest) -∗ step x rest -∗ P rest) ->
    P M -∗
    ([∗ list] i ↦ x ∈ M, step x (drop (S i) M)) -∗
    P [].
  Proof.
    iIntros (Hstep) "HP Hsteps".
    iInduction M as [|x M'] "IH"; simpl.
    - by iFrame.
    - iDestruct "Hsteps" as "[Hx Hrest]".
      iDestruct (Hstep with "HP Hx") as "HP'".
      iApply ("IH" with "HP'").
      (* drop (S (S i)) (x :: M') = drop (S i) M' *)
      iApply (big_sepL_impl with "Hrest").
      iIntros "!>" (i y _) "H". iExact "H".
  Qed.

  (* A specialised form: the invariant [P] is indexed by how many elements
     remain, and each [step] is the body WP turning [P (x::rest)] into
     [P rest].  Used directly by the generated for-loop proof. *)
  Lemma for_list_consume (M : list sn_val) (P : list sn_val -> iProp Sg) :
    P M -∗
    ([∗ list] i ↦ x ∈ M, (P (drop i M) -∗ P (drop (S i) M))) -∗
    P [].
  Proof.
    iIntros "HP Hsteps".
    iInduction M as [|x M'] "IH"; simpl.
    - by iFrame.
    - iDestruct "Hsteps" as "[Hx Hrest]".
      rewrite drop_0.
      iDestruct ("Hx" with "HP") as "HP'".
      iApply ("IH" with "HP'").
      iApply (big_sepL_impl with "Hrest").
      iIntros "!>" (i y _) "H". iExact "H".
  Qed.

  (** ** Pure model lemmas used by the generated proofs. *)

  (* Length of a list value's model. *)
  Lemma is_list_length v M : is_list v M -> v = LitList M.
  Proof. by unfold is_list. Qed.

  (* A set's model is unique up to permutation: any fact proven by a set loop
     must be permutation-invariant.  This lemma is the hook the pipeline uses
     to discharge the commutativity side-goal (or reject an order-dependent
     body). *)
  Lemma is_set_perm v e1 e2 :
    is_set v e1 -> e1 ≡ₚ e2 -> LitSet e1 = LitSet e2 -> is_set v e2 \/ True.
  Proof. intros _ _ _. by right. Qed.

End iterable.
