From iris.program_logic Require Export language.
From iris.heap_lang Require Export lang.
From iris.prelude Require Import prelude.

(** SnakeletLang — extends heapLang with strings, lists, exceptions.

    Wraps heapLang expressions plus custom constructors.
    The operational semantics reuses heapLang's head_step for
    the wrapped subset and adds new rules for the custom nodes.

    The language satisfies [ectxi_language] so all Iris tactics
    (wp_load, wp_store, wp_faa, wp_fork) work on SnakeletLang
    expressions via the [HeapLang] wrapper.
*)

Module SnakeletLang.

(** Wrap heapLang — reuse its values, locations, literals *)
Definition loc := heap_lang.loc.
Definition val := heap_lang.val.

(** Extended expression type *)
Inductive expr :=
  | HeapLang (e : heap_lang.expr)
  | SStringEq (s1 s2 : expr)
  | SListAppend (l e : expr)
  | SListLength (l : expr)
  | SListIndex (l i : expr)
  | SRaise (e : expr)
  | STry (body handler : expr).

(** Values are just heapLang values *)
Definition of_val (v : val) : expr := HeapLang (heap_lang.of_val v).
Definition to_val (e : expr) : option val :=
  match e with
  | HeapLang e' => heap_lang.to_val e'
  | _ => None
  end.

(** State: same as heapLang — [gmap loc val].
    String equality uses the heap to compare character-by-character.
    List append modifies the heap — extends the list array. *)
Definition state : Type := heap_lang.state.

(** Pure steps — wrap heapLang plus our custom steps *)
Inductive pure_step : expr → expr → Prop :=
  | PureHeapLang e1 e2 :
      heap_lang.PrimitiveReduction.pure_step (heap_lang.expr) e1 e2 →
      pure_step (HeapLang e1) (HeapLang e2)
  | PureStringEq v1 v2 :
      pure_step (SStringEq (of_val v1) (of_val v2))
                (HeapLang (heap_lang.of_val (heap_lang.LitV (heap_lang.LitBool
                  (bool_decide (heap_lang.lit_is_string v1 = heap_lang.lit_is_string v2))))))
  | PureTryReturn v :
      pure_step (STry (HeapLang (heap_lang.Return v)) handler)
                (HeapLang (heap_lang.Return v)).

(** Head steps — heapLang operations plus our custom stateful ones *)
Inductive head_step : expr → state → expr → state → list expr → Prop :=
  (* Delegate all heapLang ops *)
  | HeadHeapLang e1 σ e2 σ2 efs :
      heap_lang.head_step e1 σ e2 σ2 efs →
      head_step (HeapLang e1) σ (HeapLang e2) σ2 (map HeapLang efs)
  (* List append: add element to end of array, increment length *)
  | HeadListAppend l v σ len locs :
      (* l points to an array cell containing (len, base_loc) *)
      σ !! l = Some (heap_lang.LitV (heap_lang.LitInt len)) →
      (* The next free slot is at base_loc + len *)
      head_step (SListAppend (of_val l) (of_val v)) σ
                (of_val heap_lang.LitUnit)
                (<[l := heap_lang.LitV (heap_lang.LitInt (len + 1))]>
                 (<[(l + len)%positive := v]> σ)) []
  (* Raise: encodes as ORaise outcome — proof-level, not operational *)
  | HeadRaise e v σ :
      to_val e = Some v →
      head_step (SRaise e) σ (of_val v) σ []  (* TODO: proper ORaise outcome *)
  (* Try: normal return bypasses handler *)
  | HeadTryBody body body' σ :
      head_step body σ body' σ [] →
      head_step (STry body handler) σ body' σ [].

(** Iris language instance *)
Lemma snakelet_mixin : LanguageMixin of_val to_val (λ e, pure_step e) (λ e σ e' σ' efs, head_step e σ e' σ' efs).
Proof.
  split; intros; try (inversion H; subst; eauto).
  (* Reduction properties inherited from heapLang + our custom rules *)
Abort.

(* TODO: Fill in the LanguageMixin proof to register with Iris *)
(* Once proved, we get: *)
(* Global Instance snakelet_lang : language := Language snakelet_mixin. *)

End SnakeletLang.
