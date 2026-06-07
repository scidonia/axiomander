From iris.program_logic Require Export language.
From iris.heap_lang Require Export lang locations.
From iris.prelude Require Import prelude.
From stdpp Require Import gmap.

(** SnakeletLang — extends heapLang with strings, lists, exceptions.

    Wraps heapLang expressions plus custom constructors.
    Uses [heap_lang.expr], [heap_lang.val], [heap_lang.state] via the
    [heap_lang] module.  [loc] comes from [locations.v].
*)

(* loc is from locations.v — not inside the heap_lang module *)
Definition loc := loc.

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
Definition of_val (v : heap_lang.val) : expr := HeapLang (heap_lang.of_val v).
Definition to_val (e : expr) : option heap_lang.val :=
  match e with
  | HeapLang e' => heap_lang.to_val e'
  | _ => None
  end.

(** State: same as heapLang — [gmap loc val] *)
Definition state : Type := heap_lang.state.

(** Pure steps *)
Inductive pure_step : expr → expr → Prop :=
  | PureHeapLang e1 e2 :
      heap_lang.PureStep e1 e2 →
      pure_step (HeapLang e1) (HeapLang e2)
  | PureStringEq s1 s2 :
      pure_step (SStringEq (of_val s1) (of_val s2))
                (of_val (heap_lang.LitV (heap_lang.LitBool
                  (bool_decide (s1 = s2)))))
  | PureTryReturn v handler :
      pure_step (STry (of_val v) handler) (of_val v).

(** Head steps *)
Inductive head_step : expr → state → expr → state → list expr → Prop :=
  | HeadHeapLang e1 σ e2 σ2 efs :
      heap_lang.head_step e1 σ e2 σ2 efs →
      head_step (HeapLang e1) σ (HeapLang e2) σ2 (map HeapLang efs)
  | HeadListAppend l v σ len :
      σ !! l = Some (heap_lang.LitV (heap_lang.LitInt len)) →
      head_step (SListAppend (of_val l) (of_val v)) σ
                (of_val heap_lang.LitUnit)
                (<[l := heap_lang.LitV (heap_lang.LitInt (len + 1))]>
                 (<[(l + len)%positive := v]> σ)) []
  | HeadRaise e v σ :
      to_val e = Some v →
      head_step (SRaise e) σ (of_val v) σ []
  | HeadTryBody body body' σ efs :
      head_step body σ body' σ efs →
      head_step (STry body handler) σ body' σ efs.
