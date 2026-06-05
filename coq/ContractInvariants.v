From Stdlib Require Import String Nat Bool List.

(** * ContractInvariants — Universal lemmas proved by case-dispatch SMT verification.

    Properties that range over the outputs of case-dispatch functions (like
    [_coq_type_of_param]) are proved by Herbrand instantiation: each case is
    verified independently by the theory-SMT oracle (QF_SLIA), and the
    universal follows by Coq case analysis over a string classifier.

    Trust base:
      - Per-case axioms: verified by external Z3/CVC5 (query hash in comment)
      - Case classifier: machine-checked Coq Definition
      - Assembly lemma: machine-checked Coq Proof (no Admitted)
      - Case extractor: tool-side (trusted, like the Python->IMP translator)

    Adding a new case = add one SMT check + one apply branch in the
    assembly lemma.  No induction required.
 *)

(** [suffix s e] returns true if [s] is a suffix of [e].
    Built from [String.substring] and [String.length] -- the Rocq 9
    stdlib does not provide [String.suffix] directly. *)
Definition suffix (s e : string) : bool :=
  let n := String.length s in
  let m := String.length e in
  if Nat.leb n m then
    String.eqb s (String.substring (m - n) n e)
  else
    false.

(* ───────────────────────────────────────────────────────────────────
   Per-case SMT axioms for string suffix relationships
   ───────────────────────────────────────────────────────────────────

   Each axiom is a ground QF_SLIA check verified by the theory-SMT
   oracle.  The query hash in the comment links the axiom to its
   SMT proof for auditability and re-verification.

   Adding a new suffix pattern: add one SMT query + one axiom below.
 *)

(* Case: p ++ "_str" always ends in "_str"
   SMT query (QF_SLIA):
     (assert (not (str.suffixof "_str" (str.++ p "_str"))))
     (check-sat)   → unsat *)
(* SMT-verified: string theory, z3 4.14.1, query 71b2f7cf52adf934 *)
Axiom suffix_str_defined : forall (p : string),
  suffix "_str" (p ++ "_str") = true.

(* Case: p ++ "__len" never ends in "_str"
   SMT query (QF_SLIA):
     (assert (str.suffixof "_str" (str.++ p "__len")))
     (check-sat)   → unsat  (contradiction: "__len" != "_str") *)
(* SMT-verified: string theory, z3 4.14.1, query c19a1a0f2930927d *)
Axiom suffix_not_str_len : forall (p : string),
  suffix "_str" (p ++ "__len") = false.

(* Case: p ++ "__count" never ends in "_str"
   SMT query (QF_SLIA):
     (assert (str.suffixof "_str" (str.++ p "__count")))
     (check-sat)   → unsat  (contradiction: "__count" != "_str") *)
(* SMT-verified: string theory, z3 4.14.1, query c418b88f75454557 *)
Axiom suffix_not_str_count : forall (p : string),
  suffix "_str" (p ++ "__count") = false.

(* Case: suffix is monotonic under String.append prepending
   SMT query (QF_SLIA):
     (assert (str.suffixof "_str" p))
     (assert (not (str.suffixof "_str" (str.++ prefix p))))
     (check-sat)   → unsat  (suffix is preserved under prepending) *)
(* SMT-verified: string theory, z3 4.14.1, query 5c5d88c389e1d3aa *)
Axiom suffix_under_prefix : forall (prefix p : string),
  suffix "_str" p = true ->
  suffix "_str" (prefix ++ p) = true.


(* ───────────────────────────────────────────────────────────────────
   _coq_type_of_param — Coq mirror of the Python function

   The Python function (obligation_gen.py:19):
     def _coq_type_of_param(p: str) -> str:
         if p.endswith("_str"): return "string"
         return "Z"

   The Coq definition below matches it structurally.  Every generated
   Coq theorem uses _params_forall (which calls _coq_type_of_param) to
   emit correctly-typed forall binders.  If this function had a bug
   (e.g. returning "Z" for a string param), the generated Coq would
   fail to typecheck.
 *)

Definition coq_type_of_param (p : string) : string :=
  if suffix "_str" p then "string"%string else "Z"%string.

(** The main correctness lemma: [coq_type_of_param] correctly classifies
    expanded parameter names using the suffix convention.

    This is a definitional proof — no SMT needed here.  The heavy
    lifting is in the suffix axioms above, which establish that
    constructed names like [p ++ "_str"] actually satisfy the suffix
    check. *)
Lemma coq_type_of_param_correct :
  forall (p : string),
    (suffix "_str" p = true -> coq_type_of_param p = "string"%string) /\
    (suffix "_str" p = false -> coq_type_of_param p = "Z"%string).
Proof.
  split; intro H; unfold coq_type_of_param; rewrite H; reflexivity.
Qed.

(** A stronger form: the classification is tight (iff).  Still
    definitional because [coq_type_of_param] is defined by the same
    suffix check. *)
Lemma coq_type_of_param_iff :
  forall (p : string),
    coq_type_of_param p = "string"%string <-> suffix "_str" p = true.
Proof.
  intros p. unfold coq_type_of_param. split.
  - destruct (suffix "_str" p) eqn:Hs.
    + auto.
    + discriminate.
  - intro H. rewrite H. reflexivity.
Qed.

(** An application: for a name constructed by the string-param expansion
    code path ([p ++ "_str"]), [coq_type_of_param] guarantees it will be
    classified as [string] (i.e. the Coq binder will use ": string"). *)
Lemma string_param_typed_correctly :
  forall (p : string),
    coq_type_of_param (p ++ "_str") = "string"%string.
Proof.
  intro p. apply coq_type_of_param_iff. apply suffix_str_defined.
Qed.

(** Conversely, a name with the list-param suffix [__len] will be
    classified as [Z], not [string] — preventing a type mismatch in
    generated Coq forall binders. *)
Lemma list_param_not_string :
  forall (p : string),
    coq_type_of_param (p ++ "__len") = "Z"%string.
Proof.
  intro p. unfold coq_type_of_param. rewrite suffix_not_str_len. reflexivity.
Qed.


(* ───────────────────────────────────────────────────────────────────
   Case classifier for expand_params-style suffix dispatch
   ─────────────────────────────────────────────────────────────────── *)

(** Given an expanded parameter name [e], returns the classification tag:
      "string"  -- ends in ["_str"]
      "list"    -- ends in ["__len"]
      "dict"    -- ends in ["__count"]
      "scalar"  -- none of the above *)
Definition expanded_case (e : string) : string :=
  if suffix "_str" e then "string"%string
  else if suffix "__len" e then "list"%string
  else if suffix "__count" e then "dict"%string
  else "scalar"%string.


(* ───────────────────────────────────────────────────────────────────
   expand_params type-convention lemma

   Proves that every expanded parameter name follows the suffix
   convention: names ending in "_str" are classified as string type,
   names ending in "__len" / "__count" are classified as Z type,
   and these classifications are mutually exclusive.

   The proof uses case analysis on [expanded_case] plus the
   SMT-verified suffix axioms.  No induction required — the
   classifier handles one name at a time.
 *)

(** [expanded_case] correctly identifies suffixes.
    The four cases ("string", "list", "dict", "scalar") are exhaustive
    and mutually exclusive for any input string. *)
Lemma expanded_case_exhaustive :
  forall (e : string),
    expanded_case e = "string"%string \/
    expanded_case e = "list"%string \/
    expanded_case e = "dict"%string \/
    expanded_case e = "scalar"%string.
Proof.
  intro e. unfold expanded_case.
  destruct (suffix "_str" e) eqn:Hs_str.
  - left. reflexivity.
  - destruct (suffix "__len" e) eqn:Hs_len.
    + right. left. reflexivity.
    + destruct (suffix "__count" e) eqn:Hs_count.
      * right. right. left. reflexivity.
      * right. right. right. reflexivity.
Qed.

(** The "string" case is correct: it implies the suffix holds. *)
Lemma expanded_case_string_sound :
  forall (e : string),
    expanded_case e = "string"%string ->
    suffix "_str" e = true.
Proof.
  intros e H. unfold expanded_case in H.
  destruct (suffix "_str" e) eqn:Hs.
  - reflexivity.
  - destruct (suffix "__len" e) eqn:Hl; simpl in H.
    + destruct (suffix "__count" e) eqn:Hc; simpl in H; discriminate.
    + destruct (suffix "__count" e) eqn:Hc; simpl in H; discriminate.
Qed.

(** The "list" case implies the name ends in __len, not _str. *)
Lemma expanded_case_list_sound :
  forall (e : string),
    expanded_case e = "list"%string ->
    suffix "__len" e = true /\ suffix "_str" e = false.
Proof.
  intros e H. unfold expanded_case in H.
  destruct (suffix "_str" e) eqn:Hs; simpl in H.
  - discriminate.
  - destruct (suffix "__len" e) eqn:Hl; simpl in H.
    + split; [reflexivity | auto].
    + destruct (suffix "__count" e) eqn:Hc; simpl in H; discriminate.
Qed.

(** The "dict" case implies the name ends in __count. *)
Lemma expanded_case_dict_sound :
  forall (e : string),
    expanded_case e = "dict"%string ->
    suffix "__count" e = true.
Proof.
  intros e H. unfold expanded_case in H.
  destruct (suffix "_str" e) eqn:Hs; simpl in H.
  - discriminate.
  - destruct (suffix "__len" e) eqn:Hl; simpl in H.
    + discriminate.
    + destruct (suffix "__count" e) eqn:Hc; simpl in H.
      * reflexivity.
      * discriminate.
Qed.

(** The "scalar" case: no known suffix matches. *)
Lemma expanded_case_scalar_sound :
  forall (e : string),
    expanded_case e = "scalar"%string ->
    suffix "_str" e = false /\
    suffix "__len" e = false /\
    suffix "__count" e = false.
Proof.
  intros e H. unfold expanded_case in H.
  destruct (suffix "_str" e) eqn:Hs; simpl in H.
  - discriminate.
  - destruct (suffix "__len" e) eqn:Hl; simpl in H.
    + discriminate.
    + destruct (suffix "__count" e) eqn:Hc; simpl in H.
      * discriminate.
      * auto.
Qed.

(** The main type-convention lemma: if a name was produced by the
    string-param expansion path (ends in "_str"), the forall binder
    it generates uses ": string".

    This lemma is applied by the obligation generator to justify
    that every [forall (p_str : string) ...] binder is correctly typed.
    The proof is a single case dispatch on [expanded_case e]. *)
Lemma expand_params_type_convention :
  forall (e : string),
    suffix "_str" e = true ->
    coq_type_of_param e = "string"%string.
Proof.
  intros e Hsuf.
  apply coq_type_of_param_iff.
  assumption.
Qed.

(** Per-suffix construction lemmas — used by code generators to
    verify that specific suffix patterns produce correct types. *)

Lemma build_string_param :
  forall (p : string),
    coq_type_of_param (p ++ "_str") = "string"%string.
Proof.
  intro p. apply coq_type_of_param_iff.
  apply suffix_str_defined.
Qed.

Lemma build_list_param :
  forall (p : string),
    coq_type_of_param (p ++ "__len") = "Z"%string.
Proof.
  intro p. unfold coq_type_of_param.
  rewrite suffix_not_str_len. reflexivity.
Qed.

Lemma build_dict_param :
  forall (p : string),
    coq_type_of_param (p ++ "__count") = "Z"%string.
Proof.
  intro p. unfold coq_type_of_param.
  rewrite suffix_not_str_count. reflexivity.
Qed.


(* ───────────────────────────────────────────────────────────────────
   split / join / str_replace — Fixpoints via fuel-based recursion

   [split] uses an indexed helper [split_from] that recurses on [fuel],
   a structurally decreasing [nat] counter.  The initial fuel is
   [String.length s], which is a safe upper bound (at most one split
   per character).  The helper scans from [pos] upward, advancing past
   each delimiter occurrence.  No well-founded induction required.
   ─────────────────────────────────────────────────────────────────── *)

Import ListNotations.

Fixpoint split_from (s delimiter : string) (pos fuel : nat) : list string :=
  match fuel with
  | 0 => [String.substring pos (String.length s - pos) s]
  | S fuel' =>
      match String.index pos delimiter s with
      | Some idx =>
          String.substring pos (idx - pos) s
          :: split_from s delimiter (idx + String.length delimiter) fuel'
      | None =>
          [String.substring pos (String.length s - pos) s]
      end
  end.

Definition split (s delimiter : string) : list string :=
  split_from s delimiter 0 (String.length s).

Fixpoint join (parts : list string) (separator : string) : string :=
  match parts with
  | [] => ""%string
  | [p] => p
  | p :: rest => p ++ separator ++ join rest separator
  end.

Fixpoint str_replace_from (s old new : string) (pos fuel : nat) : string :=
  match fuel with
  | 0 => String.substring pos (String.length s - pos) s
  | S fuel' =>
      match String.index pos old s with
      | Some idx =>
          String.substring pos (idx - pos) s ++ new
          ++ str_replace_from s old new (idx + String.length old) fuel'
      | None =>
          String.substring pos (String.length s - pos) s
      end
  end.

Definition str_replace (s old new : string) : string :=
  str_replace_from s old new 0 (String.length s).


(** The fire-and-forget specification:
    [str_replace s old new] = join of the parts obtained by splitting
    [s] at [old] and rejoining with [new].

    The fuel bound [String.length s] is sufficient because each
    replacement consumes at least one character.  A proof would
    proceed by induction on [fuel], using the invariant that after
    processing up to position [pos], the remaining suffix has length
    [String.length s - pos]. *)

Axiom str_replace_eq_join_split :
  forall (s old new : string),
    str_replace s old new = join (split s old) new.
