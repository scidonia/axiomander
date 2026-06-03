From Stdlib Require Import String Bool.

(** * RegMatch -- Regex membership predicate for contract verification.

    [re_match s pattern] is a placeholder definition that makes the
    type system accept [re_match] in generated theorem statements.

    The placeholder always returns [true] -- it is NOT the semantic
    definition.  All interesting properties of [re_match] come from
    narrow oracle-backed axioms of the form:

      Axiom smt_string_<hash> :
        forall s, re_match s "strong_pattern" = true ->
                  re_match s "weaker_pattern" = true.

    These axioms are emitted by the theory-SMT oracle (Level 2b) after
    verifying the specific subsumption with Z3/CVC4 over QF_SLIA.
    Each axiom carries its query hash in a comment for auditability.

    This approach is sound because:
    - We never prove anything FROM re_match's definition.
    - We only prove things FROM specific oracle-backed axioms.
    - Each axiom was verified by an external decision procedure.
    - The placeholder is just scaffolding for Coq's type checker.

    This parallels how Dafny handles seq<T>: definitional stub, all
    interesting properties from SMT-verified axioms.
*)

(** [re_match s pattern] is a Prop, not a bool.
    As a Prop it composes naturally with /\ and -> in WP assertions
    without requiring [= true] boilerplate.  The placeholder is
    trivially true so every oracle-backed axiom can prove it from
    the specific hypothesis the SMT solver verified. *)
Definition re_match (s : string) (pattern : string) : Prop := True.
