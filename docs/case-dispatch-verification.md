# Case-Dispatch Verification via SMT Ground Checks + Coq Assembly

## Problem

Many functions in Axiomander's pipeline are **type-directed case dispatchers**: they
branch on the type or classification of an input, and in each branch produce output
that is structurally determined by that branch.  `_expand_params` is the canonical
example:

```python
def _expand_params(tree, params, func_node=None):
    for p in params:
        if p in string_params:
            expanded.append(p + "__len")   # Z binder
            expanded.append(p + "_str")    # string binder
            parts.append(f"({p}__len : Z)")
            parts.append(f"({p}_str : string)")
        elif p in list_params:
            expanded.append(p + "__len")
            parts.append(f"({p}__len : Z)")
        elif p in dict_params:
            expanded.append(p + "__count")
            parts.append(f"({p}__count : Z)")
        ...
```

The **type-convention property** is:

> For every name `e` in `expanded`, if `e` ends in `"_str"` then `params_coq`
> contains the binder `"(e : string)"`.

This property is what distinguishes correct from incorrect output.  A bug in this
function produced `(raw : Z)` instead of `(raw__len : Z) (raw_str : string)` for a
`str` parameter — violating the type convention and causing a downstream free-variable
error in generated Coq.

The property is **relational** (connects two output variables: `expanded` and
`params_coq`) and **universal** (`forall e in expanded, ...`).  Neither pure SMT
(needs quantifiers) nor pure IMP verification (strings are opaque) can handle it
directly.  Standard induction over `params` in Coq works but is verbose and must be
written by hand per function.

---

## Key Insight: Herbrand Instantiation over Case Structure

The universal quantifier `forall e in expanded` ranges over a **finite, known** set
determined by a finite case analysis in the source.  Each case of the dispatcher
independently constructs a specific suffix and a specific binder type.  The universal
follows from verifying each case independently.

This is **Herbrand instantiation**: instead of proving a universal by induction, we
enumerate the Herbrand universe (the set of cases) and verify the property
ground-instance by ground-instance.  The universal is then assembled by case analysis
over the input classifier — a Coq proof that is structurally forced by the case
partition, not written by hand.

The soundness argument: if

1. In the `string_params` case, `e = p ++ "_str"` and `params_coq` contains
   `"(" ++ p ++ "_str : string)"` — **verified by SMT (QF_SLIA)**
2. In every other case, `suffix "_str" e` is false — **verified by SMT**

then the universal `forall e, suffix "_str" e -> contains params_coq "(e : string)"`
holds by exhaustion of cases.

Each ground check is **quantifier-free** and in **QF_SLIA** (string + linear integer
arithmetic) — decidable by Z3 or CVC5.

---

## Architecture

Three components work together:

```
Source function (Python)
        |
        v
IMP IR (CIf/CSeq/CAss tree)
        |
        v
[1] case_extractor
        |  Produces list of CaseBranch
        v
[2] case_verifier (TheoryDispatcher)
        |  One SMT query per case per property
        |  Produces AxiomRecord per case
        v
[3] ContractInvariants.v
        |  Coq proof assembles universal
        |  by destruct on input classifier
        v
Proved lemma (forall e, ...)
```

### Component 1: Case Extractor

Walks the IMP IR and produces a list of `CaseBranch` pairs:

```python
@dataclass
class CaseBranch:
    path_conditions: list[ImpBExp]  # conjunction of conditions to reach this branch
    assignments: list[ImpCom]       # linear sequence of CAss/CListAppend/etc.
```

Algorithm:

```
extract_cases(com, conditions=[]) -> list[CaseBranch]:
    if com is CIf(b, then_branch, else_branch):
        then_cases = extract_cases(then_branch, conditions + [b])
        else_cases = extract_cases(else_branch, conditions + [NOT b])
        return then_cases + else_cases
    if com is CSeq:
        # linear -- collect all assignments
        return [CaseBranch(conditions, collect_assignments(com))]
    return [CaseBranch(conditions, [com])]
```

The extractor only applies when the body is a **decision tree**:
- No `CWhile`/`CFor` inside the branching structure
- `CIf` conditions partition the input space (checked by SMT: no two conditions are
  simultaneously satisfiable)

Functions that satisfy this: `_expand_params`, `_py_type_to_coq`,
`_coq_type_of_param`, `_annotation_to_guard`, `_is_list_param`, `_is_dict_param`,
`_is_string_param`, `visit_Call` in the contract linter, `lower_expr`/`lower_stmt`
in `py_to_imp.py`.

Functions that do not satisfy this: anything with a `while p in params:` loop (needs
induction), recursive functions, functions whose branching depends on the depth of an
unbounded data structure.

### Component 2: Case Verifier

For each `CaseBranch`, evaluates the output expressions symbolically and constructs
a QF_SLIA SMT query for the property.

For the type-convention property of `_expand_params`, string param case:

```python
# Path condition: p in string_params (encoded as BDictLen "string_params" p > 0)
# Assignments:
#   CListAppend "expanded" (AStrConcat (AVar "p") (AString "__len"))
#   CListAppend "expanded" (AStrConcat (AVar "p") (AString "_str"))
#   CListAppend "parts"    (AStrConcat (AString "(") ...)
#   CListAppend "parts"    (AStrConcat (AString "(") (AStrConcat p "_str : string)"))

# Property for this case:
#   e = p ++ "_str"
#   suffix "_str" e = true           -- trivially: "_str" suffixes p ++ "_str"
#   params_coq contains "(e : string)"
#                      = "(" ++ p ++ "_str : string)"
#                      -- contained in parts by construction

# SMT query (QF_SLIA, no quantifiers):
(set-logic QF_SLIA)
(declare-const p String)
(declare-const params_coq String)
(assert (= params_coq (str.++ "(" (str.++ p "_str : string)"))))
; Verify: (p ++ "_str") ends in "_str"
(assert (not (str.suffixof "_str" (str.++ p "_str"))))
(check-sat)
; Expected: unsat (the suffix always holds)
```

For the list param case:

```smt2
; e = p ++ "__len"
; Does it end in "_str"? No.
(assert (str.suffixof "_str" (str.++ p "__len")))
(check-sat)
; Expected: unsat (len suffix never ends in _str)
```

Each case produces an `AxiomRecord` with a query hash for auditability.

### Component 3: ContractInvariants.v

The Coq side receives the per-case axioms and assembles the universal.

The key is a **string classifier** — a Coq function that maps an expanded name back
to the case that produced it:

```coq
Definition expanded_case (e : string) : option string :=
  if String.suffix "_str" e then Some "string"
  else if String.suffix "__len" e then Some "list"
  else if String.suffix "__count" e then Some "dict"
  else Some "scalar".
```

The universal lemma:

```coq
(* Per-case axioms from SMT oracle *)
Axiom type_conv_string_case :
  forall (p : string),
    String.index 0 ("(" ++ p ++ "_str : string)") (build_params_coq_string p) <> None.
(* SMT: QF_SLIA, query a3f9b2c1, z3 4.17.0 *)

Axiom type_conv_not_str_len_case :
  forall (p : string),
    String.suffix "_str" (p ++ "__len") = false.
(* SMT: QF_SLIA, query b7f2c9d4, z3 4.17.0 *)

(* ... one axiom per case ... *)

(* The universal, proved by Coq case analysis over expanded_case *)
Lemma type_convention :
  forall (e params_coq : string),
    In e expanded ->
    String.suffix "_str" e = true ->
    String.index 0 ("(" ++ e ++ " : string)") params_coq <> None.
Proof.
  intros e params_coq He Hsuf.
  destruct (expanded_case e) as [case|] eqn:Hcase.
  - destruct case.
    + (* "string": e = p ++ "_str" for some p *)
      apply type_conv_string_case.
    + (* "list": e = p ++ "__len", suffix is false -- contradiction *)
      exfalso.
      rewrite (type_conv_not_str_len_case _) in Hsuf.
      discriminate.
    + (* "dict": e = p ++ "__count", similar *)
      ...
    + (* "scalar": e = p, suffix false unless p itself ends in _str *)
      ...
  - contradiction.
Qed.
```

The Coq proof is **structurally forced**: each branch either applies an SMT-backed
axiom or derives a contradiction from suffix incompatibility.  No induction,
no creativity required.  Adding a new case = add one SMT check + one `apply` branch.

---

## Generalisation: When This Works

The pattern applies whenever a function satisfies:

| Criterion | Why needed |
|---|---|
| Finite case analysis in IMP body | Gives a finite Herbrand universe |
| Each branch is linear (no loops) | Makes output symbolic evaluation tractable |
| Branches are mutually exclusive | Ensures case analysis is exhaustive |
| Property is relational between outputs | SMT string theory handles `str.++`, `str.contains`, `str.suffixof` |
| No cross-case interaction | Each case is independent |

**Fits the pattern:**

- `_expand_params` -- type-directed flattening of params
- `_py_type_to_coq` -- Python annotation → Coq type string
- `_coq_type_of_param` -- expanded name suffix → Coq type
- `_annotation_to_guard` -- annotation → type guard Coq expression
- `_is_list_param`/`_is_dict_param`/`_is_string_param` -- classification predicates
- `lower_expr` in `py_to_imp.py` -- PyExpr → ImpAExp dispatch
- `lower_stmt` in `py_to_imp.py` -- PyStmt → ImpCom dispatch
- `visit_Call` in `contract_linter.py` -- AST Call → contract IR dispatch

**Does not fit:**

- `flat_fields` -- recursive tree traversal, needs induction
- `_collect_ccalls` -- recursive tree walk, needs induction
- `get_transitive_callers` -- while loop with growing set, needs loop invariant
- `parse_axiomander_docstring` -- string parsing loop, needs induction

---

## Trust Model

The trust base for a universally quantified lemma verified by this method:

1. **The SMT oracle** — each per-case axiom is backed by a Z3/CVC5 QF_SLIA proof.
   The query hash is stored in the axiom comment for re-verification.

2. **The case classifier** (`expanded_case`) — a Coq `Definition`, machine-checked.

3. **The Coq assembly proof** -- `Lemma type_convention` is fully machine-checked
   by `coqc`.  It uses no `Admitted`.

4. **The case extractor** -- a Python function that walks the IMP IR and produces
   `CaseBranch` list.  This is trusted in the same sense that the Python→IMP
   translator is trusted: it is part of the tool, not the verified output.

This is strictly stronger than `Admitted` (which trusts nothing), and is comparable
to using `coq-hammer` (which trusts the ATP but not the reconstruction).  The
difference from hammer: our per-case axioms are tagged with auditable query hashes
and can be re-verified at any time by re-running the SMT check.

---

## Comparison to Alternatives

| Approach | Quantifier | SMT needed | Coq proof | Redundancy |
|---|---|---|---|---|
| Induction in Coq | Universal | No | Inductive, by hand | None |
| Ground check only | Ground | QF_SLIA | None | Per call site |
| Bounded unfolding | Ground | QF_SLIA | None | Per call site |
| **This approach** | **Universal** | **QF_SLIA per case** | **Case analysis, forced** | **None** |

The key advantage over ground-only approaches: the universal lemma is proved
**once** and applied at all call sites via `apply type_convention`.  No re-proving
at callers.

The key advantage over pure Coq induction: the hard part (verifying that string
construction is correct in each case) is done by the SMT oracle, which handles
`str.++` and `str.suffixof` natively.  The Coq proof only does case routing,
which is mechanical.

---

## Implementation Plan

### Phase 1 -- Infrastructure

1. **`case_extractor.py`**: `extract_cases(imp_ir) -> list[CaseBranch]`
   - Walk `ImpCIf`/`ImpCSeq` tree
   - Collect path conditions and linear assignments per branch
   - Check mutual exclusivity via SMT (optional, for correctness assurance)

2. **`theory_smt.py`**: `dispatch_cases(cases, property_fragments) -> list[AxiomRecord]`
   - For each `CaseBranch`, construct the SMT fragment for the property
   - Run via existing `SmtOracle._run_fragment`
   - Emit one `AxiomRecord` per case

3. **`coq/ContractInvariants.v`**: skeleton file with:
   - `expanded_case` classifier definition
   - Template for per-case axioms (filled in by code generation)
   - Template for assembly lemma

### Phase 2 -- Apply to `_expand_params`

1. Extract the 6 cases from `_expand_params` IMP IR
2. For each case, verify the type-convention property (QF_SLIA)
3. Emit axioms to `ContractInvariants.v`
4. Write the assembly `Lemma type_convention` (10-15 lines)
5. Add contract to `_expand_params` docstring referencing the lemma
6. Wire `generate_obligations` to `apply type_convention` in stage proofs
   that use expanded params

### Phase 3 -- Apply broadly

Apply the same pattern to the other case-dispatch functions listed above.  The
extractor and verifier are reusable; only the property specification and the Coq
assembly change per function.

---

## Relationship to Existing Infrastructure

- **`theory_smt.py`**: `dispatch_cases` is a new entry point alongside
  `TheoryDispatcher.dispatch`.  It reuses `SmtOracle._run_fragment`,
  `_python_re_to_smt`, and the existing `AxiomRecord` type.

- **`obligation_gen.py`**: stage proofs for functions that call `_expand_params`
  can `apply type_convention` in the precondition bullet, the same way they
  `apply wp_ccall_frame` for frame conditions.

- **`coq/WpTactics.v`**: `ContractInvariants.v` is a peer module.  Axioms from
  SMT oracle checks use the same tagging convention as `smt_string_*` axioms
  already emitted by the theory oracle.

- **`self-verification-plan.md`**: this design closes the gap identified in Phase 1
  of the self-verification plan (type-dispatch functions) without requiring the
  induction support noted as "very high effort" in Phase 5.
