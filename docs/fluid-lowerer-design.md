# Fluid Predicate Lowerer: Design and Work Packages

The fluid lowerer is the concrete realization of the reflection map
`R : lambda_A^tot -> CoqTerm` from
[`fluid-contract-language-theory.md`](fluid-contract-language-theory.md). Its
job: take the pure fragment of a Python contract and produce a Coq term that is
total **by construction**, subsuming every existing contract-lowering path
under one principled, type-directed recursion.

This document is the implementation plan. It does **not** restate the theory;
it states what we build, against the code that exists today.

---

## 1. Goal and non-goals

**Goal.** A single function `lower(node, ctx) -> CoqTerm` that is:

- **total on `lambda_A^tot`** -- defined exactly on the totality judgment
  `Gamma |- t : tau (down)`; nodes outside the fragment are *rejected* with a
  concrete diagnostic, never silently emitted as a malformed term;
- **type-directed** -- coercions (boolean comparison form, float wrapping,
  string equality) are chosen from the *inferred type* of subterms, not from
  syntactic position or external mutable flags;
- **subsuming** -- it replaces `contract_ir_iris.iris_prop` *and* the per-node
  `to_coq(scoped=...)` emitters with one recursion, closing the value-model
  stubs that currently compile to `"True"`.

**Phasing.** Recursive predicates (D1) and loop / measured predicates (D2) are
**required**, not optional. They are deferred to a *second phase* only because
they build on the typed `lower` core, not because they are out of scope. The
core (WP-0..8) lands first; D1/D2 land as WP-9..13, fully specified in
[section 9](#9-recursive-and-loop-predicates-d1d2). The totality judgment is
designed from the start to *grow* the D1/D2 rules rather than be retrofitted.

**Non-goals (permanent).**

- The IMP/legacy backend (`to_coq(scoped=True)`, `s "x"`, `asZ`, `hget`) is not
  ported; it is superseded, then removed once parity is reached.
- No *ad-hoc* Coq surface. D1/D2 introduce **principled** new Coq (one emitted
  `Fixpoint`/`Equations` per recursive predicate, plus the loop variant rule) --
  see section 9; everything else reuses the fixed term language (section 3).

---

## 2. What exists today (the substrate we build on)

Confirmed by codebase survey. Absolute paths under
`py/axiomander/oracle/` and `coq/`.

| Layer | File | Role | Reuse? |
|---|---|---|---|
| AST -> IR | `contract_linter.py` (`ContractLinter`, 843 ln) | Python `ast.expr` -> `contract_ir.Expr` via `visit_*` | **Reuse front-end**; lower from its IR output |
| IR union | `contract_ir.py` (32 nodes, 863 ln) | discriminated `Expr` union; each node also carries legacy `to_coq/to_smt/to_python` | **Reuse node shapes**; stop using `to_coq` |
| IR -> Coq (Iris) | `contract_ir_iris.py` (`iris_prop`, 512 ln) | current Iris Prop compiler; ~12 nodes compile to `"True"` | **Replace** with `lower()` |
| Term language | `coq/SnakeletExnLang.v` | `sn_val`/`binop`/`binop_eval`, string preds | **Target** |
| Recursors | `coq/ListPredicates.v` | `forallb/existsb/countb/fold_left_acc/filterb` + lemmas | **Target** |
| Exec semantics | `snakelet_eval.py` | Python interpreter (refutation oracle) | Keep as oracle; **adequacy reference** |
| Dead code | `predicate_lowering.py` | `detect_loop_pattern` etc. unused; only `Recursor` enum is imported | **Retire** (replace the one import) |

Key facts that constrain the design:

- **`iris_prop` threads mutable module globals** (`_LIST_MODEL`, `_POST_BOUND`,
  `_FLOAT_PARAMS`, `_STRING_PARAMS`, `_BOOL_PARAMS`) because `_binop`/`_logical`
  recurse without forwarding kwargs. The fluid lowerer must instead thread an
  explicit immutable `LowerCtx` -- no globals.
- **The `z_scope` boolean-form coercion is positional today**: `_binop` emits
  `(a <? b) = true` iff `post_var` is non-empty. This is the single biggest
  correctness smell; the fluid lowerer makes it type-directed (a comparison
  always yields a `Prop`; whether it needs `= true` depends on the *operand
  type*, not on being in a postcondition).
- **Dict ops must route through `BinOp DictGetOp/DictSetOp`**, not the legacy
  `DictGet`/`DictSet`/`FAA`/`Fork` constructors (those exist only in the
  inactive `SnakeletLang.v`). `SCompound` already does this correctly.
- **Only `ListPredicates`/`RegMatch`/`DictModel` are dune-built.**
  `SnakeletExnLang` is compiled on demand via `coqc -R coq "" tmp`. New Coq
  Fixpoints the lowerer depends on go in one of those two places accordingly.

---

## 3. Target term language (fixed)

- Values: `sn_val` (`coq/SnakeletExnLang.v:49`) --
  `LitInt | LitBool | LitString | LitFloat | LitLoc | LitUnit | LitExn |
  LitList | LitTuple | LitDict | LitSet`.
- Operators: `binop` (`:63`, 30 ctors) evaluated by `binop_eval` (`:380`).
- Recursors: `forallb/existsb/countb/fold_left_acc/filterb`
  (`coq/ListPredicates.v`).
- String predicates: `str_all_hex`, `is_hex_char`, `string_contains`,
  `str_contains_val`, `str_to_lower_val` (`SnakeletExnLang.v:316-368`).
- Dict model: `model_field_Z`, `dict_lookup_Z` (`SnakeletExnLang.v`).
- WP gate lemmas: `wp_binop`, `wp_for_list_forall`, etc. (`SnakeletExnWp.v`).

---

## 4. Core design

### 4.1 Typed terms

`lower` returns a `CoqTerm { text: str, ty: Ty }` where `Ty` is the reified
type code of the pure fragment:

```
Ty ::= INT | BOOL | STR | FLOAT | LIST | TUPLE | DICT | SET | PROP | UNKNOWN
```

`PROP` is the type of a finished Coq proposition (output of a comparison /
connective / quantifier); it is distinct from `BOOL` (a `sn_val`). Carrying the
type is what lets coercions be *derived* rather than *guessed*.

### 4.2 The context (the judgment carrier)

`LowerCtx` is immutable and threaded explicitly:

```
LowerCtx {
  gamma      : name -> Ty        # the typing environment Gamma
  post_var   : str               # result variable name ("" outside postconditions)
  post_bound : str               # binder it renames to: z / s / b / v
  list_model : name -> coq_model # xs -> M_xs for len()/recursors
}
```

`ctx.bind(x, ty)` produces a child context for quantifier binders. There are
**no module globals**.

### 4.3 The recursion shape

`lower(node, ctx)` matches on `node.kind` and returns a typed term. Three
representative clauses show the type-direction principle:

- **Comparison `a < b`.** Lower `a` and `b`; from their joined type decide the
  Coq form: `INT/INT -> (a <? b) = true : PROP`; `FLOAT-involved ->
  (PrimFloat.ltb a' b') = true : PROP` with `z2float` inserted on the non-float
  side; `STR` equality -> `(String.eqb a b = true) : PROP`. The `= true` is
  emitted because the operand type is a decidable `bool`, **independent of
  postcondition position**.
- **`len(x)`.** Type of `x` decides: `STR -> Z.of_nat (String.length ...)`;
  `LIST -> Z.of_nat (List.length M_x)`. Result type `INT`.
- **`all(p(x) for x in xs)`.** Bind `x : elem(typeof xs)`, lower `p` to a
  `bool` lambda, emit `forallb (fun x => ...) M_xs = true : PROP`. This is the
  D0 bounded recursor; totality is structural and free.

### 4.4 The totality gate

A node reaches `lower` only if a `Gamma |- node : tau (down)` derivation
exists. In practice the gate is folded into `lower`: any clause that cannot
assign a type (unknown call, self-recursive predicate, unbounded quantifier
over a non-range domain) raises `FluidLowerError` with a message naming the
construct. This is the "reject at the boundary" behavior -- the linter surfaces
it as a violation rather than producing `"True"` or a bad term.

### 4.5 Embedding into pre/postconditions

Two thin wrappers replace `compile_precondition`/`compile_postcondition`:

- **precondition**: `lower(node, ctx).text` (must have type `PROP`; a bare
  `BOOL` value is coerced `... = true`).
- **postcondition**: `exists <binder> : <T>, v = <Ctor> <binder> /\ P`, where
  `<binder>`/`<Ctor>`/`<T>` come from the *inferred result type* (INT -> `z`,
  `LitInt`, `Z`; STR -> `s`, `LitString`, `string`; BOOL -> `b`, `LitBool`,
  `bool`; structural -> `v`, identity, `sn_val`). Today `_result_value_kind`
  guesses this by walking the tree; the fluid lowerer *knows* it from the type.

---

## 5. Subsumption map (what each existing path becomes)

| Existing | Fluid replacement | Notes |
|---|---|---|
| `iris_prop` dispatch | `lower` match on `kind` | one recursion, explicit ctx |
| `_binop` z_scope flag | type-directed comparison clause | removes positional `= true` |
| `_var` float/bool/result rename | `gamma` lookup + `post_bound` | no `_FLOAT_PARAMS` global |
| `_list_len` string/list branch | `len` clause off `Ty` | |
| `_all`/`_any` range only | `all`/`any` over list (forallb/existsb) **and** range | closes list stub |
| `_recursor` | recursor clause (same output) | |
| `_hex_string`/`_string_contains`/`_string_eq` | string clauses (same output) | |
| `_placeholder -> "True"` for `index/dict_len/dict_count/sum/tuple/dict/set/list_eq` | real clauses over `LitList/LitTuple/LitDict/LitSet` | **the value-model closure** |
| per-node `to_coq(scoped=...)` | deleted | after parity |
| `predicate_lowering.detect_loop_pattern` | deleted | unused already |

"True" stubs that **stay** "True" deliberately (out of pure fragment, handled
elsewhere): `raises` (exception arm, handled upstream), `rown`/`opaque_term`
(resource/observer, discharged by callee contracts), `is_shape` (well-typed at
`sn_val` level).

---

## 6. Work packages

Each WP is independently testable and lands behind a flag until parity. Tests
mirror `py/tests/test_iris_python_pipeline.py` conventions (assert exact Coq
output per node; `coqc -R coq "" tmp` for end-to-end positives/negatives).

### WP-0  Module scaffold + types  (S)
- New `fluid_lowering.py`: `Ty`, `CoqTerm`, `FluidLowerError`, `LowerCtx`.
- No lowering yet. Unit tests for `LowerCtx.bind`, `typ`, immutability.
- **Exit:** types importable; ctx threading proven by test.

### WP-1  Scalar core  (M)
- Clauses: `var`, `int`, `bool`, `strlit`, `float`, `binop` (arith +
  compare, int/float/string, type-directed coercion), `logical`,
  `implies`, `min`, `max`, `slice_len`.
- **Exit:** byte-for-byte parity with `iris_prop` on all scalar nodes
  (golden-output tests diffing `lower` vs `iris_prop`); the positional
  `z_scope` smell replaced by the type-directed rule, *verified equal on the
  existing corpus*.

### WP-2  Bounded recursors (the D0 fragment)  (M)
- `all`/`any` over a **list** -> `forallb`/`existsb ... = true` (closes the
  current `"True"` stub); over a **range** -> the existing forall/exists Prop;
  `sum(1 for x in xs if p)` -> `countb` (already an IR `RecursorExpr`, route
  through the recursor clause).
- Predicate body lowering: the comprehension filter becomes a `bool` lambda via
  `lower` (not the string-based `_compile_comprehension_filter`).
- **Exit:** `all(x > 0 for x in xs)` end-to-end proves via `forallb` +
  `forallb_true`/`wp_for_list_forall`; negative test (`all(x > 0 ...)` with a
  zero element) fails.

### WP-3  Totality gate + diagnostics  (S)
- Reject: unknown call (non-builtin, non-predicate), self-recursive predicate,
  unbounded quantifier over a non-range/non-list domain, untyped variable.
- Each rejection: `FluidLowerError` with construct name; linter maps it to a
  `Violation` (mirror existing `UNSUPPORTED`/`IMPURE_CALL`).
- **Exit:** rejection tests assert the diagnostic text; no node ever yields a
  malformed Coq term.

### WP-4  Value-model closure (immutable structures)  (L)
- `LenExpr`/`IndexExpr` over `LitList`; `list_eq` -> structural
  `value_eqb`/equality over `LitList`; `tuple`/`set`/`dict` literals ->
  `LitTuple`/`LitSet`/`LitDict`; `dict_len`/`dict_count` via dict model.
- May require small Coq lemmas (e.g. `nth`/`length` over `LitList`); add to
  `ListPredicates.v` (dune-built) where pure, else `SnakeletExnLang.v`.
- **Exit:** a contract over `result == [a, b]` and `xs[0] == ...` proves; this
  is the section-10 representation-predicate seam exercised end-to-end for
  tree-shaped values.

### WP-5  Pre/postcondition wrappers  (S)
- `compile_precondition_fluid`, `compile_postcondition_fluid` using the
  inferred result type for the existential binder/constructor.
- **Exit:** parity with `compile_precondition`/`compile_postcondition` on the
  corpus; result-kind no longer guessed by `_result_value_kind`.

### WP-6  Pipeline wiring behind a flag  (M)
- `iris_pipeline.py` selects fluid vs legacy via `AXIOMANDER_FLUID=1` (env) or
  a `Contracts` flag. Default stays legacy until WP-1..5 reach parity.
- **Exit:** full suite (238 tests) green with flag **off**; a curated subset
  green with flag **on**.

### WP-7  Cutover + delete legacy  (M)
- Flip default to fluid. Delete `iris_prop` `_placeholder` paths,
  per-node `to_coq(scoped=...)`, `predicate_lowering.detect_loop_pattern`,
  string-based `_compile_comprehension_filter`.
- **Exit:** suite green with fluid as the only path; legacy code removed; one
  remaining import of `Recursor` enum either kept or inlined.

### WP-8  Adequacy harness (cross-check vs executable semantics)  (M)
- Property test: for a generated pure value and predicate, evaluate via
  `snakelet_eval.py` and check the lowered Coq term `vm_compute`s to the same
  boolean (the `R(t) ~>* lit(eval t)` adequacy obligation, machine-checked per
  instance). This is translation validation for the lowerer (section 7 of the
  theory), short of a Coq-verified `R`.
- **Exit:** N random (value, predicate) pairs agree between interpreter and
  `vm_compute`d Coq term; disagreement is a hard failure.

Sizes: S ~= half day, M ~= 1-2 days, L ~= 3+ days. Critical path:
WP-0 -> WP-1 -> WP-2 -> WP-5 -> WP-6. WP-3/WP-4/WP-8 parallelizable after WP-1.

---

## 7. Risks and the honest boundary

- **Type inference gaps.** `gamma` must be populated from parameter type hints
  and the result type. Where a type is genuinely unknown (`UNKNOWN`), the
  lowerer must reject (WP-3), not guess. Risk: over-rejection on contracts the
  legacy path accepted via `"True"`. Mitigation: WP-6 flag + corpus diff before
  cutover.
- **Parity vs improvement.** WP-1/WP-5 demand *byte-for-byte* parity on scalars
  so cutover is safe; WP-2/WP-4 are strict *improvements* (close `"True"`), so
  they add new proofs that must be validated by `coqc`, not just diffed.
- **D1/D2 are phase 2, not out of scope.** The core lowerer's totality is
  inherited from D0 (bounded recursors); recursive and loop predicates are added
  in section 9 (WP-9..13). Until WP-9 lands the lowerer *rejects* recursion with
  a diagnostic (WP-3) -- a safe, honest gate, not a silent gap.
- **Trusted edge unchanged.** Python -> IR elaboration stays trusted (theory
  section 7); the lowerer narrows the gap below the IR but does not close the
  AST->IR boundary. WP-8 adds per-instance validation, not a verified `R`.

---

## 8. Definition of done (phase)

1. `lower` is the only IR->Coq path used by `iris_pipeline` (legacy deleted).
2. No node in the pure fragment compiles to `"True"` (only the deliberate
   out-of-fragment nodes do).
3. Comparison coercion is type-directed; no positional `z_scope`.
4. The 238-test suite is green; new positive/negative tests cover every clause.
5. WP-8 adequacy harness passes on a random corpus.
6. `predicate_lowering.py` dead code removed.

Phase 2 (D1/D2) has its own DoD in [section 9.6](#96-definition-of-done-phase-2).

---

## 9. Recursive and loop predicates (D1/D2)

This is the second phase, and it is mandatory. A predicate like

```python
def is_sorted(xs: list[int]) -> bool:
    if len(xs) <= 1:
        return True
    return xs[0] <= xs[1] and is_sorted(xs[1:])     # D1: structural recursion
```

or a loop predicate

```python
def all_positive(xs: list[int]) -> bool:
    ok = True
    for x in xs:                                    # D2: loop (bounded)
        if x <= 0:
            ok = False
    return ok
```

must enter the pipeline and reflect to a **guard-passing Coq definition**, not
be rejected. The theory (sections 11.1-11.5) fixes *what* is required; this
section fixes *how* it lands in the code.

### 9.1 The three sources, and where each goes

| Source shape | Discipline | Reflects to | Owner |
|---|---|---|---|
| `for`/comprehension over a finite collection | D0 (done) | `forallb`/`existsb`/`countb` over the list | WP-2 (core) |
| imperative `for ... :` loop in a predicate body | D2-bounded | the same recursors, via loop-to-recursor normalization | WP-12 |
| `while` with a user variant | D2-measured | loop variant obligation on the WP side | WP-13 |
| self-recursive `def` with a structural argument | D1 | an emitted `Fixpoint` (one per predicate) | WP-9..11 |
| self-recursive `def` with a non-structural measure | D2-measured | an emitted `Equations`/`Program Fixpoint` + decrease obligation | WP-11 |

The unifying move: a recursive predicate is **reflected once into a named Coq
definition** placed in the generated preamble, and *every call site lowers to an
application of that name* -- exactly how `RecursorExpr` already lowers to
`existsb p xs`, generalized from fixed combinators to arbitrary user `Fixpoint`s.
This is the reflection-first design from
[`predicate-lifting-plan.md`](predicate-lifting-plan.md): combinators
(`forallb` etc.) become a *special case* of emitted recursive definitions, not
the foundation.

### 9.2 The pipeline path for a recursive predicate

```
def is_sorted(xs): ...            (Python AST of the predicate body)
        |
        | (1) totality analysis: Gamma |- body : bool (down)?   [WP-9]
        |     - detect self-call; find the decreasing argument
        |     - D1: structural subterm  OR  D2: user `decreases m`
        v
   PredicateDef { name, params, body_ir, rec_arg | measure }     (new IR record)
        |
        | (2) slice-to-match reassociation                        [WP-10]
        |     xs[1:]/xs[0] recursion  ->  match xs with [] | x::rest
        v
   a SnakeletIR / structural body whose recursive call lands on `rest`
        |
        | (3) emit Coq Fixpoint (D1) or Equations (D2)            [WP-11]
        |     `Fixpoint is_sorted (xs : list Z) : bool := match xs with ...`
        v
   named definition in the proof preamble  +  adequacy lemma stub
        |
        | (4) call sites lower via `lower`                        [WP-9]
        |     is_sorted(ys)  ->  CoqTerm("is_sorted M_ys", BOOL)
        v
   contract uses `is_sorted M_ys = true`  (a `prop` leaf, section 9 of theory)
```

The current `_expand_predicate` (`contract_linter.py:370`) does step (4) only by
*inlining* (it has no recursion case and rejects at line 440). The change is:
when the predicate is recursive, **stop inlining** -- register it as a
`PredicateDef`, emit the `Fixpoint`, and lower call sites to an application.

### 9.3 The totality analysis (WP-9): the `(down)` gate made operational

A new analysis `classify_recursion(func_node) -> RecKind` returns one of:

- `NONREC` -- no self-call; existing inliner path (unchanged).
- `STRUCTURAL(arg)` -- self-call(s) all occur on a syntactic *reduction* of one
  parameter (`xs[1:]`, `xs[:-1]`, `rest` after an unpack). This is D1.
- `MEASURED(measure_expr)` -- a `# decreases: <expr>` annotation is present and
  every self-call strictly decreases it. This is D2.
- `REJECT(reason)` -- self-call with no detectable structural decrease and no
  measure: a concrete diagnostic ("`f` recurses on `g(xs)` which is not a
  sub-structure of `xs`; add `# decreases: <expr>`").

The analysis walks the AST (never strings -- per AGENTS.md), comparing each
self-call's argument to the parameters under the slice/index/unpack
relation. `STRUCTURAL` requires that the reduction is one Coq's guard checker
will accept *after* reassociation (WP-10), which is the load-bearing invariant.

### 9.4 Slice-to-match reassociation (WP-10): the heart of D1

Python expresses structural recursion by *slicing the same value*
(`is_sorted(xs[1:])`); Coq's guard checker only accepts recursion on a
*subterm bound by a `match`*. WP-10 is the normalizer that bridges them:

```
recursion on xs[1:]   =>   match xs with
                            | []        => <base, with len(xs)<=k branches folded in>
                            | x :: rest => <body[xs[0]:=x, xs[1:]:=rest]>
```

Rules:
- `xs[0]`, `xs[1]` in the body become `x` and `head rest` once `xs` is matched.
- `xs[1:]` becomes `rest` (the bound subterm) -- the *only* shape that makes the
  emitted `Fixpoint` guard-pass.
- `len(xs) <= c` guards in the source fold into the `[]`/singleton match arms.
- Multi-argument and `xs[:-1]` (prefix) recursion: handled by reversing or by a
  secondary accumulator; if neither applies, fall through to D2 (demand a
  measure). The normalizer is *partial and honest*: when it cannot expose a
  subterm it returns `None` and WP-9 reclassifies as `REJECT`/`MEASURED`.

**Owed lemma (preservation of decrease).** The reassociation must be
*semantics-preserving*: the emitted `match`-form computes the same boolean as
the sliced source on every input. This is verified per-instance by the WP-8
adequacy harness extended to recursive predicates (evaluate both via
`snakelet_eval` and `vm_compute`), and is the concrete form of theory
section 11.5.2.

### 9.5 Emission and the WP connection (WP-11/12/13)

- **WP-11 (emit D1/D2 definitions).** From the reassociated body, emit:
  - D1: `Fixpoint <name> (a : <Ty>) ... : bool := match ... end.` into the
    preamble. The kernel's acceptance *is* the totality proof (no obligation).
  - D2: `Equations <name> ... by wf (measure args) lt := ...` (or
    `Program Fixpoint`), producing decrease obligations routed to the 3-tier
    prover (lia/SMT/LLM); rejection on failure.
  Placement: pure recursive definitions over `list Z`/`Z` go in a dune-built
  theory (extend `ListPredicates.v` or a new `UserPredicates` generated file);
  definitions touching `sn_val` go in the on-demand-compiled preamble.
- **WP-12 (imperative loop predicates -> recursors).** A `for x in xs:` body
  that accumulates a boolean / count normalizes to `forallb`/`existsb`/`countb`
  (the D0 recursors) by recognizing the accumulator pattern -- reusing the
  WP-2 recursor clause. This subsumes the dead `detect_loop_pattern`
  (`predicate_lowering.py`) with an AST-level, IR-producing analysis.
- **WP-13 (`while` with variant).** Generalize the single `wp_while_str`
  special case (`SnakeletExnTactics.v`, guard-falsification) to a user
  `decreases` variant on `while`: the loop measure strictly decreases in `<`
  on N each iteration, discharged as a WP-side obligation. This is the
  imperative counterpart of D2 and the last piece needed for general loops.

### 9.6 Definition of done (phase 2)

1. A self-recursive `def` predicate with a structural argument
   (`is_sorted` above) **verifies end-to-end** via an emitted `Fixpoint`; the
   `Fixpoint` is kernel-accepted with no `Admitted`.
2. A measured predicate (`# decreases:`) verifies via `Equations`, with its
   decrease obligation discharged by the prover; a *false* measure is rejected.
3. An imperative loop predicate (`all_positive` above) lowers to `forallb` and
   verifies; `detect_loop_pattern` is deleted.
4. A `while` with a user variant verifies for termination; the
   guard-falsification case remains a special case of the general rule.
5. The reassociation passes the extended WP-8 adequacy harness on a recursive
   corpus (interpreter and `vm_compute` agree).
6. A recursive predicate with no structural arg and no measure is **rejected**
   with the section-9.3 diagnostic -- never silently mistranslated.

### 9.7 New work packages

| WP | Title | Size | Depends |
|---|---|---|---|
| WP-9  | `classify_recursion` + `PredicateDef` IR; call sites lower to application | M | WP-1, WP-3 |
| WP-10 | Slice-to-match reassociation normalizer (D1) | L | WP-9 |
| WP-11 | Emit `Fixpoint` (D1) / `Equations` (D2) + route decrease obligations | L | WP-10 |
| WP-12 | Imperative loop predicate -> recursor normalization; retire `detect_loop_pattern` | M | WP-2 |
| WP-13 | `while` user variant -> WP-side decrease obligation | L | WP-2 |

Critical path for D1: WP-9 -> WP-10 -> WP-11. WP-12 depends only on WP-2 and can
proceed in parallel. WP-13 is independent of D1 and extends the existing loop
machinery in `SnakeletExnTactics.v`.
