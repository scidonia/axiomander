# A Fluid Contract Language: Formal Account

A "fluid" contract language is one where **any pure term of the program
language is also a term of the specification language**, with a single,
total, semantics-preserving translation between them. Fluidity is not a
feature set; it is the property that the specification logic and the
executable core share one term calculus and one denotation.

This document gives the calculus, its two interpretations, the reflection
map that connects them, the elaboration of contracts to verification
conditions, and the soundness theorem that makes the whole thing trustworthy.

---

## 1. The core calculus λ_A (the pure fragment)

We isolate the pure, terminating fragment of SnakeletIR. This is the shared
substrate: both the executable semantics and the logic are defined over it.

### 1.1 Syntax

```
Types        τ ::= int | bool | str | list τ | τ × τ | dict τ τ | set τ
Values       v ::= n | b | s | [v,…] | (v,…) | {v↦v,…} | {v,…}
Operators    ⊕ ::= + | − | × | = | < | ≤ | ∧ | ∨ | ¬ | ∈ | len | …
Terms        t ::= x                      (variable)
                 | v                       (literal)
                 | t ⊕ t                   (primitive op)
                 | f(t,…,t)                (call to pure f ∈ Σ)
                 | if t then t else t      (conditional)
                 | let x = t in t          (binding)
                 | match t with …          (structural elimination)
```

`Σ` is the **signature**: the set of pure functions in scope (user-defined
predicates and pure helpers). Each `f ∈ Σ` has an arity and a definition
`f(x₁…xₙ) = t_f` whose body `t_f` is itself a λ_A term, possibly recursive
with a structural decreasing argument.

### 1.2 Typing

A standard simply-typed judgment `Γ ⊢ t : τ` over `Σ`:

```
  x:τ ∈ Γ                       Γ ⊢ t₁:τ₁   Γ ⊢ t₂:τ₂   ⊕ : τ₁→τ₂→τ
  ─────────                     ──────────────────────────────────────
  Γ ⊢ x:τ                       Γ ⊢ t₁ ⊕ t₂ : τ

  f : τ₁→…→τₙ→τ ∈ Σ   Γ ⊢ tᵢ:τᵢ      Γ ⊢ t₀:bool  Γ ⊢ t₁:τ  Γ ⊢ t₂:τ
  ────────────────────────────────      ────────────────────────────────
  Γ ⊢ f(t₁,…,tₙ) : τ                    Γ ⊢ if t₀ then t₁ else t₂ : τ
```

Well-typed λ_A terms are the only things the contract language admits; this is
what eliminates the `Z`-only assumption that plagues string-templated lifting.

---

## 2. Two interpretations of λ_A

The single calculus has two meanings. Fluidity is the theorem that they agree.

### 2.1 Operational semantics (what runs)

A total evaluator on well-typed closed terms:

```
⟦·⟧ᴱ : Term → Env → Value
```

defined by the obvious recursion; `⟦f(t…)⟧ᴱ ρ = ⟦t_f⟧ᴱ [xᵢ ↦ ⟦tᵢ⟧ᴱ ρ]`.
Totality holds because every `f ∈ Σ` is terminating. This is exactly what
`snakelet_eval.py` computes and what Coq's `binop_eval` / `Fixpoint`
reductions compute.

### 2.2 Logical reflection (what the prover reasons about)

A translation into Coq terms:

```
R : Term → CoqExpr
R(x)                 = x
R(v)                 = lit(v)
R(t₁ ⊕ t₂)           = ⊕_coq (R t₁) (R t₂)
R(f(t₁,…,tₙ))        = f_coq (R t₁) … (R tₙ)      -- f_coq : reflected Fixpoint
R(if t₀ then t₁ t₂)  = if R t₀ then R t₁ else R t₂
R(let x=t₁ in t₂)    = let x := R t₁ in R t₂
R(match t with …)    = match R t with …
```

For each `f ∈ Σ`, `f_coq` is the Coq `Fixpoint` obtained by reflecting `t_f`:

```
Definition/Fixpoint f_coq (x₁:R τ₁) … (xₙ:R τₙ) : R τ := R(t_f).
```

`R` is **total on well-typed λ_A terms** — there is no fallback case, no
`ast.unparse`, no string templating. Every syntactic form has a structural
image.

### 2.3 The adequacy theorem (the heart of fluidity)

> **Theorem (Reflection Adequacy).** For every well-typed closed term `t` and
> environment `ρ`, the Coq term `R(t)[ρ]` reduces to `lit(⟦t⟧ᴱ ρ)`:
> ```
>   R(t)[ρ]  ⇝*  lit(⟦t⟧ᴱ ρ)
> ```

Proof by induction on `t`, using for the `f` case that `f_coq`'s body is
`R(t_f)` and the IH on `t_f`. (Recursive `f` needs the corresponding fixpoint
unfolding; the structural measure guarantees the induction is well-founded.)

**Consequence.** The logical meaning of any contract term is *provably* its
computational meaning. A predicate cannot mean one thing when it runs and
another when it is reasoned about. This is precisely the property a
string-templating lifter cannot guarantee.

---

## 3. The contract language

The contract language is λ_A **in assertion position**, closed under the
logical connectives and quantifiers.

```
Formulas   φ ::= b(t)                    boolean term t lifted:  R(t) = true
                | t ≐ t | t ≺ t | …       atomic relations
                | φ ∧ φ | φ ∨ φ | ¬φ
                | φ ⟹ φ
                | ∀ x:τ. φ | ∃ x:τ. φ
                | old(t)                  pre-state value (post only)
                | result                  the returned value (post only)
```

A **contract** for a function `g(p₁…pₘ)` is a pair `(P, Q)`:

```
  P  : Formula over p₁…pₘ                  (precondition)
  Q  : Formula over p₁…pₘ, result, old(·)  (postcondition)
```

Elaboration of a formula to a Coq `Prop`:

```
⟦b(t)⟧ᴾ          = (R(t) = true)
⟦t₁ ≐ t₂⟧ᴾ       = (R(t₁) = R(t₂))
⟦φ₁ ∧ φ₂⟧ᴾ       = ⟦φ₁⟧ᴾ ∧ ⟦φ₂⟧ᴾ
⟦¬φ⟧ᴾ            = ¬ ⟦φ⟧ᴾ
⟦φ₁ ⟹ φ₂⟧ᴾ      = ⟦φ₁⟧ᴾ → ⟦φ₂⟧ᴾ
⟦∀x:τ. φ⟧ᴾ       = ∀ x:R τ, ⟦φ⟧ᴾ
⟦∃x:τ. φ⟧ᴾ       = ∃ x:R τ, ⟦φ⟧ᴾ
⟦result⟧         = the WP-bound result variable
```

`b(·)` is the lifting coercion: a boolean *term* `t` (e.g. `is_hex(s)`) becomes
the *proposition* `R(t) = true`. This single coercion is what lets an
arbitrary pure predicate appear in a contract — `is_hex(result)` is
`⟦b(is_hex(result))⟧ᴾ = (is_hex_coq (R result) = true)`, a closed Coq Prop.

---

## 4. Verification conditions via WP

Let `B` be the (possibly impure) body of `g`, expressed in full SnakeletIR
(λ_A plus heap/exception effects). The WP calculus `wp(B, Φ)` is already
defined and proven sound in Coq (SnakeletExnWp). The verification condition is:

```
  VC(g)  ≡  ∀ p₁…pₘ,  ⟦P⟧ᴾ  →  wp( B, λ result. ⟦Q⟧ᴾ )
```

The contract terms enter `wp` only through `⟦·⟧ᴾ`, i.e. through `R`. So the
prover never sees Python, never sees strings — it sees Coq Props built by the
total, adequate reflection.

---

## 5. Soundness

Three layers, composed:

```
  (A)  WP soundness        wp(B, Φ) ⟹ every execution of B ends satisfying Φ
                           [proven in Coq: SnakeletExnWp]

  (B)  Reflection adequacy R(t)[ρ] ⇝* lit(⟦t⟧ᴱ ρ)
                           [§2.3, proven by induction]

  (C)  Translation         the Python source elaborates to (B, P, Q) in λ_A/IR
                           [TRUSTED — see §7]
```

> **Theorem (End-to-end correctness, modulo C).** If `VC(g)` is proved in
> Coq, then for all inputs satisfying `P`, the operational execution of `g`'s
> body produces a `result` satisfying `Q` — where "satisfying" is the
> *operational* reading via `⟦·⟧ᴱ`.

Proof. `VC(g)` proved ⟹ (A) gives operational executions land in
`λ result. ⟦Q⟧ᴾ`. (B) lets us replace every `R(t)` in `⟦Q⟧ᴾ` by `lit(⟦t⟧ᴱ)`,
turning the logical postcondition into the operational one. ∎

The only unverified link is (C). That is the translation gap, and it is the
single thing standing between "fluid and sound modulo a trusted compiler" and
"fluid and sound, full stop."

---

## 6. Fluidity, precisely

The language is *fluid* in exactly this sense:

> **Definition (Fluidity).** A specification language is fluid over a program
> calculus λ if there is a total, type-preserving, adequacy-satisfying
> reflection `R : λ_pure → Logic` such that every pure program term is a
> specification term with `R(t)` denoting `⟦t⟧ᴱ`.

Three corollaries, each a concrete capability we currently lack:

1. **Composition is free.** `is_permutation` calls `count_item`; under `R`,
   the call `count_item(t…)` becomes `count_item_coq (R t…)`. No special case —
   `R` is homomorphic on application.

   ```python
   def count_item(x: int, xs: list) -> int:
       c = 0
       for e in xs:
           if e == x: c += 1
       return c

   def is_permutation(xs: list, ys: list) -> bool:
       if len(xs) != len(ys): return False
       for x in xs:
           if count_item(x, xs) != count_item(x, ys): return False
       return True
   ```
   `R(is_permutation)` = a Coq `Fixpoint` calling `count_item_coq`. Usable as
   `ensures: is_permutation(result, old(xs))` with no new machinery.

2. **No semantic drift.** By adequacy, `is_hex(result)` in a contract means
   exactly what `is_hex` computes. A string-templating lifter has no such
   guarantee and can silently mean something else.

3. **The recursors are derived, not primitive.** `forallb`, `existsb`,
   `countb` are *recognizable shapes of reflected Fixpoints*, kept only to
   inherit pre-proved lemmas. They are an optimization over `R`, never a
   prerequisite.

---

## 7. The trusted edge (C) and how to discharge it

(C) is the elaboration `Python AST → λ_A/IR`. Two routes to remove it from the
TCB:

- **Translation validation.** For each elaboration instance, emit a checkable
  certificate that the IR term has the same `⟦·⟧ᴱ` as a reference semantics of
  the Python AST fragment. Cheaper than full verification; per-run, not
  once-and-for-all. (CompCert uses this for register allocation.)

- **Verified elaboration.** Define `elaborate : PyAST → Term` *in Coq* and
  extract it. Then (C) becomes a Coq theorem and the chain is closed.

Until then the honest statement is: **fluid and sound modulo a trusted, total
elaboration into λ_A.** That is already strictly stronger than any
SMT-only system (which trusts the solver *and* the encoding), and it is the
same trust posture as Nagini — but with kernel-checked proofs below the IR.

---

## 8. Summary of the construction

| Layer | Object | Status |
|---|---|---|
| Core calculus | λ_A (pure SnakeletIR fragment) | exists |
| Operational semantics | `⟦·⟧ᴱ` | `snakelet_eval.py`, Coq `binop_eval` |
| Reflection | `R : Term → CoqExpr`, total, homomorphic | **to build (replaces string lifter)** |
| Adequacy | `R(t) ⇝* lit(⟦t⟧ᴱ)` | **to prove (induction)** |
| Contract elaboration | `⟦·⟧ᴾ` with lifting coercion `b(·)` | partial (per-node compilers exist) |
| VC generation | `∀ p, ⟦P⟧ᴾ → wp(B, λr.⟦Q⟧ᴾ)` | exists |
| WP soundness | (A) | proven (SnakeletExnWp) |
| Elaboration soundness | (C) | trusted — discharge via validation/extraction |

The fluid contract language is the pair `(R, ⟦·⟧ᴾ)` over λ_A, made trustworthy
by the adequacy theorem (§2.3) and the WP soundness already in hand. Building
`R` as a total reflection — and proving its adequacy — is the concrete next
piece of work; everything else is either already present or a known technique.

---

## 9. Does fluidity fit inside Iris?

Yes — comfortably, and via standard Iris layering. The key observation that
makes the fit clean:

**The boundary is exactly the boundary between the *executable/decidable*
fragment and the *quantified/spatial/propositional* fragment.** Fluidity lives
entirely on the executable side. Iris owns the other side. They meet at a
single, well-understood seam: the pure embedding `⌜·⌝`. Nothing about fluidity
asks Iris to do anything non-standard; it asks only that pure reflected facts
appear as `⌜φ⌝` leaves inside Iris propositions, which is precisely what that
connective is for.

### 9.1 Pure reflected terms live at the `⌜·⌝` leaves

A reflected predicate `R(p) : CoqExpr` of type `bool` (or its `Prop`
reflection) enters an Iris proposition `iProp` through the pure-embedding
coercion:

```
⌜ R(p) = true ⌝  :  iProp
```

This is the canonical Iris idiom. `⌜·⌝ : Prop → iProp` injects a meta-level
proposition as an Iris proposition with no spatial content. Every fluidly
reflected predicate is, at the Iris level, a `⌜·⌝`-wrapped decidable fact.
Fluidity therefore does **not** extend Iris's logic — it populates the pure
leaves of an otherwise ordinary Iris proposition.

### 9.2 The WP postcondition structure

A verified function with contract `(P, Q)` becomes, in Iris-WP form:

```
{ ⌜⟦P⟧ᴾ⌝ ∗ heap-resources }  B  { r. ⌜⟦Q⟧ᴾ r⌝ ∗ heap-resources' }
```

The fluid (pure) part of `P` and `Q` is the `⌜·⌝` conjunct; the spatial part
(`l ↦ v`, ownership, invariants) is Iris's own. The two are joined by `∗`. The
pure conjunct is discharged by **reflection + adequacy** (§2.3): reduce
`R(p)` by `vm_compute`/`reflexivity` to a literal, exactly as in the standalone
calculus. Iris never reasons about the *internals* of a reflected predicate —
it carries the `⌜·⌝` fact and the pure side closes it.

### 9.3 Persistence: pure facts are free to duplicate

`⌜φ⌝` is **persistent** in Iris (`Persistent ⌜φ⌝`). Reflected predicate facts
can be freely duplicated, framed, and reused without affecting resources.
This matches their meta-status: a pure fact about a value is not consumed by
use. So fluid predicates compose with the separating conjunction without any
of the linearity caveats that spatial assertions carry. This is the formal
reason fluidity and separation logic do not interfere: pure ⊆ persistent ⊆
freely-shareable.

### 9.4 The spatial split: representation predicates

Mutable data is where Iris earns its keep, and the bridge is the standard
**representation-predicate** pattern:

```
isList l vs  ≜  l ↦ … ∗ … (spatial layout) …            (* Iris's job *)
sortedList l ≜  ∃ vs, isList l vs ∗ ⌜ R(is_sorted)(vs) = true ⌝
```

The spatial predicate `isList l vs` relates a heap location to a *pure value*
`vs : list τ`. Once we have the pure value, every fluid predicate over it is a
`⌜·⌝` leaf. So the division of labour is total and clean:

| Concern | Owner |
|---|---|
| Heap layout, aliasing, ownership, framing | Iris (spatial `∗`, `↦`) |
| Properties of the *extracted pure value* | fluid reflection (`⌜R(·)⌝`) |

The mutable/immutable split already mandated by AGENTS.md (VList value vs. heap
representation) is *exactly* this representation-predicate seam. Fluidity was
designed for the pure value; Iris handles the heap that the value mirrors.

### 9.5 No step-indexing burden

Fluid predicates are **Coq `Fixpoint`s with structural recursion**, not
Iris-recursive (guarded) definitions. They do not pass through Iris's `▷`
(later) modality and incur no step-indexing obligations. This is a direct
consequence of λ_A's termination requirement (§1.1: recursion is structurally
decreasing). Iris's `▷` exists to tame *non-well-founded* recursion (recursive
`iProp`s, impredicative invariants); fluid predicates never need it because
they bottom out in the kernel's own termination checker. So embedding fluid
predicates into Iris adds **zero** later-modality reasoning — they sit under
`⌜·⌝` as plain decidable terms.

### 9.6 Quantifiers

Universally/existentially quantified fluid predicates
(`∀ x ∈ xs, φ(x)`) reflect to bounded recursors (`forallb`, `existsb`,
`countb` over the concrete list) and remain **decidable** `bool` terms — still
`⌜·⌝` leaves, still closed by computation. Unbounded quantifiers over infinite
domains (`∀ n : Z, …`) are *not* in the executable fragment; they live on the
Iris/`Prop` side as ordinary `∀` in `iProp` and are discharged by tactic/SMT,
not by reflection. This is the precise statement of the boundary: **bounded =
fluid/decidable/`⌜·⌝`; unbounded = Iris-propositional.**

### 9.7 Two adequacy theorems compose

The trust chain factors into two independent adequacy results that compose
end-to-end:

```
Iris adequacy:        ⊢ {True} e {v. ⌜φ v⌝}   ⟹   safe(e) ∧ (e ⇓ v → φ v)
                                                     (meta-level φ holds)
Reflection adequacy:  R(t) ⇝* lit(⟦t⟧ᴱ)        (§2.3)
                                                     (φ is the right meta-fact)
```

Iris adequacy lifts a proved WP into a meta-level fact about the program's
final value `⌜φ v⌝`. Reflection adequacy guarantees that the `φ` appearing
there is *defeq to the executable predicate's value*. Their composition gives:
**if the Iris-WP proof goes through, the program's result satisfies the fluid
predicate under its executable semantics.** No new metatheory is required —
each half is a known, kernel-checked theorem.

### 9.8 Conclusion

Fluidity fits inside Iris as a **conservative pure layer**:

- pure reflected predicates → `⌜·⌝` leaves (persistent, freely shareable);
- spatial/heap reasoning → Iris's native `∗`/`↦`, joined to pure values by
  representation predicates;
- termination of λ_A → no `▷`/step-indexing obligations;
- bounded quantifiers → decidable recursors under `⌜·⌝`; unbounded ones →
  ordinary Iris `∀`;
- soundness → composition of Iris adequacy with reflection adequacy.

The result is the standard Iris layering with fluid predicates occupying the
pure fragment. Iris is not modified; it is *targeted*. The fluid contract
language and the separation logic meet at exactly one connective, `⌜·⌝`, which
is the boundary between the executable/decidable world (where fluidity lives)
and the quantified/spatial world (where Iris lives).

---

## 10. Heap lifting and the representation functor

How are heap elements lifted into the contract layer, and does every reference
to a heap value need its own type-directed inductively-defined relation?

**Answer: there is always such a relation, but it is ONE generic relation
defined by structural recursion on a reified type code — one clause per type
former, not a bespoke inductive per reference or per concrete type.** References
to a heap value of type `t` reuse `repr t`; nothing bespoke is written at the
use site. This is exactly RustBelt's semantic interpretation of types
(`⟦τ⟧.own`) and the standard Iris `is_list`/`array` family, unified under a type
code.

### 10.1 The representation relation, by recursion on a type code

Reify types as a datatype of **type codes** with a decoder into the pure value
universe:

```
Ty   ::= int | bool | str | list Ty | Ty × Ty | dict Ty Ty | set Ty
⟦·⟧  : Ty → Type          (* decode a code to its pure Coq type *)
⟦int⟧ = Z,  ⟦list t⟧ = list ⟦t⟧,  …
```

Then the heap↔pure relation is **one** function, by recursion on the code, with
exactly one clause per type former (the "representation functor"):

```
repr : ∀ (t : Ty), Loc → ⟦t⟧ → iProp

repr int        l n        ≜  l ↦ #n
repr bool       l b        ≜  l ↦ #b
repr str        l s        ≜  l ↦ #s
repr (t₁ × t₂)  l (x₁,x₂)  ≜  ∃ l₁ l₂, l ↦ (l₁,l₂) ∗ repr t₁ l₁ x₁ ∗ repr t₂ l₂ x₂
repr (list t)   l []       ≜  ⌜ l = null ⌝
repr (list t)   l (x::xs)  ≜  ∃ hd tl, l ↦ (hd,tl) ∗ repr t hd x ∗ repr (list t) tl xs
repr (dict k v) l m        ≜  … structural over the entry list …
repr (set t)    l s        ≜  … structural over the element list …
```

Per type former, one clause — not per reference. The mutable/immutable split
mandated by AGENTS.md (VList *value* vs. heap *representation*) is exactly this
seam: `repr t l x` relates a heap location to the pure value `x` it mirrors.

### 10.2 Systematic lifting of any fluid predicate

Any pure (fluid) predicate `φ : ⟦t⟧ → bool` lifts to a heap predicate
uniformly — no new relation required:

```
Φ(l)  ≜  ∃ x : ⟦t⟧,  repr t l x  ∗  ⌜ R(φ)(x) = true ⌝
```

The spatial conjunct extracts the pure value `x`; the `⌜·⌝` conjunct is the
fluid predicate evaluated on it (§9.1). One scheme covers every predicate over
every type. This is the representation-predicate seam of §9.4 made generic.

### 10.3 The obligations `repr` must satisfy (proved once, generically)

Two properties, both by induction on `t` (one obligation per clause):

1. **Functionality (determinism).** `repr t l x ∗ repr t l y ⊢ ⌜x = y⌝` — a heap
   fragment determines a unique pure value, so "the value `x`" in `Φ(l)` is
   well-defined.
2. **Extraction/adequacy.** `repr t l x ⊢ repr t l x ∗ ⌜x = ⟦read l⟧ᴱ⌝` — the
   recovered pure value agrees with the executable semantics. This is the
   heap-level counterpart of reflection adequacy (§9.7); the two compose.

### 10.4 Where type-direction is complete — and where it stops

- **Tree-shaped (acyclic, unshared) data: complete.** The recursion above plus
  the two generic lemmas lifts *every* heap value of *every* λ_A type with no
  per-reference work. The separating conjunction `∗` enforces sub-structure
  disjointness — exactly the tree assumption.

- **Sharing / aliasing / cycles: NOT type-directed.** If two fields point at the
  same sub-object (a DAG) or the structure is cyclic, `∗`-based `repr`
  over-counts ownership and the clause becomes false. Sharing is a property of
  the value's *identity graph*, not its type, so no amount of type-direction
  recovers it. The fixes:
  - **fractional / read-only points-to** (`↦□`, `↦{q}`): makes `repr`
    persistent, restoring free sharing for *immutable* structures — closing the
    loop with §9.3 (pure ⊆ persistent ⊆ shareable). Right tool for Python's
    frozen/immutable VList snapshots.
  - **ghost names + a graph predicate** with a global footprint, for genuine
    mutable sharing.
  - **guarded recursion (`▷`)** when the ownership predicate itself is
    non-well-founded — the `▷` that §9.5 avoids for *pure* predicates but cannot
    avoid for *recursive ownership*.

**Direct answers.** (1) Every reference reuses the *single* `repr` indexed by a
type code; no bespoke inductive per reference. (2) Lifting is uniform:
`Φ(l) ≜ ∃x. repr t l x ∗ ⌜R(φ)(x)⌝`. (3) The honest caveat: type-direction is
complete only for tree-shaped data; the genuine boundary is **value identity /
sharing**, not type, and it is paid for with fractions / ghost state / guarded
recursion — exactly where the pure-fluid layer hands off to full Iris.

---

## 11. Totality is the domain of reflection

Reflection `R : PyPredicate → CoqTerm` is **partial unless the source is
constrained**, because the kernel *rejects* the output of `R` on any predicate
whose recursion it cannot see as decreasing. There is no "define now, prove
later" escape at definition time: an unguarded `Fixpoint` is not a well-formed
term. So `R` must be a **total function from a restricted source language**, and
that restriction *is* the totality discipline. Reflection failure is
qualitatively worse than proof failure: a proof failure leaves an unproved
goal; a reflection failure means the predicate **has no denotation in the logic
at all**.

```
R is definable  ⟺  every predicate in dom(R) reflects to a guard-passing Fixpoint
```

Hence `R : λ_A^tot → CoqTerm`, where `λ_A^tot` is a decidable, syntactically
checkable total sublanguage of pure Python. The reflection map and the totality
discipline are the same artifact viewed two ways.

### 11.1 Three disciplines (increasing power, increasing cost)

**(D0) Bounded-recursor-only — the safe core (what we have today).**
No user recursion; iteration only via `for x in <finite collection>` /
comprehensions, which reflect to *folds over a concrete list* (`forallb`,
`existsb`, `countb`, `fold_left_acc`, `filterb` in `coq/ListPredicates.v`) —
structural `Fixpoint`s over the iterated structure. Totality is **syntactic and
free**: an O(n) AST check (no `while`, no self-call, every loop ranges over
inductive data). This is exactly the current fragment.

**(D1) Structural recursion — recursion the kernel can see.**
Allow recursive predicates *only* when one argument structurally decreases on
every recursive call, that argument being a syntactic subterm of a
pattern-match scrutinee. `R` emits a guarded `Fixpoint`. The discipline is a
**guardedness check on the Python AST that mirrors Coq's guard condition**, so
that source acceptance ⟹ kernel acceptance. This requires the load-bearing
theorem of §11.4 (the lowering preserves the decrease witness); without it a
source-level guard check is unsound.

**(D2) Well-founded recursion with an explicit measure — opt-in, with an
obligation.** For non-structural predicates (gcd, binary-search-on-indices), `R`
stays total only with a **user-supplied `decreases m` measure** plus a *proof
obligation discharged at reflection time*: `m` strictly decreases in a wf order
on every recursive call. `R` emits `Equations` / `Program Fixpoint` / `Acc`
recursion; the decrease obligations go to the existing 3-tier prover
(lia/SMT/LLM). The obligation is discharged *before* the predicate is usable —
failure ⇒ rejection, not admission.

### 11.2 The totality judgment

Make `R` total-by-construction via a termination-aware judgment `Γ ⊢ t : τ ↓`
("t is well-typed and total"), with `R` defined *exactly* on its derivations:

```
                                  (every loop ranges over inductive data)
  ──────────────────────  (D0)   ────────────────────────────────────────
   Γ ⊢ literal/op : τ ↓           Γ ⊢ for x in (e:list σ): body  : τ ↓

   f∈Σ,  arg_i structurally < scrutinee on each rec call
  ──────────────────────────────────────────────────────  (D1)
   Γ ⊢ f(…) : τ ↓

   m : State→ℕ,   ⊢ m[rec_args] < m[args]   (discharged by prover)
  ────────────────────────────────────────────────────────────────  (D2)
   Γ ⊢ f(…) decreases m : τ ↓
```

Slogan: **`R` is a total function out of the totality judgment, not out of raw
Python.** Raw Python lacking a `↓` derivation is *rejected at the
contract-linter boundary* with a concrete diagnostic ("predicate `p` is
recursive but no decreasing argument / measure found"), never silently
reflected into a malformed term.

### 11.3 Pure totality vs. loop variants vs. measures

The metatheory keeps two layers strictly apart:

| Where | Totality mechanism | Status |
|---|---|---|
| λ_A pure recursion | structural subterm → kernel guard checker (totality *inherited*, not proved) | **complete** (D0) |
| λ_A non-structural pure recursion | well-founded measure into ℕ / wf relation (`Equations`/`Program`/`Acc`) | **not used** — fragment restricted to structural |
| `while` termination | loop *variant* = measure on state, strictly decreasing per iteration | **partial** |

- **λ_A has no `while`.** The pure fragment (§1.1) is variables, literals, ops,
  calls, `if`, `let`, `match` — no loops. Pure recursion is via `Σ` definitions
  only, so the pure layer never needs a loop variant.
- **`while` lives only in the imperative SnakeletIR layer**, and there
  termination is by a well-founded variant — a WP-side obligation, not a
  pure-fragment one. The implemented case is `wp_while_str`
  (`coq/SnakeletExnTactics.v`): a string-guard loop whose body falsifies the
  guard in one step (the well-founded measure), so the loop unfolds finitely
  with **no coinduction / Löb**. General symbolic `while` with a user `decreases`
  variant is **not yet wired** (tests flag `test_while_with_inline_invariant` as
  "needs the per-loop lemma path").
- **Measures** are the unifying mechanism for both non-structural pure recursion
  and loop variants. Today axiomander uses only the *degenerate* (structural)
  measure for pure code and the *guard-falsification* measure for the one
  implemented loop. User-supplied measures (`decreases` clauses, wf recursion)
  are a deliberate, not-yet-taken extension.

### 11.4 Recognizing structural recursion: the slice-to-match problem

**Will normal structural recursion in a Python predicate be noticed under
translation? Today: no — and for two distinct reasons.**

**Detection gap — the recursion isn't recognized as recursion.** The
predicate-expansion path (`contract_linter._expand_predicate`,
`iris_pipeline._subst_params`) is an **inliner**: it substitutes the callee body
into the call site. The only "recursion" the lowering handles is bounded
iteration (`for`/comprehension → recursors) and one imperative special case
(`iris_proof_gen._detect_string_guard`). A self-recursive `def`
(`def is_sorted(xs): … is_sorted(xs[1:])`) either diverges during inlining or
surfaces as an unresolved `OpaqueTerm`. Nothing says "this is a `Fixpoint`, stop
inlining." So genuine structural recursion is **not mistranslated — it is not
translated as recursion at all** (the safe-but-limited failure the totality
discipline predicts).

**Witness gap — Python's decrease idiom ≠ Coq's decrease form.** Even if a
`Fixpoint` were emitted, Python expresses structural recursion through
*indexing/slicing on the same value* (`xs[1:]`, `xs[0]`) — a subscript/`BinOp`
in the IR — whereas Coq's guard checker only accepts decrease on a *syntactic
subterm of a `match` scrutinee*. `Fixpoint f xs := … f (tail xs)` is **rejected**
because `tail xs` is a function application, not a `match`-bound subterm.

**What "noticing" requires — an explicit recursion-recognition pass:**

| Step | What it does | Exists? |
|---|---|---|
| Recursion detection | flag self-calls in a predicate `def` → emit `Fixpoint`, not inline | **no** |
| Slice-to-match reassociation | rewrite `xs[1:]`/`xs[0]` recursion into `match xs with [] => … \| x :: rest => …` so the recursive call lands on `rest` (a real subterm) | **no** |
| Guard-preservation proof | the reassociation preserves the decrease witness through lowering (§11.2 D1) | **no** |
| Measure fallback (D2) | when no subterm can be exposed, demand a `decreases` clause | **no** |

The crux is the **slice-to-match reassociation**: Python's slice-recursion and
Coq's match-recursion are *semantically equal but syntactically incomparable to
the guard checker*. Recognizing "this `xs[1:]` recursion is structural" means
normalizing Python's slice idiom into Coq's match form — a real analysis, plus
the preservation lemma that the reshaping keeps the decrease witness. This is
D1 made concrete: the guard discipline is not merely "check the source
decreases" but "**translate Python's decrease idiom into Coq's decrease
form**," and that translation is itself the recognition pass not yet built.

### 11.5 What we owe

1. **Source-level termination checker** = the decision procedure for
   `Γ ⊢ t : τ ↓` (D0 implicit today; D1 needs explicit guard analysis +
   slice-to-match reassociation on the AST).
2. **Preservation-of-decrease lemma**: lowering preserves the structural/measure
   decrease, so source acceptance ⟹ kernel acceptance. Load-bearing; same
   trusted-or-verified bucket as the §7 elaboration edge.
3. **D2 obligation plumbing**: route `decreases` measures' decrease goals into
   the 3-tier prover; reject on failure.
4. **`while` variant annotation**: general `decreases` on imperative loops,
   decreasing in `<` on ℕ, replacing the single guard-falsification special
   case.

Until these exist, the honest statement is: **`R` is total because `λ_A^tot` is
restricted to D0 (bounded recursors).** Admitting user-recursive predicates (D1)
or non-structural ones (D2) requires promoting the implicit D0 check into the
explicit totality judgment of §11.2 and proving §11.5.2.
