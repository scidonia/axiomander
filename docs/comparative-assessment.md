# Comparative Assessment: Axiomander vs Dafny, Nagini, Liquid Haskell, F*

A critical assessment of Axiomander's verification approach against four
established systems. The goal is honest critique, not promotion: where the
design is defensible, where it overclaims, and what the highest-value
investments are.

---

## 1. Where Axiomander sits in the design space

The four reference systems cluster along two axes — **trust base** (SMT-only
vs proof-term producing) and **language strategy** (bespoke language vs
checker on an existing language):

```
                  bespoke language          existing language
                ┌──────────────────────┬──────────────────────┐
  SMT-only      │ Dafny                │ Nagini (Python)      │
  (trust Z3)    │ (Boogie → Z3)        │ Liquid Haskell (GHC) │
                ├──────────────────────┼──────────────────────┤
  proof-term    │ F* (SMT + Meta-F*)   │ Axiomander           │
  producing     │                      │ (Python, Coq kernel) │
                └──────────────────────┴──────────────────────┘
```

Axiomander occupies an under-explored quadrant: a checker for an *existing
dynamic language* that produces *kernel-checked proof terms*. No comparator
is there. Nagini is the closest peer (Python + separation logic) but trusts
Z3/Viper end-to-end with no independent check. That positioning is the single
most defensible thing about the project.

---

## 2. Strengths

### 2.1 Smallest trust base for the WP layer

Dafny, Nagini, and Liquid Haskell all trust Z3 with no independent check — a
Z3 soundness bug silently invalidates every proof. Axiomander's WP calculus
is proven sound in Coq, and every discharged obligation is re-checked by the
Coq kernel. This is the same guarantee F* gives for its tactic-proved goals,
but for the entire pipeline rather than a fragment.

### 2.2 The LLM-oracle tier is a real contribution, and it is sound

The usual objection to "an LLM proves it" is unsoundness. Axiomander defuses
that completely: the LLM only *proposes* a Coq script; the kernel decides.
You get SMT-beating reach (induction, nonlinear arithmetic, data-structure
lemmas) with zero soundness cost. None of the four comparators have this. The
cost is reproducibility/latency, not correctness.

The correct framing is **not** "AI proves theorems" (which invites soundness
skepticism) but "**SMT-beating proof search that is sound by kernel
re-checking.**" That framing is bulletproof and the comparators cannot match
it.

### 2.3 Zero-import contracts

Nagini *requires* `from nagini_contracts import *`; the source no longer runs
as ordinary Python without the shim. Axiomander's docstring/assert contracts
keep the program dependency-free. Strictly better ergonomics for adoption.

### 2.4 Structural immutable values

The VList/VTuple/VDict-as-structural, mutation-on-heap split mirrors Dafny's
`seq` vs array and F*'s `list` vs `LowStar.Buffer`. The right call, already
in place.

---

## 3. Weaknesses and risks

### 3.1 The translation gap is the theoretical Achilles heel

Python → PyIR → SnakeletIR → ANF → Coq is **trusted and unverified**. A bug
in the lowerer means you prove a theorem about a *different program* than the
one that runs. This is the same hole Nagini has (Python → Viper encoding is
trusted), so Axiomander is not worse than its closest peer — but it markets
itself as "Coq is the trust base," and that claim is only true *below* the IR
boundary.

- **Dafny / F\*** sidestep this by being their own languages — what you
  verify is what runs (modulo extraction, which F* addresses with verified
  extraction in Low*).
- **Liquid Haskell** sidesteps it because refinements are elaborated *within*
  GHC's type system — the "translation" is type checking, not a separate
  trusted compiler.

**Recommendation:** highest-value theoretical investment. Either (a) extract
the lowerer from a Coq definition (à la CompCert), or (b) build a *validator*
that checks each lowering instance against a reference semantics (translation
validation — much cheaper than full verification; CompCert uses it for
register allocation). The current "Python→IMP translator is trusted (or
extractable from Coq later)" in AGENTS.md is doing load-bearing hand-waving.

### 3.2 Predicate lifting is ad-hoc

`detect_loop_pattern` → `forallb`/`existsb`/`countb` **pattern-matches
specific loop shapes** and emits Coq as strings. Compare:

- **Liquid Haskell** has *measures* and *refinement reflection*: any
  terminating Haskell function is automatically lifted into the logic, and
  PLE (Proof by Logical Evaluation) unfolds it. Principled, total,
  compositional.
- **F\*** — functions *are* logic; no lifting needed.
- **Dafny** — `function` definitions are directly usable in specs; recursion
  handled by SMT encoding + fuel.

Axiomander's combinator matching is brittle: it works for
`for x in xs: if p(x): return True` but breaks on the same predicate written
with a `while`, an accumulator with two updates, a `break`, a non-`Z`
element type, or a body that calls another predicate. See §5 for the detailed
analysis and fix.

### 3.3 Method-level Hoare triples are less compositional than refinement types

Liquid Haskell's `{v:Int | v > 0}` flows through composition automatically.
Axiomander's contracts are per-function pre/post pairs; intermediate values
need explicit `assert`s to thread facts. For straight-line code this is fine;
for deeply nested pure expressions it is more annotation burden than LH or F*.
This is an inherent consequence of choosing Hoare logic over refinement
types — the right choice for imperative Python with mutation, but the pure
fragment would be lighter under a refinement discipline.

### 3.4 Coverage is early-stage

Dafny verifies real data-structure libraries; F* verifies HACL* (production
crypto); Nagini handles inheritance, generics, and IO traces. Axiomander
proves an integer/bool/string/list fragment with single loops. The
architecture is sound; the *coverage* is a research prototype. Any external
comparison must lead with "comparable trust model, far smaller language
fragment," or it reads as overclaiming.

### 3.5 SMT is still in the loop and inherits its brittleness

Level 2 is coq-hammer → cvc4/eprover. Hammer reconstruction failures, ATP
timeouts, and `Z.of_nat`/`nth`/`length` opacity are the same brittleness
Dafny/Nagini/LH suffer. The Coq re-check makes failures *safe* (a bad proof
is never accepted) but not *rare*. The LLM tier is the hedge against this,
trading determinism for reach.

---

## 4. Per-system scorecard

| Dimension | Dafny | Nagini | Liquid Haskell | F* | Axiomander |
|---|---|---|---|---|---|
| Trust base | Z3 | Z3 + Viper | Z3 | Z3 + kernel + extraction | Coq kernel (below IR); trusted lowerer (above) |
| Proof terms | No | No | No | Partial | Yes (kernel-checked) |
| Target language | bespoke | Python | Haskell | bespoke | Python (zero-import) |
| Predicate lifting | `function` + fuel | predicates | measures/reflection (principled) | native | pattern-matched recursors (brittle) |
| Heap reasoning | dynamic frames | separation logic | n/a (pure) | monadic/separation | Iris separation logic |
| Automation | high | high | high | medium | high (SMT) + novel LLM tier |
| Compositionality | method-level | method-level | type-level (high) | type-level (high) | method-level |
| Maturity / coverage | production | research | production-ish | production (crypto) | early prototype |
| Novel contribution | — | Python + SL | refinement reflection | dependent + effects | sound LLM oracle + Coq-checked Python |

---

## 5. Deep dive: why predicate lifting is brittle, and the fix

### 5.1 Five concrete failure modes (grounded in `predicate_lowering.py`)

**(1) Exact-shape matching.** The existsb detector requires this precise tree:

```python
for x in xs:
    if p(x):
        return True   # exactly one stmt; value exactly True
return False
```

Every equivalent predicate silently falls through to `NONE`:
`if p(x): return 1` (value not `True`); `if p(x): found = True; ...`
(two statements); `while` loops (`_classify_while_loop` returns NONE);
`break`-based loops. The advertised `forallb` pattern is **not even
implemented** — only existsb and fold_left exist.

**(2) Invalid Coq from strings.** `_py_expr_to_coq`'s fallback is
`ast.unparse(node)` — Python syntax masquerading as Coq:

```
item.balance > 0   →  (fun item => Z.gtb item.balance 0)   # .balance isn't Coq
f(item) > 0        →  (fun item => Z.gtb f(item) 0)        # f(item) isn't Coq
```

This is exactly the failure AGENTS.md forbids: *"Never use regex on
parse-tree strings."* Here Coq is built by string templating over
un-type-checked AST fragments.

**(3) `Z`-only assumption.** `_extract_lambda` hardcodes `Z.eqb`, `Z.gtb`,
`Z.ltb`. A predicate over strings or bools emits `Z.eqb` on non-`Z` values →
type error. No type information flows in, because the lambda is built from raw
AST, not the typed IR.

**(4) No composition.** `is_permutation` calling `count_item` is impossible:
`_extract_lambda` only turns a single `ast.Compare` into a lambda.

**(5) The lifted form is never checked against the function.** The pattern
matcher *guesses* a Coq lambda and trusts it. A mis-rendered `item != x`
proves a theorem about a *different predicate* than the Python defines, with
no error. Unsound-by-sloppiness, not by design — but the effect is the same.

### 5.2 Root cause

It is a **syntactic pattern matcher that reconstructs semantics from AST
shapes and emits Coq as strings.** Structurally the wrong architecture —
brittle for the same reason a regex parser is brittle: it enumerates surface
forms instead of processing meaning. The irony: the rest of Axiomander does
this correctly. PyIR → SnakeletIR lowers for-loops to `SFor`, comparisons to
`SBinOp`, calls to `SApp`, with types attached, producing real Coq terms.
`predicate_lowering.py` is a parallel, inferior, string-based reimplementation
of lowering the project otherwise avoids.

### 5.3 The fix: reflection, not pattern-matching

Lower the predicate's body through the same IR the verifier already uses,
producing a Coq `Fixpoint`, then inline calls to that Fixpoint in contracts.
This is what Liquid Haskell's refinement reflection and Dafny's `function`
do.

```
def is_hex(s: str) -> bool:        Reflection:
    for c in s:                      PyIR → SnakeletIR (existing) → Coq Fixpoint
        if c not in HEX:               Fixpoint is_hex (s:string) : bool := ...
            return False             is_hex(result) → (is_hex result = true)
    return True
```

| Failure mode | How reflection fixes it |
|---|---|
| Exact-shape matching | IR lowerer handles `if`/`return`/`while`/`break`/accumulators generically |
| Invalid Coq strings | IR emits real Coq via `to_coq()`, type-carrying, never string-templated |
| `Z`-only | IR carries types; `is_hex` over `string` lowers correctly |
| No composition | A predicate calling another lowers the call as `SApp` — free |
| Unchecked lifted form | The Fixpoint *is* the lowered function; verify it (termination + contract). Lifted form equals verified form by construction |

**Recursors become an optimization, not the foundation.** When the lowered
Fixpoint matches `match xs with [] => true | x::r => p x && rec r`, rewrite it
to `forallb p xs` to inherit pre-proved lemmas. Unrecognized shapes still get
a working Fixpoint. You never *depend* on recognizing the shape.

**Termination is the one genuinely new obligation.** Coq `Fixpoint` needs a
decreasing argument. For `for c in s` / `for x in xs` this is structural
(recurse on the tail) — trivially accepted. For `while` loops you need a
measure, which is *correctly* harder, not brittle. Reject `while`-based
predicates with a clear "add a `decreases` measure" message rather than
silently returning `NONE`.

---

## 6. Bottom line

The thesis is sound and the quadrant is real: "kernel-checked proofs for
ordinary Python, with an LLM tier that is sound by construction" is a novel
position no comparator occupies. Lead with that.

Two investments determine whether it is a research prototype or a serious
tool:

1. **Close the translation gap.** Until the Python→IR lowerer is verified or
   translation-validated, the "Coq is the trust base" claim is half-true, and
   any sophisticated reviewer will press on it. This is the difference between
   "Nagini but with proof terms for the easy part" and "the first
   end-to-end-trustworthy Python verifier."

2. **Make predicate lifting principled, not pattern-based.** Reflection of
   arbitrary terminating pure functions into Coq Fixpoints should be the
   *architecture*; the recursor combinators a mere optimization. Liquid
   Haskell is the model to study.

The LLM oracle is the genuine differentiator — framed precisely as sound
proof search, it is unmatchable by the comparators.
