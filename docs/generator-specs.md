# Generator Specifications and Loop Integration

Status: Design — June 2026
Branch: `feature/iris-backend-prototype`

## Goal

Make Python `for` loops over **generators** (and other iterables) verifiable
through the Iris backend by giving each iterable a contract that a loop can
*consume* to auto-generate a sensible proof obligation. The design unifies
range loops, list iteration, and generator consumption under a single
fold-based verification rule, while keeping a sound, explicit boundary between
finite (decidable) and potentially-infinite (coinductive) iteration.

## Background: the two complexity classes

Iteration in Axiomander splits along a single axis — whether the loop has a
*decreasing measure*:

| Class | Examples | Machinery |
|-------|----------|-----------|
| **Bounded / decreasing measure** | `range(n)`, finite lists, finite generators | pure induction, no `iLöb`, no `▷` |
| **Unbounded production** | `while True`, lazy/infinite generators, cyclic structures | `iLöb` + `▷` (the symbolic-`while` path) |

The symbolic `while` loop already lives in the second class and is handled by
the per-loop `iLöb`-based lemma (`loop_inv_<fn>_<id>`). Generators that are
*finite* belong in the first class and should reuse the much cheaper fold rule
rather than the Löb machinery. The contract design below makes a generator
*declare* which class it is in, and the pipeline refuses to silently assume
finiteness.

## Core idea: representation predicates + induction on the model

The standard Iris technique is to connect a heap (or runtime) structure to a
*mathematical model* via a **representation predicate**, then do induction on
the pure model rather than the heap. A `for` loop is **always** a fold over the
model, regardless of the concrete structure:

```coq
Lemma wp_for_fold {M : Type} (model : M)
    (repr : heap_val -> M -> iProp)   (* connects runtime value to model *)
    (uncons : M -> option (val * M))  (* the model's destructor *)
    (P : M -> iProp)                  (* invariant over the remaining model *)
    body :
  P model -∗
  (forall m x m', uncons m = Some (x, m') ->
     P m -∗ WP body[x] {{ _, P m' }}) -∗
  WP (for x in <iter>: body) {{ _, P model_empty }}.
```

The iterables instantiate one typeclass:

```coq
Class Iterable (H : Type) (M : Type) := {
  repr   : H -> M -> iProp;
  uncons : M -> option (val * M);
}.
```

| Iterable | Model `M` | `repr` | `uncons` |
|----------|-----------|--------|----------|
| `range(lo, hi)` | `Z` (current index) | `emp` (degenerate) | `i ↦ (i, i+1)` while `i < hi` |
| `list` | `list val` | `isList l xs` | head/tail split |
| `dict` | `gmap K V` | `isMap m kv` | `gmap` pop |
| finite generator | `list val` | `genRepr g xs` | head/tail split |

The **range loop is the degenerate instance**: `repr ≡ emp`, `M = Z`, measure
`hi - i`. Everything else differs only in `(model, repr, uncons)`. Implement
`wp_for_fold` once; range/list/dict/generator are instances.

## Generator contracts: the consumable surface

A generator is just a function returning an iterable. It maps onto the existing
opaque/transparent call machinery. An **opaque generator** exposes a contract
that a loop consumes; a **transparent generator** has its model derived from the
`yield` sequence in its body.

### Minimal opaque contract

A consumable generator contract needs exactly two clauses:

```python
def gen(n):
    # ensures: produces(result, n)              -- yields exactly n elements
    # ensures: element(result, i) satisfies P(i) -- the i-th element satisfies P(i)
    ...
```

- `produces(result, count)` supplies the **finiteness measure** (becomes the
  `hi` of a range). This is the clause that *asserts* the generator is finite.
- `element(result, i) satisfies P(i)` supplies a **per-iteration assumption**
  the loop body may use about the bound variable `x`.

Both are pure facts about a model, discharged when the generator itself is
verified (the existing `gen_table_total` totality lemma forces the callee to
realize its post).

### The IR addition

In `OpaqueSpec` terms, a generator spec is a new table entry kind:

```python
@dataclass
class GeneratorSpec:
    """Contract for an opaque generator: count + indexed element predicate."""
    count: str          # Coq Z expression: number of elements produced
    elem_pred: str      # Coq Prop over (i, args): the i-th element's property
    args: list[str]     # generator argument names (for count/elem_pred scope)
```

This sits alongside `OpaqueSpec` and `TransparentDef` in the `FunTable`.

## What the loop supplies vs. what the generator supplies

The honest boundary: the generator contract gives the **input structure**, but
it cannot give the **accumulator invariant** — what the loop *computes*. That
comes from the loop's own annotation (a body `assert` or the function
postcondition). Auto-generation is a *combination*:

```
loop_invariant(i, acc)       ← from the loop's own contract (user-written)
∧ element(gen, i) sat P(i)    ← from the generator contract (auto-injected)
```

- **Pure side-effect loop** (no accumulator): `loop_invariant ≡ emp`, fully
  automatic — the user writes nothing.
- **Accumulating loop**: the user annotates the loop invariant once, exactly as
  for any Hoare-logic loop. The generator's `P(i)` is injected for free.

## Lowering `for x in g(): body`

When the lowerer sees `for x in g(): body` where `g ∈ table` is a
`GeneratorSpec`:

1. **Desugar to a counted range** using `produces(g, count)`:
   ```
   _x_i = 0
   while _x_i < count:
       x = element(g, _x_i)     # bind loop var to the i-th element
       <assume P(_x_i)>          # inject the element predicate as a hypothesis
       body
       _x_i += 1
   ```
2. **Emit `wp_for_fold`** with `model = Z`, `repr ≡ emp`, measure
   `count - _x_i`. The per-iteration step gets `⌜P(_x_i)⌝` in its context.
3. **Thread the loop invariant** (from the loop annotation, or `emp`) as `P` in
   `wp_for_fold`.

No coinduction, no `iLöb`, no `▷` — because `produces(g, count)` *asserts
finiteness as part of the contract*, discharged when the generator is verified.

## The finite/infinite gate

The annotation direction matters for soundness. The default is **derive
finiteness or fail**, never **assume finiteness**:

1. **Transparent generator**: try to derive a finite `list` model from the
   `yield` sequence. Succeeds for straight-line `yield`s or a loop with a
   decreasing measure. The derived model collapses to `wp_for_fold`.
2. **Derivation fails** (unbounded `while True: yield ...`): the pipeline
   *requires* an explicit escape-hatch annotation:
   ```python
   # axiomander: coinductive(gen)
   ```
   This switches to a `stream` model + the `iLöb`/`▷` path (the symbolic-`while`
   infrastructure). It is a *forced acknowledgement* that you have left the
   decidable-finite fragment, not an optional opt-in.

## Soundness invariant

The single rule that keeps the system sound:

> `produces(g, count)` must be a postcondition the generator *proves*, never a
> free axiom. Finiteness is either **proven** by the generator (transparent /
> verified opaque) or **explicitly trusted** at an unverified boundary (same
> status as any opaque callee contract). It is *never silently assumed* by the
> loop.

Why this is safe even when wrong:

- If a generator declared `produces(g, count)` is actually infinite and the
  contract is *derived*, the proof of `produces` simply fails — the user cannot
  construct it.
- If the contract is *trusted* (third-party generator), `produces` has the same
  trust status as any opaque contract, recorded explicitly.
- Under partial correctness (Axiomander's `WP {{ Φ }}` is partial), an actually
  infinite generator under a finite model is *vacuously* fine — the loop never
  terminates, so the postcondition is never claimed. The protection holds only
  because the model is derived, not assumed.

## Implementation order

1. **`wp_for_fold`** over the `Iterable (H M)` typeclass — prove once. `range`
   as the degenerate instance (`repr ≡ emp`, `model = Z`, measure `hi - i`). No
   Löb.
2. **`list` instance**: `isList l xs`, `uncons` on `xs`. Induction on `xs`.
3. **`GeneratorSpec`** table entry + `for x in g()` lowering that desugars to a
   counted range and injects `⌜P(i)⌝` per iteration.
4. **Transparent finite-generator lowering**: walk the `yield`s, build the list
   model, emit `wp_for_fold`.
5. **`# axiomander: coinductive(gen)` gate**: when finiteness cannot be derived,
   require the annotation and route to the `stream`/Löb path.

## Relationship to existing work

- **Range loops** become the first `Iterable` instance — they validate the
  `wp_for_fold` lemma with the simplest model.
- **Symbolic `while`** (already shipped) remains the home for unbounded
  production. Generators only join it via the `coinductive` gate.
- **Opaque/transparent calls** already provide the trust infrastructure;
  generator specs are `FunSpec`-style postconditions lifted to "produces this
  sequence." The `gen_table_total` lemma already forces realization.

## Open questions

- **Indexed vs. relational element predicates.** `element(g, i) sat P(i)` is the
  closed-form (indexed) model. Some generators are better described relationally
  (`yields(g, prev, next)`). Whether to support both, or canonicalize to the
  indexed form, is undecided.
- **Early exit (`break`).** A `for` loop with `break` does not consume the full
  model. The fold rule needs a `break`-aware variant that proves the
  postcondition for any prefix of the model. Out of scope for the first cut.
- **`zip`, `enumerate`, comprehensions.** These are compositions of `Iterable`
  instances. Whether they get derived instances automatically or require
  hand-written `Iterable` proofs is a follow-up.
