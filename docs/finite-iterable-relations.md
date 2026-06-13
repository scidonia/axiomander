# Representation Relations for Finite Iterables

Status: Design — June 2026
Branch: `feature/iris-backend-prototype`

## Goal

Define the **representation relations** that connect Python's finite iterable
types (`list`, `tuple`, `dict`, `set`, `str`, `bytes`) to mathematical models,
and show how each becomes an `Iterable` instance consumable by the `wp_for_fold`
rule from [`generator-specs.md`](generator-specs.md). The central design choice
is the **iteration-order axis**: ordered iterables fold left-to-right over a
`list`-shaped model; unordered iterables fold over a `gset`/`gmap`-shaped model
and require the combining step to *commute*.

## The taxonomy of finite iterables

Every finite iterable Python builtin reduces to one of three shapes:

| Python type | Order semantics | Model type | stdpp/Coq | Duplicates |
|-------------|-----------------|------------|-----------|------------|
| `list` | indexed, ordered | `list val` | `list` | yes |
| `tuple` | indexed, ordered | `list val` | `list` | yes |
| `str` | indexed, ordered | `list ascii` | `string` | yes |
| `bytes`, `bytearray` | indexed, ordered | `list Z` | `list` | yes |
| `dict` | insertion order (3.7+) | `list (K*V)` keyed by `gmap K V` | `gmap` | unique keys |
| `set`, `frozenset` | **unspecified** | `gset val` | `gset` | unique |
| `range` | indexed, ordered | `Z` (degenerate) | `Z` | n/a |

Three structural families:

1. **Ordered-indexed** (`list`, `tuple`, `str`, `bytes`): model is a `list`,
   `uncons` is head/tail, fold is `fold_left` — order matters.
2. **Keyed** (`dict`): model is a `gmap K V`; iteration yields *keys* (or items)
   in insertion order. Spec-able as an ordered `list K` plus the `gmap` for
   value lookup.
3. **Unordered-unique** (`set`, `frozenset`): model is a `gset val`; iteration
   order is **implementation-defined**. A verified loop *cannot* depend on
   order; the fold must be over a commutative monoid.

There are no other finite-iterable builtins. (`frozenset` shares `set`'s model;
`bytearray` shares `bytes`'s model but is mutable — see the mutability axis
below. Generators are covered separately in `generator-specs.md`.)

## Two regimes: structural vs. heap-backed

Per the project ground rules, immutable values are *structural* (the value **is**
the model), while mutable structures have a heap representation that parallels
the value. This gives two definitions of every representation relation:

### Structural (immutable: `tuple`, `frozenset`, `str`, `bytes`, immutable `list`/`dict` reads)

The value carries its model directly. The relation is a *pure equality*, no
separation logic:

```coq
Definition is_list (v : sn_val) (M : list sn_val) : Prop := v = LitList M.
Definition is_set  (v : sn_val) (M : gset sn_val)  : Prop := v = LitSet (elements M).
Definition is_dict (v : sn_val) (M : gmap sn_val sn_val) : Prop :=
  v = LitDict (map_to_list M).
```

`sn_val` already provides `LitList (vs : list sn_val)`, `LitTuple`,
`LitDict (kvs : list (sn_val * sn_val))`, and `LitSet (vs : list sn_val)`, so the
structural relation is a thin wrapper over the existing constructors.

### Heap-backed (mutable: `list.append`, `dict[k]=v`, `set.add`)

The structure lives in the heap and the relation is a separation-logic predicate
threading `pointsto` cells. The model parallels the heap state:

```coq
(* a mutable list as a heap-backed structure; M is its current contents *)
Definition isListHeap (l : loc) (M : list sn_val) : iProp := ...
```

Mutating operations update both the heap and the model in lockstep
(`isListHeap l M ∗ ... ⊢ WP append l x {{ _, isListHeap l (M ++ [x]) }}`).

For **iteration**, the loop reads but does not mutate the iterable, so the
structural (pure) relation is sufficient even for mutable types: snapshot the
contents into a pure model `M` at loop entry and fold over `M`.

## The `Iterable` instances

Recall the typeclass from `generator-specs.md`:

```coq
Class Iterable (H : Type) (M : Type) := {
  repr   : H -> M -> iProp;
  uncons : M -> option (val * M);
}.
```

### Ordered-indexed (`list`, `tuple`, `str`, `bytes`)

```coq
Instance list_iterable : Iterable sn_val (list sn_val) := {
  repr v M := ⌜v = LitList M⌝%I;
  uncons M := match M with [] => None | x :: xs => Some (x, xs) end;
}.
```

Fold is `fold_left`; the loop invariant `P : list sn_val -> iProp` is over the
*remaining* suffix. Induction is on `M`. No Löb, no `▷`.

### Keyed (`dict`)

```coq
Instance dict_iterable : Iterable sn_val (list (sn_val * sn_val)) := {
  repr v kvs := ⌜v = LitDict kvs⌝%I;
  uncons kvs := match kvs with [] => None | (k,_)::r => Some (k, r) end;
}.
```

Iterating a dict yields **keys** in insertion order, so the iteration model is
the ordered association list `kvs` (CPython 3.7+ semantics). Value lookup inside
the body uses the `gmap` projection of `kvs`. If a loop iterates `d.items()`,
`uncons` yields the pair `(k, v)` instead; `d.values()` yields `v`.

### Unordered-unique (`set`, `frozenset`)

```coq
Instance set_iterable : Iterable sn_val (gset sn_val) := {
  repr v S := ⌜v = LitSet (elements S)⌝%I;
  uncons S := match elements S with [] => None | x::_ => Some (x, S ∖ {[x]}) end;
}.
```

**Critical constraint:** because Python's set iteration order is
implementation-defined, the fold rule for sets is *not* `fold_left` — it is
`set_fold` over the `gset`, which is only well-defined (independent of the
enumeration order) when the combining operation forms a **commutative monoid**.
The verification condition for a set loop therefore includes a *commutativity
side-goal*:

```coq
Lemma wp_for_set S (P : gset sn_val -> iProp) body :
  (* the per-element step commutes: order of consumption is irrelevant *)
  (forall x y consumed, P consumed -∗ WP body[x];body[y] {{ _, R }}
                     ⊣⊢ P consumed -∗ WP body[y];body[x] {{ _, R }}) ->
  P ∅ -∗
  (forall x S', x ∉ S' -> P S' -∗ WP body[x] {{ _, P ({[x]} ∪ S') }}) -∗
  WP (for x in <set>: body) {{ _, P S }}.
```

In practice the pipeline discharges commutativity automatically when the body's
effect is itself an `gset`/`gmultiset` accumulation (e.g. `result.add(f(x))`),
and *rejects* a set loop whose body has order-dependent effects (e.g. appending
to a list), pointing the user at the order-dependence as the failure cause.

## Why this unifies with `range` and generators

- `range(n)` is the `Iterable Z Z` instance with `repr ≡ emp` and
  `uncons i = if i < n then Some (i, i+1) else None`. It is the degenerate
  ordered-indexed case with an empty representation.
- A finite generator (`generator-specs.md`) is the `list` instance with
  `repr = genRepr g M`; its `produces(g, count)` clause is just the assertion
  that `length M = count`.

So `list`, `tuple`, `dict`, `range`, and finite generators all share the
`fold_left` rule; only `set`/`frozenset` need the commutative `set_fold`. One
`wp_for_fold` lemma plus one `wp_for_set` lemma cover every finite iterable.

## Mathematical models map to stdpp

The Iris standard library (`stdpp`) supplies exactly the model types needed,
each with mature induction and fold principles:

| Model | stdpp type | Fold principle |
|-------|------------|----------------|
| ordered sequence | `list` | `fold_left`, `list_ind` |
| finite map | `gmap K V` | `map_fold`, `map_ind` |
| finite set | `gset K` | `set_fold`, `set_ind` |
| finite multiset | `gmultiset K` | `gmultiset_ind` (if duplicates-without-order ever needed) |

`SnakeletLang` already imports `stdpp.gmap`; adding `gset`/`gmultiset` is a
one-line `Require`.

## The contract surface for iterables

Mirroring `GeneratorSpec`, an iterable argument can carry a contract that a loop
consumes. For a list parameter:

```python
def process(xs):
    # requires: is_list(xs, M) and len(M) == n
    # requires: forall i, 0 <= i < n -> P(M[i])
    ...
```

- `is_list(xs, M)` binds the pure model `M`.
- The element predicate `P` is injected per iteration, exactly as for
  generators.
- The accumulator invariant remains the user's responsibility.

The set/dict analogues use `is_set(xs, S)` / `is_dict(xs, KV)` and quantify over
membership rather than indices.

## Implementation order

1. **`list` instance + `wp_for_fold` over `list`** — validates the ordered case
   against the simplest non-degenerate model. (Range already validates the
   degenerate case.)
2. **`dict` instance** — ordered association-list model + `gmap` lookup for the
   body.
3. **`set` instance + `wp_for_set`** — the commutative-monoid fold, with the
   commutativity side-goal and the order-dependence rejection check.
4. **`str`/`bytes`** — reuse the `list` instance with element type `ascii`/`Z`.
5. **Contract surface** — `is_list`/`is_set`/`is_dict` clauses in the
   ContractLinter, lowered to the pure model bindings.

## Open questions

- **Mutation during iteration.** Python forbids (or warns on) mutating a
  collection while iterating it. The snapshot-at-entry model assumes no
  mutation; detecting/forbidding in-loop mutation of the iterated structure is a
  separate static check.
- **Insertion-order trust for `dict`.** The ordered-`dict` model relies on
  CPython 3.7+ insertion-order semantics. If a target runtime does not guarantee
  this, `dict` collapses to the unordered `set`-style fold over keys (with the
  commutativity constraint). This should be a configuration flag, not a silent
  assumption.
- **`elements` canonical order for `gset`.** stdpp's `elements` gives *a*
  deterministic order, but it is not Python's. The `set_iterable` instance must
  never let that order leak into a provable fact — enforced by routing all set
  loops through `wp_for_set` (commutative) rather than the `list` fold.
