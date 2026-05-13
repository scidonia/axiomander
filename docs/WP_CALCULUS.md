# Weakest Precondition Calculus

## Hoare Triples

```
{P} c {Q}
```

where `P` is the precondition, `c` is a command, and `Q` is the postcondition.

Meaning: if `P` holds before executing `c`, and `c` terminates, then `Q` holds afterwards.

## Weakest Precondition

`wp(c, Q)` is the weakest predicate `P` such that `{P} c {Q}`.

### Definition (structural)

```
wp(skip, Q)       = Q
wp(x := e, Q)     = Q[x ↦ e]
wp(c1; c2, Q)     = wp(c1, wp(c2, Q))
wp(if e then c1 else c2, Q) = (e → wp(c1, Q)) ∧ (¬e → wp(c2, Q))
wp(while e inv I do c, Q)   = I
```

For `while`, the WP doesn't capture the loop semantics directly — instead, we use the invariant `I` and generate verification conditions:

```
VC1: I ∧ ¬e → Q           (invariant + exit condition implies postcondition)
VC2: I ∧ e → wp(c, I)     (invariant preserved by loop body)
```

### Soundness

```
{P} c {Q}  ↔  (∀ s. P s → wp c Q s)
```

Proved by induction on the structure of `c`.

## Verification Condition Generation

For a function `f(x)` with precondition `P`, postcondition `Q`, and body `c`:

The top-level proof obligation is:

```
∀ x. P(x) → wp(c, Q(result ↦ f(x)))
```

For bodies with loops, we additionally generate the invariant VCs.
