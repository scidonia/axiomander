# Condition Splitting and Havoc Rules
_For Partial Weakest-Precondition (WP) Analysis with Side Effects_

This document defines how the analysis should behave when it encounters
code that cannot be fully translated into weakest-precondition form,
such as unknown side effects, external calls, or loops without invariants.

The goal is to still prove **some** properties soundly by:
- **Havoc-ing** variables that might be affected, and
- **Preserving** conditions that only depend on variables known to be unaffected.

We always prefer **sound overcomplete verification** to unsound claims.

---

## 1. Terminology

- **State variables**: program variables symbolically tracked by the analysis.
- **Postcondition** `Q`: the logical formula we want to hold after a code fragment.
- **WP fragment**: weakest precondition as computed so far for a suffix of the code.
- **Unknown block** `U`: a piece of code we cannot (or choose not to) model precisely:
  - I/O, DB calls, network
  - calls into unknown libraries
  - loops without invariants
  - any construct not in the trusted WP fragment
- **Affected set** `A`: variables that `U` may modify.
- **Unaffected set** `Ū`: variables that `U` is guaranteed not to modify.

We assume the agent can compute (or approximate) a set `A` and therefore `Ū` for each unknown block.

---

## 2. High-level Strategy

Given a postcondition `Q` and an unknown block `U`:

1. **Split** `Q` into:
   - `Q_keep` – part that depends only on variables in `Ū` (unaffected)
   - `Q_drop` – part that depends on any variable in `A` (potentially affected)

2. **Preserve** `Q_keep` by continuing WP over it.

3. **Handle** the affected variables by **havoc**:
   - treat them as arbitrarily changed by `U`
   - do not rely on `Q_drop` anymore (it is no longer guaranteed)

4. The resulting precondition is a **sound over-approximation**:
   - It may be stronger than necessary.
   - It must not be weaker than the true weakest precondition for `Q_keep`.

This allows the analyzer to still prove properties about variables not affected by side effects, while avoiding unsound claims about affected variables.

---

## 3. Condition Splitting

### 3.1 Variable dependency analysis

For each formula `F` (e.g. a boolean combination of atomic predicates), compute:

- `Vars(F)` = set of variables that syntactically occur in `F`.

Given an unknown block with affected set `A` and unaffected set `Ū`:

- A subformula `F` is **safe to keep** if `Vars(F) ⊆ Ū`.
- A subformula `F` is **unsafe to keep** if `Vars(F) ∩ A ≠ ∅`.

### 3.2 Structural splitting of Q

Assume `Q` is in some boolean normal form (or any AST with `and`, `or`, `not`, etc.).

We define a function:

```text
split(Q, A) -> (Q_keep, Q_drop)
```

that returns:
- `Q_keep`: conjunction of all safe conjuncts
- `Q_drop`: everything else (possibly for warning / reporting)

A simple version for conjunctive postconditions:

If:

```text
Q = C1 ∧ C2 ∧ ... ∧ Cn
```

Then:

- For each `Ci`:
  - if `Vars(Ci) ⊆ Ū` → put `Ci` into `Q_keep`
  - else → put `Ci` into `Q_drop`

So:

```text
Q_keep = ∧ { Ci | Vars(Ci) ⊆ Ū }
Q_drop = ∧ { Ci | Vars(Ci) ∩ A ≠ ∅ }
```

If `Q` has disjunctions, the analysis can either:
- Normalize to CNF and apply the same rule per clause, or
- Use a more precise symbolic splitting (optional, more complex).

For an initial implementation it is acceptable to require `Q` to be in conjunctive form for splitting.

---

## 4. Havoc Semantics for Affected Variables

When encountering an unknown block `U` with affected set `A`:

- Conceptually, `U` can arbitrarily change any variable in `A`.
- This is modeled by **havoc**.

### 4.1 Havoc rule

For a single variable:

```text
wp(havoc x, Q) = ∀x'. Q[x := x']
```

For a set of variables `A = {x1, ..., xk}`:

```text
wp(havoc A, Q) = ∀x1' ... ∀xk'. Q[x1 := x1', ..., xk := xk']
```

In practice, this often makes `Q` very strong or unsatisfiable unless `Q` does not depend on those variables.

Because of this, we only apply havoc to the **affected** part of the state, and we only keep those pieces of `Q` that do not mention affected variables.

### 4.2 Practical approximation

Instead of computing the full quantified `wp(havoc A, Q)`, we do:

1. Split `Q` into `(Q_keep, Q_drop)` using variable dependency.
2. For the unknown block, define:

```text
wp(U, Q) ≈ Q_keep
```

where:

- `Q_keep` only depends on unaffected vars (`Ū`),
- `Q_drop` is no longer enforced after `U`.

This is sound because any condition that depends on `A` is not guaranteed after arbitrary changes to `A`.

If the user wants, `Q_drop` can be reported as “properties not checked due to side effects”.

---

## 5. Examples

### 5.1 Simple example

Postcondition:

```text
Q = (x > 0) ∧ (y == x + 1) ∧ (z >= 3)
```

Unknown block `U` might modify `y` but not `x` or `z`:

- `A = {y}`
- `Ū = {x, z, ...}`

Compute:

- `Vars(x > 0) = {x}` → safe
- `Vars(y == x + 1) = {x, y}` → contains `y` (affected) → unsafe
- `Vars(z >= 3) = {z}` → safe

Thus:

```text
Q_keep = (x > 0) ∧ (z >= 3)
Q_drop = (y == x + 1)
```

We then define:

```text
wp(U, Q) ≈ Q_keep = (x > 0) ∧ (z >= 3)
```

After `U`, we no longer claim `y == x + 1` holds, but we **do** preserve the relations on `x` and `z`.

### 5.2 Completely affected condition

If `Q = (y == x + 1)` and `A = {y}`, then:

- `Vars(Q) = {x, y}` → intersects `A` → unsafe.

Thus:

```text
Q_keep = True       # empty conjunction
Q_drop = (y == x + 1)
```

Effectively, after `U` we do not enforce any part of `Q`. The analyzer should classify the result as
“no postcondition preserved across this unknown block”.

---

## 6. Loops Without Invariants

For a loop without a known invariant:

```python
while B:
    body
```

If the analyzer cannot infer an invariant, treat the loop as an **unknown block**:

1. Compute a (possibly conservative) affected set `A_loop`:
   - All variables written in the loop header and body.
2. Apply the same splitting and havoc logic as above:
   - Split `Q` into `(Q_keep, Q_drop)` based on `A_loop`.
   - Define:

     ```text
     wp(while B: body, Q) ≈ Q_keep
     ```

   - Optionally, mark this as **partial verification** and report which parts of `Q` were dropped.

This ensures we do not claim properties about variables that may be arbitrarily changed by an unverified loop.

---

## 7. Using the Resulting Precondition

After applying the above rules, the analyzer obtains a **reduced** postcondition `Q'` (typically `Q_keep` accumulated through multiple unknown blocks).

The backwards WP propagation then proceeds as usual on `Q'`:

1. Compute a weakest precondition `WP(Q')` for the remaining, analyzable code.
2. To check a declared precondition `P`, query the SMT solver with:

   ```text
   SAT( P ∧ ¬WP(Q') )
   ```

   - If **UNSAT** → `P` is strong enough to ensure `Q'` (but **only** `Q'`).
   - If **SAT** → either a real bug or insufficient/over-pessimistic modeling.

3. Clearly communicate to the user that only `Q'` was proven; the dropped parts `Q_drop` were not checked due to side effects / unsupported constructs.

---

## 8. Summary of Implementation Rules

When encountering an unknown block `U`:

1. **Determine affected variables** `A` and unaffected `Ū`.
2. **Split** the current postcondition `Q` into:
   - `Q_keep`: depends only on `Ū`,
   - `Q_drop`: depends on at least one variable in `A`.
3. **Replace** `Q` with `Q_keep` for further WP propagation.
4. **Record** `Q_drop` for reporting (“not verified due to side effects/loop”).

This policy is:

- **Sound**: never proves more than is justified.
- **Useful**: still proves properties for unaffected state.
- **Composable**: can be applied repeatedly across multiple unknown blocks.
