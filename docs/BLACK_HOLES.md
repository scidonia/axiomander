# Reporting Black Holes and Suggesting Post-Black-Hole Asserts
_For Partial WP Analysis with Side Effects and Unknown Segments_

This document extends the **Condition Splitting and Havoc Rules** to explain:

1. How to detect and **report where weakest-precondition (WP) analysis is blocked**.
2. How to compute the **required conditions after a “black hole”** (unknown segment).
3. How to **suggest asserts** that the user can insert after those segments to recover full verification power.

The aim is to guide the user toward adding contracts/assertions so that previously “opaque” regions become locally specified, and the rest of the program can be verified again.

---

## 1. Black Holes

A **black hole** is any code segment that the analyzer cannot model precisely in the WP calculus, such as:

- External calls (I/O, DB, network, system calls)
- Functions without contracts or summaries
- Loops without invariants (and where inference fails)
- Arbitrary Python constructs outside the supported fragment

Formally, a black hole is a contiguous code range `U` with:

- **Entry point**: location `loc_in`
- **Exit point**: location `loc_out`
- **Affected set**: variables `A` that may be modified by `U`
- **Unaffected set**: variables `Ū` that are guaranteed not to be modified

The analyzer treats `U` as a single unknown block with possible havoc on `A`.

---

## 2. Interaction with Postconditions

Suppose we are propagating backwards from a postcondition `Q_exit` that should hold at `loc_out` (just after the black hole).

Using the **condition splitting** rules, we split `Q_exit` into:

- `Q_keep`: conjuncts depending only on `Ū` (unaffected vars)
- `Q_drop`: conjuncts that depend on any variable in `A` (affected vars)

Recall:

- After `U`, we **can still guarantee** `Q_keep` (it depends only on unaffected variables).
- We **cannot guarantee** `Q_drop` because `U` may arbitrarily change its variables.

So, by default:

```text
wp(U, Q_exit) ≈ Q_keep
```

and the analyzer abandons proving `Q_drop` for the rest of the analysis.

However, we can do more: we can **tell the user exactly what conditions must be re-established after the black hole** in order to restore full verification of `Q_exit`.

---

## 3. Required Conditions After the Black Hole

Let:

- `Q_exit = Q_keep ∧ Q_drop`

Intuitively:

> If the user *guarantees* `Q_drop` at `loc_out` (e.g. via an `assert`), then the analyzer can still use the full `Q_exit` for subsequent analysis.

So we define the **required condition after the black hole** as:

```text
RequiredPost(U, Q_exit) := Q_drop
```

That is, we treat `Q_drop` as a *desired assertion* at `loc_out`.

### 3.1 Reporting

For each black hole `U`, the analyzer should record and report:

- `location`: file/line range of `U` (entry and exit positions)
- `affected_vars`: the set `A`
- `unaffected_vars`: the set `Ū`
- `required_post`: the formula `Q_drop`

A human-readable description might be:

> **Black hole at lines [L1–L2]:**
> - This code may modify: `A = { ... }`  
> - These postcondition clauses could not be preserved across it: `Q_drop = { C_i }`  
> - To restore full verification, consider adding an `assert` at line L2+1 equivalent to `Q_drop`.

---

## 4. Suggesting Concrete Asserts

Concretely, if `Q_exit` is a conjunction:

```text
Q_exit = C1 ∧ C2 ∧ ... ∧ Cn
```

and splitting yields:

- `Q_keep = ∧ { Ci | Vars(Ci) ⊆ Ū }`
- `Q_drop = ∧ { Ci | Vars(Ci) ∩ A ≠ ∅ }`

then a natural suggestion is:

```python
# After the black hole (at loc_out)
assert C_i_1
assert C_i_2
...
assert C_i_k
```

for each conjunct `C_i_j` in `Q_drop`.

In other words: **each dropped conjunct becomes a candidate assertion** that the user may enforce explicitly after the unknown block.

### 4.1 Example

Postcondition at exit of U:

```text
Q_exit = (x > 0) ∧ (y == x + 1) ∧ (z >= 3)
```

Black hole `U` may modify `y` but not `x` or `z`:

- `A = {y}`
- `Ū = {x, z, ...}`

We split:

- `x > 0` → uses `x` only → **keep**
- `y == x + 1` → uses `y` → **drop**
- `z >= 3` → uses `z` only → **keep**

So:

```text
Q_keep = (x > 0) ∧ (z >= 3)
Q_drop = (y == x + 1)
```

Analyzer behaviour:

- For WP propagation across `U`, only use `Q_keep`.
- For reporting:
  - Black hole at lines [L1–L2] modifies `y`.
  - We lost the ability to guarantee `y == x + 1`.
  - Suggest:

    ```python
    # Suggested assertion after this block:
    assert y == x + 1
    ```

If the user adds that assertion, the analysis can treat `Q_exit` as fully enforced again.

---

## 5. Multiple Black Holes and Composition

There may be multiple black holes in a function. For each one, the analyzer should:

1. Identify `Q_exit` – the desired postcondition at the black hole’s exit point.
2. Split `Q_exit` into `(Q_keep, Q_drop)` with respect to the affected set at that block.
3. Use `Q_keep` for continued backing propagation.
4. Record `Q_drop` as the suggested assertion(s) at the black hole’s exit.

Because WP propagation is backward, the process is naturally **compositional**:

- Later black holes see postconditions that already reflect earlier losses.
- Each black hole produces its own “recovery” suggestion.

---

## 6. Integrating with Precondition Checking

At the start of the function, the analyzer ultimately computes a (possibly weakened) weakest precondition:

```text
WP(Q_reduced)
```

where `Q_reduced` is the **accumulated** subset of postconditions that survived all black holes (and any other unsupported constructs).

The verification query for a user-declared precondition `P` is:

```text
SAT( P ∧ ¬WP(Q_reduced) )
```

- `UNSAT` → `P` is strong enough to ensure `Q_reduced`.
- `SAT` → counterexample (or model) suggests either:
  - a real bug, or
  - missing assertions / specifications around black holes.

**Important**: the tool must clearly distinguish:

- Properties in `Q_reduced` (actually verified), vs
- Properties in the union of all `Q_drop` (not verified; only suggested).

---

The coding assistant can:

- Surface this to the user: A commented region with the `Q_drop` assert.
- Offer one-click insertion of suggested `assert`s after each black hole location.
- Re-run the analysis after the user accepts or edits those assertions.

---

## 8. Summary of Behaviour for the Agent

When encountering a black hole during WP analysis:

1. **Identify**:
   - the code range (`loc_in`, `loc_out`),
   - the affected set `A`,
   - and the current postcondition `Q_exit`.

2. **Split** `Q_exit` into `Q_keep` and `Q_drop` using variable dependency.

3. **Use** `Q_keep` as the new postcondition for continued backward WP.

4. **Record**:
   - location information,
   - `affected_vars`,
   - `required_post := Q_drop`.
   - `suggested_asserts`: decomposition of `Q_drop` into per-conjunct assertions.

5. **Report** to the user that:
   - “Verification is blocked / weakened here”,
   - “These properties were lost across this segment”,
   - “Adding these assertions after the segment would restore them.”

This preserves soundness while giving practical guidance to enrich the program with local assertions/contracts that make future analyses more powerful.
