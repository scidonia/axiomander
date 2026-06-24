# Predicate Lifting Plan — Pure Python Functions as Contract Vocabulary

## Goal

Let users write pure Python functions (no side effects, no heap mutations,
no opaque calls) and use them as contract predicates in `requires`/`ensures`
clauses.  The verifier lifts the function's lowered Coq form into the contract
language and inlines it at call sites.

## Architecture Overview

```
  Python source
        │
        ├─ 1. Purity check     (purity_analyzer.py, already exists)
        ├─ 2. Loop detection   (predicate_lowering.py, partially exists)
        ├─ 3. Standalone verify (iris_pipeline.py, already exists)
        ├─ 4. Register predicate (contract_linter.py predicates dict)
        └─ 5. Inline at call site (contract_linter._expand_predicate)
```

## Current State

### What already works

| Component | Status |
|---|---|
| `detect_loop_pattern` in `predicate_lowering.py` | Exists, supports EXISTSb and FOLD_LEFT patterns |
| `RecursorExpr` in `contract_ir.py` | Exists, compiles to `countb`/`forallb`/`existsb`/`fold_left_acc`/`filterb` |
| `ListPredicates.v` Coq library | Exists, 5 Fixpoints with lemmas |
| `_expand_predicate` in `contract_linter.py` | Exists, 4 paths (Recursor, simple inline, postcondition inline, fallback) |
| Single-expression predicates | Working — `def pos(x): return x > 0` inlines directly |
| Postcondition predicates | Working — `implies(result == 1, property)` rewrites and inlines |
| Comprehension in contracts | Working — `sum(1 for x in xs if p(x))` → `countb` |

### What's broken or missing

1. **`detect_loop_pattern` is never called.**  `_collect_predicates` in
   `mcp_server.py` never invokes it bridging predicate entries never get
   the Recursor/lambda fields.  The Recursor path in `_expand_predicate`
   is dead code.
2. **Missing loop patterns:** ENUM has `FORALLB` and `COUNTB` but the
   detector only handles `EXISTSb` (guard + early return True) and
   `FOLD_LEFT` (single `+=`).  The forall and count patterns are
   straightforward but unimplemented.
3. **Name mismatch:** `FOLD_LEFT` maps to string `"fold_left"` but the
   Coq Fixpoint is `fold_left_acc`.
4. **No Coq lemmas for `fold_left_acc` and `filterb`.**
5. **No multi-statement lowering** — a pure function with intermediate
   computations (but no loop) can't be wired because the body isn't a
   single expression.

## Architectural decision: reflection is the foundation, recursors are an optimization

> See [`docs/comparative-assessment.md`](comparative-assessment.md) §5 for the
> full brittleness analysis.

The pattern-matching approach in `predicate_lowering.py`
(`detect_loop_pattern` → `_extract_lambda` → string-templated Coq) is
**structurally the wrong foundation**.  It guesses semantics from exact AST
shapes, emits Coq as strings (`ast.unparse` into Coq — the very thing
AGENTS.md forbids), assumes every element is `Z`, can't compose, and never
checks the lifted form against the function it claims to represent.

The principled approach — what Liquid Haskell (refinement reflection) and
Dafny (`function`) do — is **reflection**: lower the predicate's body through
the *same* PyIR → SnakeletIR pipeline the verifier already uses, producing a
real Coq `Fixpoint` (type-carrying, not string-templated), then inline calls
to that Fixpoint in contracts.

```
def is_hex(s: str) -> bool:        Reflection:
    for c in s:                      PyIR → SnakeletIR (existing) → Coq Fixpoint
        if c not in HEX:               Fixpoint is_hex (s:string) : bool := ...
            return False             is_hex(result) → (is_hex result = true)
    return True
```

Why this fixes every failure mode of the pattern matcher:

| Failure mode | Reflection's answer |
|---|---|
| Exact-shape matching | IR lowerer handles `if`/`return`/`while`/`break`/accumulators generically |
| Invalid Coq strings | IR emits real Coq via `to_coq()`, never string-templated |
| `Z`-only | IR carries types; `is_hex` over `string` lowers correctly |
| No composition | A predicate calling another lowers the call as `SApp` — free |
| Unchecked lifted form | The Fixpoint *is* the lowered function; verify it (termination + contract). Lifted form equals verified form by construction |

**Termination** is the one genuinely new obligation. Coq `Fixpoint` needs a
decreasing argument. For `for c in s` / `for x in xs`, recursion on the tail
is structural and trivially accepted. For `while` loops you need an explicit
`decreases` measure — reject those with a clear message, do not silently
return `NONE`.

The recursor combinators (`forallb`/`existsb`/`countb`) become a **rewrite
pass over the reflected Fixpoint**: when the body matches
`match xs with [] => true | x::r => p x && rec r`, rewrite to `forallb p xs`
to inherit the pre-proved lemmas.  Unrecognized shapes still get a working
Fixpoint.  You never *depend* on recognizing the shape.

## Plan (revised: reflection-first)

### Step 0 — Reflection entry point (the new foundation)

**File:** new `predicate_reflection.py`

```python
def reflect_predicate(func_node: ast.FunctionDef,
                      table: FunTable) -> CoqFixpoint:
    """Lower a pure predicate's body to a Coq Fixpoint via PyIR/SnakeletIR.

    1. Translate to PyIR (PyIRTranslator — existing).
    2. Lower to SnakeletIR (IrisLowerer — existing).
    3. Wrap the SExpr body in a Coq Fixpoint with a structural
       decreasing argument (the iterated list/string param).
    4. Emit via SExpr.to_coq() — no string templating.
    """
```

This reuses the *entire* existing lowering stack.  The only new code is the
Fixpoint wrapper + termination-argument selection.

**Expected:** any terminating pure predicate produces a real Coq Fixpoint,
type-correct, composable.

### Step 0b — Verify the reflected predicate

Run the standalone `python_to_iris_proof` on the predicate so the kernel
accepts its termination and (optional) contract.  Register the *verified*
Fixpoint name.  Now `is_hex(result)` inlines a kernel-checked definition.

---

## Legacy plan (pattern-matcher path — superseded by Step 0)

The steps below describe wiring up the existing pattern matcher.  They remain
useful as a *fast path* for the common loop shapes (they inherit nicer
lemmas), but they must sit on top of the reflection foundation, not replace
it.  Treat them as the recursor-rewrite optimization.

### Step 1 — Wire `detect_loop_pattern` (small)

**File:** `mcp_server.py`, `_collect_predicates`

For each pure predicate function found, call `detect_loop_pattern(func_node)`.
If it returns a `Recursor` (not `NONE`), compute the lambda string via
`_extract_lambda(loop_var, test)` and store both in the predicate entry
as indices 3 and 4:

```python
recursor, lam = detect_loop_pattern(pred_node)
if recursor != Recursor.NONE:
    predicate_map[name] = (params, body_expr, post_asserts,
                           recursor, lambda_str)
```

**Expected:** `_expand_predicate` Path 1 (Recursor) becomes live.  Loop
predicates that match `EXISTSb` or `FOLD_LEFT` patterns immediately work.

---

### Step 2 — Add missing loop patterns (medium)

**File:** `predicate_lowering.py`, `detect_loop_pattern`

Add detection for the remaining `Recursor` cases:

| Pattern | Detection Rule | Coq combinator |
|---|---|---|
| `FORALLB` | `for x in xs: if not p(x): return False; return True` | `forallb` |
| `COUNTB` | `for x in xs: if p(x): count += 1; return count` | `countb` |
| `FILTERB` | `for x in xs: if p(x): result.append(x); return result` | `filterb` |

Each pattern follows the same structure as `EXISTSb`: walk the for-loop
body, identify the guard, extract the lambda via `_extract_lambda`.

---

### Step 3 — Fix naming and add lemmas (small)

**Files:** `predicate_lowering.py`, `ListPredicates.v`

1. Map `FOLD_LEFT` → `"fold_left_acc"` (matches Coq Fixpoint name).
2. Add lemmas for `fold_left_acc`:
   ```coq
   Lemma fold_left_acc_nil : forall A B f (acc : B) (xs : list A),
     fold_left_acc f acc xs = ...
   ```
3. Add lemmas for `filterb`:
   ```coq
   Lemma filterb_length : forall A p (xs : list A),
     List.length (filterb p xs) = countb p xs.
   ```

---

### Step 4 — Multi-statement pure lowering (medium)

**File:** `predicate_lowering.py` (new) or `iris_proof_gen.py`

For pure functions that have intermediate values but no loops:

```python
def is_valid_account(acct: Account) -> bool:
    b = acct.balance
    s = acct.status
    return b >= 0 and s >= 0
```

The postcondition `implies(result == 1, acct.balance >= 0 /\ acct.status >= 0)`
should be inlined.  This already works via `_expand_predicate` Path 3
(postcondition inlining) **if** the postcondition asserts use
`implies(result == 1, property)`.

**Action:** Ensure functions without loops but with `Ensures` docstring
contracts are registered in the predicate map with postcondition asserts.
The existing `_expand_predicate` Path 3 handles the rest.

---

### Step 5 — String character iteration (medium)

**File:** `predicate_lowering.py`, `contract_linter.py`, Coq

For predicates that iterate over string characters:

```python
def is_hex(s: str) -> bool:
    for c in s:
        if c not in "0123456789abcdef":
            return False
    return True
```

Add a string variant of the loop patterns.  The Coq side needs
`forallb`/`existsb` over strings (convert string to `list Ascii.ascii` and
reuse the existing combinators).  The linter lowers `for c in s` to
`forallb (fun c => ...) (list_of_string s)`.

**Action:** Add `list_of_string` Fixpoint to `SnakeletExnLang.v`:

```coq
Fixpoint list_of_string (s : string) : list Ascii.ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: list_of_string rest
  end.
```

Then `forallb is_hex_char (list_of_string s)` works with the existing
combinator library.

---

### Step 6 — Recursive predicates (large)

For predicates defined by structural recursion (e.g., `is_sorted` defined
via `len(lst) <= 1 or (... and is_sorted(lst[1:]))`):

This requires:
1. Detecting the recursive pattern in `predicate_lowering.py`
2. Generating a Coq `Fixpoint` for the predicate
3. Inlining the Fixpoint call in contracts

This is a larger effort.  The Coq infrastructure already handles
Fixpoints; the detector needs to recognize the structural-recursive
pattern and emit the appropriate Coq.

---

## Verifier features table (updated)

| Feature | Status | Enables |
|---|---|---|
| Purity detection | Existing | Safely flag functions as predicate-candidates |
| Recursor Expr (countb/forallb/existsb) | Existing | Loop → combinator lowering |
| `_expand_predicate` inlining | Existing, partially wired | Predicate call → inlined expression |
| Loop pattern: EXISTSb | Detection exists, dead code | `def has_item(xs, x): for ...` |
| Loop pattern: FOLD_LEFT | Detection exists, dead code | `def sum_sq(xs): acc=0; for x: acc+=x*x` |
| Loop pattern: FORALLB | Missing | `def all_pos(xs): for x: if not (x>0): return False` |
| Loop pattern: COUNTB | Missing | `def count_gt(xs, n): c=0; for x: if x>n: c+=1` |
| Loop pattern: FILTERB | Missing | `def positives(xs): for x: if x>0: out.append(x)` |
| Multi-statement lowering | Partially working (postcondition inline) | `def valid(acct): b=acct.balance; return b>=0` |
| String char iteration | Missing | `def is_hex(s): for c in s: if ...` |
| Recursive predicates | Missing | `def is_sorted(xs): ...` |
| Body for-loop lowering | Missing | Verifying the predicate's body (currently trust-based) |

## Priority order (reflection-first)

| Step | Impact | Effort | What it unlocks |
|---|---|---|---|
| 0 — Reflection entry point (`reflect_predicate`) | Very high | Medium | *Any* terminating pure predicate → Coq Fixpoint, type-correct, composable |
| 0b — Verify reflected predicate | Very high | Low | Lifted form is kernel-checked (sound by construction) |
| (opt) Recursor rewrite pass | Medium | Medium | Nicer lemmas for `forallb`/`countb`/`existsb`-shaped Fixpoints |
| Legacy: fix naming + lemmas | Low | Low | `fold_left_acc`, `filterb` lemmas (only if using fast path) |

The legacy pattern-matcher steps (wire `detect_loop_pattern`, add FORALLB /
COUNTB / FILTERB) are subsumed by Step 0.  They are worth keeping only as a
performance/lemma-quality optimization once reflection works.

## Success criteria

1. **Any** terminating pure Python function (loop, recursion, intermediate
   values, composed predicate calls) lifts into the contract language — not
   just N blessed loop shapes.
2. The lifted predicate is a kernel-checked Coq Fixpoint: the form used in
   contracts *equals* the verified function by construction.
3. A user can write `def is_hex(s): ...` and use `assert is_hex(result)` in a
   postcondition, with no string-templated Coq anywhere in the path.
4. `_extract_lambda` / `_py_expr_to_coq` string templating is deleted.
