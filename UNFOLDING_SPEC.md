
# Logical Function Encoding for Python → Z3  
### (Unfolding Trick Specification for AI Coding Agent)

This document describes how the agent should translate **pure logical Python functions** into SMT (Z3) using the **fuelled unfolding technique**, similar to F★. This enables limited reasoning about recursively defined predicates while keeping SMT solving tractable.  
This is intended for *verification-assisted linting* and *counterexample search*, not full program verification.

---

## 1. Overview

When translating Python functions marked with `@logic` into SMT, the agent must:

1. Treat each logical function as **pure**, **side-effect free**, and part of the specification logic.
2. Encode it as:
   - An **uninterpreted function** `f`.
   - A **fuelled version** `f_fuel(k, ...)` controlling unfolding depth.
3. Generate a **bounded unfolding axiom** for one-step expansion.
4. Introduce a **maximum fuel constant** `MAX_FUEL`.
5. Tie `f` to `f_fuel(MAX_FUEL, ...)` via an equality axiom.
6. Use `f(...)` in verification conditions; Z3 handles unfolding automatically.

---

## 2. Marking Logical Functions

Any Python function decorated with:

```python
@logic
def f(...): ...
```

must be treated as a *logical* function eligible to appear in contracts such as:

```python
@requires(lambda x: sorted(x))
@ensures(lambda x, y: foo(y) > 0)
```

Logical functions:

- Must be pure.
- May be recursive.
- Must use only a limited subset of Python expressions (conditionals, arithmetic, lists, booleans).

---

## 3. SMT Encoding for Each Logical Function

Given:

```python
@logic
def f(x1, ..., xn):
    BODY
```

### 3.1 Declare the uninterpreted symbol

```smt2
(declare-fun f (T1 ... Tn) R)
```

This symbol is what contracts refer to.

---

### 3.2 Declare the fuelled version

```smt2
(declare-fun f_fuel (Int T1 ... Tn) R)
```

Interpretation:  
`f_fuel(k, args)` = the value of `f(args)` computed with at most `k` unfolding steps.

---

### 3.3 Build the SMT body template

Translate the Python body `BODY` into SMT expression form `Body_f(k, args)` with:

- Each recursive call `f(t1, ..., tn)` replaced by:

```smt2
(f_fuel (- k 1) t1 ... tn)
```

- Non-recursive calls translated normally.

---

### 3.4 Add the one-step unfolding axiom

Example form:

```smt2
(assert (forall ((k Int) (x1 T1) ... (xn Tn))
  (=> (> k 0)
      (= (f_fuel k x1 ... xn)
         Body_f(k, x1, ..., xn)))))
```

This encodes:  
“if fuel is positive, the function unfolds once.”

---

### 3.5 Declare and set the maximum fuel

```smt2
(declare-const MAX_FUEL Int)
(assert (= MAX_FUEL 3))  ; or any small integer
```

Small fuel is intentional—this is for linting, not full proofs.

---

### 3.6 Connect uninterpreted and fuelled symbols

```smt2
(assert (forall ((x1 T1) ... (xn Tn))
  (= (f x1 ... xn)
     (f_fuel MAX_FUEL x1 ... xn))))
```

This tells Z3 to use *bounded* unfolding when it sees `f(...)`.

---

## 4. Using Encoded Predicates During Analysis

When generating verification conditions or counterexample queries:

- **Always use** the uninterpreted symbol `f(...)`.
- **Never inline** Python function bodies directly.
- The solver decides when to instantiate unfolding axioms.

This yields:

- Decidable reasoning
- Limited but practical power over recursive predicates
- Good performance for automated counterexample search

---

## 5. Non-Recursive Logical Functions

If a logical function is not recursive, `Body_f` contains no calls to `f_fuel(k-1, ...)`.

The unfolding axiom then fully evaluates the function in one step.

This improves solver performance significantly.

---

## 6. Example

Python:

```python
@logic
def foo(n: int) -> int:
    return 1 if n == 0 else n + foo(n - 1)
```

Generated SMT:

```smt2
(declare-fun foo (Int) Int)
(declare-fun foo_fuel (Int Int) Int)

(assert (forall ((k Int) (n Int))
  (=> (> k 0)
      (= (foo_fuel k n)
         (ite (= n 0)
              1
              (+ n (foo_fuel (- k 1) (- n 1))))))))

(declare-const MAX_FUEL Int)
(assert (= MAX_FUEL 3))

(assert (forall ((n Int))
  (= (foo n)
     (foo_fuel MAX_FUEL n))))
```

---

## 7. Summary for the Agent

> **When translating logical Python functions:**
>
> 1. Declare `f` and `f_fuel`.
> 2. Build an unfolding body template with recursive calls using `k-1`.
> 3. Emit the guarded unfolding axiom.
> 4. Pick a small `MAX_FUEL`.
> 5. Tie `f(args)` to `f_fuel(MAX_FUEL, args)`.
> 6. Use `f(...)` in all VCs; solver handles unfolding.

This provides:
- A solid approximation of F★'s unfolding behavior  
- Reasonable performance  
- Useful partial reasoning  
- Counterexample-friendly behavior  

Perfect for **verification-assisted linting**.

