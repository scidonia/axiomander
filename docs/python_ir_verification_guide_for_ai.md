# Guide for an AI Assistant: Choosing and Using the Right Intermediate Language for Python Verification

## Purpose

This guide tells an AI coding assistant how to reason about an intermediate language, or IR, for proving properties of Python programs.

The goal is not to design a beautiful toy language. The goal is to support a significant chunk of real Python code while remaining sound enough to generate proof obligations for SMT solvers, Coq, or other verification backends.

The central recommendation is:

> Use two intermediate languages, not one.

```text
Python source
   ↓
Faithful Python Core IR
   ↓
Verification IR
   ↓
SMT / Coq / supercompiler / proof search
```

The first IR must be faithful to Python.  
The second IR must be suitable for proof.

Trying to make one IR do both jobs is likely to produce either an unsound system or a system too complex to prove anything useful.

---

# 1. The Core Principle

The AI assistant must preserve this rule:

> Never silently simplify Python semantics in a way that could change observable behavior.

Python is highly dynamic. Even simple-looking expressions can hide complex behavior.

For example:

```python
x = obj.f(y)
```

This is not merely a function call. It may involve:

- dynamic attribute lookup;
- `__getattribute__`;
- descriptors;
- method binding;
- allocation of a bound method object;
- arbitrary user code during lookup;
- mutation;
- exceptions;
- dynamic dispatch;
- monkey patching.

Therefore, the first IR must not pretend that Python is simpler than it is.

The AI assistant should think in terms of this discipline:

```text
Faithful first. Prove second.
```

---

# 2. Why One IR Is Not Enough

A single IR is tempting because it feels simpler:

```text
Python AST → proof obligations
```

But this is dangerous.

Python AST is not explicit enough. It hides too much of the runtime behavior. A proof engine based directly on Python AST will likely miss effects, exceptions, aliasing, or dynamic dispatch.

A tiny verification language is also not enough. It may be pleasant for proofs, but it cannot faithfully represent real Python.

Therefore, the system should use two IRs:

```text
1. Faithful Python Core IR
2. Verification IR
```

The first captures what Python actually does.  
The second captures what the prover can reason about.

---

# 3. The Faithful Python Core IR

## 3.1 Purpose

The Faithful Python Core IR is the front-end semantic representation.

Its purpose is to make Python behavior explicit.

It should represent:

- control flow;
- heap effects;
- local variables;
- attribute access;
- item access;
- function calls;
- method calls;
- allocation;
- mutation;
- assertions;
- exceptions;
- returns;
- unknown effects.

It should be close enough to Python semantics that lowering from Python source to this IR is trustworthy.

This IR is allowed to be ugly. It is not meant to be the final proof language.

## 3.2 Shape

A good structure is a control-flow graph of basic blocks.

```text
FunctionIR:
  name
  parameters
  locals
  blocks
  entry_block
  exit_blocks
```

Each block contains statements and a terminator:

```text
BasicBlock:
  statements: Statement[]
  terminator: Terminator
```

Terminators include:

```text
Return(value)
Jump(block)
Branch(condition, then_block, else_block)
Raise(exception)
```

Statements include:

```text
Assign(target, expr)
LoadName(dst, name)
StoreName(name, value)
LoadAttr(dst, obj, attr)
StoreAttr(obj, attr, value)
LoadItem(dst, obj, key)
StoreItem(obj, key, value)
Call(dst, callee, args, kwargs)
Alloc(dst, type_or_constructor)
Assert(condition)
Assume(condition)
Havoc(target_or_region)
```

The AI assistant should prefer an explicit CFG over raw AST because verification needs explicit control flow.

---

# 4. The Verification IR

## 4.1 Purpose

The Verification IR is the proof-oriented language.

It should be simpler than Python and suitable for:

- weakest precondition generation;
- SMT encoding;
- Coq encoding;
- symbolic execution;
- supercompilation;
- proof caching;
- function summaries;
- modular verification.

This IR should look closer to Boogie, WhyML, Viper, or a classic guarded-command language than to Python.

## 4.2 Shape

The Verification IR should include:

```text
variables
pure expressions
heap locations
assignments
assume
assert
havoc
function calls through summaries
loop invariants
preconditions
postconditions
frame conditions
```

Example:

```text
assume x >= 0
old_heap := heap
y := x + 1
assert y > x
return y
```

For heap mutation:

```text
heap[obj, field] := value
```

For unknown mutation:

```text
havoc heap_region
assume known_postcondition
```

This language should be small enough to encode into SMT or Coq cleanly.

---

# 5. Translation Strategy

The AI assistant should treat translation as a staged process:

```text
Python source
  → parse
  → faithful core IR
  → effect analysis
  → alias analysis / approximation
  → summary lookup
  → verification IR
  → proof obligations
```

The transition from Faithful Python Core IR to Verification IR is where the system decides what it can prove exactly and what must be approximated conservatively.

---

# 6. Handling Unsupported Python Features

The AI assistant must follow this rule:

> Every unsupported feature must become either exact semantics, conservative havoc, an opaque summary, or a clear verification failure.

The allowed outcomes are:

```text
1. Translate exactly.
2. Replace with conservative havoc.
3. Use an opaque function or method summary.
4. Reject the proof attempt with a clear explanation.
```

The system must never silently pretend that an unsupported feature is pure, deterministic, or side-effect free.

## 6.1 Exact Translation

Use exact translation when the feature is understood well enough.

Example:

```python
x = y + 1
```

can become:

```text
x := y + 1
```

provided `y` is known to be an integer and `+` is known not to dispatch to arbitrary Python code.

## 6.2 Conservative Havoc

Use `havoc` when the code may mutate state in unknown ways.

Example:

```python
unknown_library_call(obj)
```

may become:

```text
havoc heap_reachable_from(obj)
```

This is conservative. It weakens what can be proved, but it avoids unsoundness.

## 6.3 Opaque Summary

Use an opaque summary when the system has a contract for a function but not its body.

Example:

```python
def sort(xs: list[int]) -> None:
    ...
```

with summary:

```text
requires all_ints(xs)
modifies xs
ensures sorted(xs)
ensures permutation(xs, old(xs))
```

Then a call to `sort(xs)` can be represented as:

```text
assert all_ints(xs)
havoc xs_contents
assume sorted(xs)
assume permutation(xs, old_xs)
```

## 6.4 Clear Verification Failure

If neither exact translation, havoc, nor summary is acceptable, fail clearly.

Example message:

```text
Cannot verify this function because attribute lookup on object `obj` may invoke user-defined `__getattribute__`, and no summary is available.
```

This is much better than generating a false proof.

---

# 7. What Python Should Be Supported First

The first useful target should include:

- local variables;
- integer and boolean expressions;
- simple strings;
- tuples in limited form;
- lists with modeled heap effects;
- dictionaries with modeled heap effects;
- simple classes;
- ordinary instance fields;
- ordinary methods;
- function calls with summaries;
- loops with invariants;
- assertions;
- preconditions;
- postconditions;
- exceptions as explicit control flow;
- module-level constants;
- simple imports with trusted summaries.

This is enough to verify a significant and useful fragment of Python.

The assistant should not aim to support all Python immediately. It should aim to support real Python incrementally and conservatively.

---

# 8. Difficult Python Features

The following features are dangerous and should not be treated as ordinary pure constructs:

- dynamic attribute access;
- monkey patching;
- reflection;
- `getattr` / `setattr` / `hasattr`;
- metaclasses;
- descriptors;
- decorators;
- properties;
- operator overloading;
- generators;
- async functions;
- context managers;
- global mutation;
- native extension calls;
- arbitrary library calls;
- mutation through aliases;
- mutation through containers;
- exceptions thrown from ordinary-looking expressions.

The system may still handle these, but only through exact modeling, summaries, conservative havoc, or explicit rejection.

---

# 9. Assertions as the User-Facing Specification Language

The user-facing specification system should use ordinary Python features as much as possible:

```python
assert x >= 0
```

Preconditions and postconditions can be expressed using asserts, decorators, type annotations, or helper functions.

Example:

```python
def inc(x: int) -> int:
    assert x >= 0
    result = x + 1
    assert result > x
    return result
```

The AI assistant should interpret these assertions as proof obligations.

However, assertion expressions must belong to a controlled, observably pure specification sublanguage.

This means assertion expressions should be checked before being trusted.

---

# 10. The Specification Sublanguage

Python expressions used inside assertions, preconditions, postconditions, and invariants should be linted.

They should be allowed only when they are observably pure or explicitly summarized.

Allowed examples:

```python
x >= 0
len(xs) == n
is_sorted(xs)
all(xs[i] <= xs[i+1] for i in range(len(xs)-1))
```

Potentially disallowed examples:

```python
assert f(x)
```

unless `f` is known to be pure and has a specification.

Dangerous examples:

```python
assert obj.next()
assert xs.pop() == 3
assert random.random() > 0.5
assert database.query(...)
```

These should be rejected or treated as opaque under an explicit summary.

The AI assistant should not assume that Python expressions in asserts are pure merely because they appear in asserts.

---

# 11. Heap Model

A useful heap model should make object state explicit.

A simple model is:

```text
heap: Location × Field → Value
```

Then:

```python
obj.x = 3
```

becomes:

```text
heap[obj, "x"] := 3
```

and:

```python
y = obj.x
```

becomes:

```text
y := heap[obj, "x"]
```

This is only sound when attribute access is known to be ordinary field access. Otherwise, Python attribute lookup may involve custom code and must be modeled more carefully.

For containers:

```text
list_contents: Location × Index → Value
dict_contents: Location × Key → Value
```

or as abstract functional maps.

---

# 12. Aliasing and Frames

The assistant must treat aliasing as central.

Example:

```python
a = xs
b = xs
b.append(1)
assert len(a) == len(xs)
```

Here `a`, `b`, and `xs` may refer to the same object.

The verification system must track or conservatively approximate aliasing.

Function summaries should include frame conditions:

```text
modifies xs
```

or:

```text
modifies heap_reachable_from(obj)
```

Without frame conditions, calls should be assumed to potentially modify too much, making proofs weak but sound.

---

# 13. Function Summaries

Function summaries are essential for scaling.

A function summary should include:

```text
requires: preconditions
ensures: postconditions
modifies: frame conditions
raises: possible exceptions
pure: whether it is observationally pure
```

Example:

```text
function abs(x: int) -> int
requires true
ensures result >= 0
ensures result == x or result == -x
modifies nothing
raises nothing
pure true
```

The assistant should use summaries to avoid re-verifying everything every time.

---

# 14. Caching and Incremental Verification

The AI assistant should design verification around caching.

A function proof depends on:

- the function body;
- its precondition;
- its postcondition;
- loop invariants;
- called function summaries;
- relevant type assumptions;
- relevant library summaries;
- the semantics version of the IR translator.

A proof cache key should include hashes of these dependencies.

If a called function body changes but its summary remains valid, callers may not need to be re-proved.

If a called function summary changes, callers that depend on it must be reconsidered.

---

# 15. SMT and Coq Division of Labor

The assistant should use SMT for routine obligations:

- arithmetic;
- linear inequalities;
- simple algebra;
- boolean logic;
- simple arrays/maps;
- quantifier-light properties.

Coq should be used for:

- proof-producing validation;
- complex inductive invariants;
- reusable lemmas;
- recursive specifications;
- trusted proof reconstruction;
- higher-confidence certificates.

A practical flow is:

```text
Generate verification condition
   ↓
Try SMT
   ↓
If successful, optionally record certificate or lemma
   ↓
If not, ask LLM/proof oracle for invariant or proof help
   ↓
Try Coq or proof reconstruction
```

SMT success should not automatically become an unexamined global axiom. The system should record what was proved, under what assumptions, and with what summaries.

---

# 16. Supercompilation

Supercompilation can be useful for checking certain pre/post relationships by specializing a program against its specification.

Example idea:

```python
def insertion_sort(xs): ...

def is_sorted(xs): ...
```

The system may combine the implementation and postcondition into a residual verification problem.

In ideal cases, the residual program simplifies to something equivalent to:

```text
true
```

However, supercompilation must operate over a well-defined IR. It should not operate directly on arbitrary Python AST unless Python effects have already been made explicit.

Recommended flow:

```text
Python → Faithful Core IR → Verification IR → supercompiler / symbolic reducer
```

Supercompilation is a proof aid, not a replacement for a sound semantics.

---

# 17. What the AI Assistant Should Do When Editing Code

When asked to modify Python code, the assistant should:

1. Preserve existing behavior unless explicitly asked otherwise.
2. Add assertions that express useful local facts.
3. Prefer simple, pure assertions.
4. Add preconditions and postconditions where they clarify intent.
5. Avoid assertions that call effectful functions.
6. Add loop invariants when loops are present.
7. Identify unknown calls and suggest summaries.
8. Avoid making unverifiable dynamic behavior look verified.
9. Report which proof obligations are likely SMT-solvable.
10. Report which obligations require stronger invariants or summaries.

---

# 18. What the AI Assistant Must Not Do

The assistant must not:

- translate Python AST directly to Coq while ignoring Python semantics;
- assume attribute access is pure;
- assume method calls are simple function calls;
- assume assert expressions are pure;
- ignore exceptions;
- ignore aliasing;
- ignore mutation through containers;
- ignore operator overloading;
- treat unsupported code as verified;
- generate fake proofs;
- silently drop hard parts of Python semantics.

If unsure, the assistant should choose sound conservatism over convenience.

---

# 19. Recommended IR Decision

The recommended architecture is:

```text
Python source
   ↓
Faithful Python Core CFG IR
   ↓
Verification IR with heap, assumes, asserts, havoc, summaries
   ↓
SMT / Coq / supercompilation
```

The Faithful Core IR should be operational and explicit.

The Verification IR should be small, logical, and proof-oriented.

This is the best compromise between supporting real Python and generating trustworthy proof obligations.

---

# 20. Final Guidance for the AI Assistant

When working on this verification system, always ask:

```text
Did I preserve Python behavior faithfully?
```

then:

```text
Did I translate only the parts I understand into proof obligations?
```

then:

```text
Did I conservatively handle the parts I do not understand?
```

The right intermediate language is not a tiny idealized Python. It is a pipeline:

```text
faithful Python core first,
proof-friendly verification language second.
```

That is the architecture most likely to verify a significant chunk of Python without becoming unsound.

