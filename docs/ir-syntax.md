# Axiomander IR (IMP) Syntax

Axiomander compiles Python to a simple imperative intermediate language (IMP)
with tagged value semantics. The IR is **untyped at the term level** — types are
carried in runtime value tags (`VZ`, `VBool`, etc.), mirroring Python's dynamic
dispatch.

State is a record `{ ls: var->value, hs: (var,var)->value }` with string-named
variables.  `ls` is the local store (coerced so `s "x"` works); `hs` is a
two-dimensional heap for object fields.

## Values (Coq `value` type)

```
VZ(z: Z)      VBool(b: bool)     VUnit
VString(s)    VFloat(f: Z)       VNone
VTuple(ts)    VList(xs)          VDict(kvs)
VBytes(bs)    VSet(xs)
```

Float is integer-scaled (`float_scale = 10^6`).  String is Coq's native `string`.

## AExp — arithmetic expressions

| Node | Meaning |
|------|---------|
| `ANum(value : int)` | integer literal |
| `AVar(name : str)` | variable lookup `s[x]` |
| `APlus(left, right)` | addition (int/float promotion) |
| `AMinus(left, right)` | subtraction |
| `AMult(left, right)` | multiplication |
| `AMod(left, right)` | modulo |
| `ADiv(left, right)` | floor division |
| `ABool(bexp : ImpBExp)` | bool → integer (0/1) |
| `ALen(name : str)` | `len(collection)` |
| `AIndex(array : ImpAExp, index : ImpAExp)` | subscript `xs[i]` |
| `AString(value : str)` | string literal |
| `AFloat(int_val : int)` | float literal (scaled integer) |
| `ANone()` | `None` literal |

## BExp — boolean expressions

| Node | Meaning |
|------|---------|
| `BTrue()` / `BFalse()` | constant bools |
| `BEq(left, right)` | `a1 == a2` (numeric equality) |
| `BLe(left, right)` | `a1 <= a2` |
| `BNot(operand)` | logical negation |
| `BAnd(left, right)` | conjunction |
| `BOr(left, right)` | disjunction |
| `BIsVZ(aexp)` | `isinstance(val, int)` |
| `BIsVString(aexp)` | `isinstance(val, str)` |
| `BIsNone(aexp)` | `val is None` |
| `BIsVFloat(aexp)` | `isinstance(val, float)` |

**Encoding**: boolean comparisons use `BLe` + `BNot`.  `x > y` →
`BNot(BLe(x, y))`.  `!=` → `BNot(BEq(...))`.

## Com — commands (sequential, effectful)

| Node | Python source |
|------|--------------|
| `CSkip()` | `pass` |
| `CAss("x", aexp)` | `x = expr` |
| `CSeq(commands : list[ImpCom])` | `s1; s2; ...` |
| `CIf(condition, then_branch, else_branch)` | `if b: c1 else c2` |
| `CWhile(condition, body)` | `while b: body` |
| `CCall(callee, args, pre, post, writes, target)` | `target = callee(args)` (see below) |
| `CListNew("xs", aexp)` | `xs = [0] * n` |
| `CListAppend("xs", aexp)` | `xs.append(e)` |
| `CListPop("xs", "dest")` | `v = xs.pop()` |
| `CListSet("xs", idx, val)` | `xs[i] = v` |
| `CDictSet("d", key, val)` | `d[k] = v` |
| `CDictGet("d", key, "dest")` | `v = d[k]` |
| `CDictEnsureList("d", "k")` | `if k not in d: d[k] = []` |
| `CDictAppend("d", key, val)` | `d[k].append(v)` (after EnsureList) |
| `CDictAppendKv("d", key, val)` | `d.append((k, v))` (list-of-pairs dict) |
| `CHavoc(["x1", ...])` | black-hole writes (frame enforcement) |
| `CAssume(bexp)` | `assume condition` (loop invariants) |

### CCall — modelled function call

The callee's contract is **inlined** into the call node:

```
CCall("inc",
      args      = [AVar("a")],
      pre       = fun s => asZ(s["x"]) >= 0,
      post      = fun s => asZ(s["a2"]) = asZ(s["x"]) + 1,
      writes    = [],
      target    = "a2")
```

`pre` and `post` are lambda-assertions (Python→Coq translated).  `writes` is the
callee's declared write-set.  Frame conditions are proven by the WP calculus:
`lget s x = lget (clobber (lupd s target (VZ r)) writes) x` for all `x`
not equal to `target` and not in `writes`.

## WP calculus (semantics in `coq/Wp.v`)

```
wp(CSkip) Q s          = Q s
wp(CAss x a) Q s       = Q (lupd s x (VZ (aeval s a)))
wp(CSeq c1 c2) Q s     = wp c1 (wp c2 Q) s
wp(CIf b c1 c2) Q s    = (beval s b -> wp c1 Q s) /\ (~beval s b -> wp c2 Q s)
wp(CWhile b c) Q s     = fixpoint of invariant
wp(CCall ...) Q s      = pre s /\ (forall r, post(lupd s tgt (VZ r)) -> 
                           Q(clobber (lupd s tgt (VZ r)) writes) /\
                           (forall x, ~In x (tgt::writes) -> 
                             lget s x = lget (clobber (lupd s tgt (VZ r)) writes) x))
```

## Design notes

- **Not a typed IVL**.  Unlike Boogie or Why3, there is no static type system
  on expressions.  Types live in the value domain (runtime tags).  Coercion
  rules (float+int→float, etc.) are explicit in the semantics.
- **Structural values**.  `VList`, `VTuple`, `VDict` are immutable value types
  (like Dafny `seq`).  Mutable operations work through the heap store `hs`.
- **Frame conditions** are explicit and enforced — the WP rule for `CCall`
  generates `forall x, ~In x (...) -> lget ... = ...` subgoals for every
  variable not written by the callee.
