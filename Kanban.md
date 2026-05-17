# Kanban

## Done

### Core pipeline
- [x] IMP language — value-typed state model: `VZ | VBool | VUnit | VString | VFloat`
- [x] WP calculus with `aeval → value` (box/unbox dispatch), `beval` type-aware comparison
- [x] `wp_reduce` / `wp_prove` structural automation (unfolds asZ/asString/asFloat/clobber)
- [x] VCG while-exit obligation generation + SMT/Lia proofs
- [x] Pydantic model encoding (Record types, `store_field`, `load_field`, frame condition generation)
- [x] Python contract linter (`assert` → IR → Coq + SMT-LIB)
- [x] Python → IMP body translator (assign, if/else, while, for, return, augmented assignment, break/continue)
- [x] 74 tests: arithmetic, loops, lists, dicts, sets, strings, class fields, predicates, function calls, range quantifiers, frame conditions, stub integration
- [x] LLM oracle wired to coqpyt (interactive proof validation)

### MCP server + tools
- [x] check-file, check-function, verify-function, verify-changed, verify-impacted, explain-cache
- [x] `frame-report` — pre/post/inv contracts + modifies/preserves + callee effects
- [x] CLI parity: all tools exposed via Typer CLI

### Caching
- [x] Incremental verification cache (body/contract/callee-contract discipline)
- [x] Dependency graph + transitive invalidation

### Frame conditions
- [x] Library stubs (`.pyi`): requires/ensures/reads/writes docstring contracts
- [x] Stub merge with source asserts (source pre/post take precedence, reads/writes union)
- [x] `CCall` carries `writes : list var` through the pipeline
- [x] `clobber` semantics — ceval zeros out callee writes variables
- [x] Frame lemmas: `clobber_unchanged`, `upd_unchanged`
- [x] Implicit field preservation for class fields (generate_frame_conditions)
- [x] `asZ` wrapping fix for frame conditions

### Purity & black holes
- [x] Purity analyzer: black hole detection for impure calls
- [x] `CHavoc` for impure calls

### VString (Phase 1)
- [x] `VString : string → value` constructor
- [x] `AString` aexp, `asString` extractor
- [x] `BEq` type dispatch: `String.eqb` for string equality
- [x] `StrLitExpr` IR node — Coq string literals in contracts
- [x] `BinOp.to_coq` — `asString` wrapping for string comparisons
- [x] Tests: `str_literal_eq`, `str_literal_cond` (internal strings work)
- [ ] String parameter storage (currently replaced by `s__len`, not stored as value)

### VFloat (Phase 1)
- [x] `VFloat : Z → value` constructor (Z-encoded, scale factor 100)
- [x] `AFloat` aexp, `asFloat` extractor
- [x] `BEq` type dispatch: `Z.eqb` for float equality
- [x] `BLe` type dispatch: `VFloat/VFloat` comparison
- [x] `FloatExpr` IR node
- [x] `BinOp.to_coq` — `asFloat` wrapping for float comparisons
- [x] Tests: `float_literal_eq`, `float_eq` (store/compare, equality via ==)
- [ ] Float arithmetic (`a + b`, `a < b` with mixed VFloat/VZ operands) — needs per-type dispatch in `APlus` etc.
- [ ] Float parameter storage (same issue as strings)

---

## In Progress

### Frame enforcement
- [ ] Wire `clobber` + frame conjunct into `CCall` WP rule
- [ ] Fix `wp_reduce` to handle `String.eqb` without ASCII explosion (currently blocks enforcement)
- [ ] Negative frame test that actually fails when callee writes to caller's variable
- [ ] Per-type dispatch in `APlus`, `AMinus`, etc. for `VFloat` operands

### LSP + tooling
- [ ] Better error reporting (map coqc errors to Python source lines)
- [ ] LLM oracle reliability (better prompt, more retries, proof repair)
- [ ] CI — GitHub Action

---

## Next — Python Runtime Type System

The `value` type needs to match Python's runtime. Priority order:

### High (ubiquitous, trivial to add)
- [ ] **`VNone`** — `None` currently maps to `VZ 0`. Adding `VNone` to `value` + dispatch in `BEq`/`BLe` would verify `is None`/`is not None` correctly. Same pattern as VFloat.
- [ ] **Type annotation mapping**: `float` → `float` (not `Z`), `None` → proper type, `bool` → proper type

### Medium (need container semantics)
- [ ] **`VList (list value)`** — currently encoded as heap array (`parray_key`). Value constructor enables `xs == ys`, concatenation, value-typed indexing.
- [ ] **`VDict (list (value * value))`** — similar to list. Enables `k in d` as value dispatch, not ghost-length check.
- [ ] **`VTuple (list value)`** — immutable list. `(1, "hello")` becomes `VTuple [VZ 1; VString "hello"]`.
- [ ] **`VSet (list value)`** — dict without values. Dedup on insert via value equality.

### Hard (need new IMP constructs)
- [ ] **`VComplex (re im : Z)`** — two-component float. Arithmetic is domain-specific.
- [ ] **`VGenerator`** — lazy evaluation. Would need state-capture semantics.
- [ ] **`VFunction` / `VMethod`** — first-class functions. Would need closure model.

---

## Next — Effects & I/O

- [ ] **Filesystem ghost state** — `read_text`/`write_text` modeled as ghost map updates
- [ ] **Path traversal safety proofs** — `_resolve_local_path` never escapes root
- [ ] **OCC (optimistic concurrency control)** verification — hash-checked writes
- [ ] **Two-phase commit** — temp write doesn't clobber main until commit
- [ ] **Database ghost state** — SQL queries as ghost reads, transactions as ghost writes
- [ ] **Network stubs** — `httpx.get` as opaque axiom with timeout/non-response possibilities

---

## Backlog

### Contract language
- [ ] Implication in contracts: `A → B` (conditional guarantees)
- [ ] Branch-specific postconditions
- [ ] Quantified invariants: `forall i, 0 <= i < len(lst) → lst[i] <= lst[i+1]`
- [ ] Relational properties: "output is a permutation of input", "output ⊆ input"
- [ ] Multiple loop VCGs (currently only outermost/last loop gets VCG)

### Proof strength
- [ ] Induction in VCG
- [ ] Non-linear arithmetic counterexample extraction
- [ ] Termination measures
- [ ] Supercompiler / symbolic evaluation of WP for concrete inputs

### Polish
- [ ] Delete dead code: `vcg_exit` Ltac, duplicate `return` in `_translate_for`
- [ ] `_fresh_var` generator for loop counters
- [ ] Documentation — user guide, API reference
- [ ] Exception handling (try/except as black holes)
- [ ] Pydantic/BaseModel support for `@dataclass`-style classes
