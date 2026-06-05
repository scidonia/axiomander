# Kanban

## Done

### Core pipeline
- [x] IMP language — value-typed state model: `VZ | VBool | VUnit | VString | VFloat | VNone | VTuple | VList | VDict | VBytes`
- [x] `value_eqb` — structural equality dispatching on all 10 value constructors (nested fix for containers)
- [x] WP calculus with `aeval → value` (box/unbox dispatch), `beval` type-aware comparison, float coercion
- [x] `wp_reduce` / `wp_prove` structural automation (unfolds asZ/asString/asFloat, `cbn -[In clobber]`)
- [x] VCG while-exit obligation generation + SMT/Lia proofs
- [x] Pydantic model encoding (Record types, `store_field`, `load_field`, frame condition generation)
- [x] Python contract linter (`assert` → IR → Coq + SMT-LIB)
- [x] Python → IMP body translator (assign, if/else, while, for, return, augmented assignment, break/continue)
- [x] **85 tests**: 15 negative, 70 positive — covering arithmetic, loops, lists, dicts, sets, strings, class fields, predicates, function calls, range quantifiers, frame conditions, stub integration, tuple/bytes/dict/None/float/string value comparisons
- [x] LLM oracle wired to coqpyt (interactive proof validation)
- [x] String parameter storage — `VString s_str` at original key + `VZ s__len` at `._len`
- [x] Float parameter storage — `VFloat` for `float`-annotated params
- [x] `IsNot` → `BNot(BEq)` fix (was silently proving `x is not None` on `None` values)

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
- [x] Frame lemmas: `clobber_nil`, `clobber_unchanged`, `upd_unchanged`, `wp_ccall_frame`
- [x] Frame enforcement wired via `cbn -[In clobber]` + `wp_ccall_frame` lemma
- [x] Implicit field preservation for class fields (generate_frame_conditions)
- [x] `asZ` wrapping fix for frame conditions

### Purity & black holes
- [x] Purity analyzer: black hole detection for impure calls
- [x] `CHavoc` for impure calls

### Value types (all 10 constructors)
- [x] `VString` — `String.eqb` equality, `AString` aexp, `StrLitExpr` IR, `asString` wrapper
- [x] `VFloat` — Z-encoded (scale 100), `AFloat` aexp, `FloatExpr` IR, `asFloat`, `BLe` dispatch, coercion in aeval
- [x] `VNone` — `ANone` aexp, `is None` via BEq, `is not None` via BNot(BEq)
- [x] `VTuple` — `ATuple` aexp, structural equality via nested fix
- [x] `VList` — value constructor for equality, heap commands preserved for mutation
- [x] `VDict` — `ADict` aexp, `DictExpr` IR, `visit_Dict` linter
- [x] `VBytes` — `ABytes` aexp, byte literal translation
- [x] `VSet` — value constructor exists, translator/linter pending

### Negative tests
- [x] 15 negative tests: weak invariants, missing bounds, false postconditions, broken string/bytes/dict/None comparisons, frame violation, braces, count errors
- [x] AGENTS.md rule: every new type/operation must have negative tests

---

## In Progress

### LSP + tooling
- [ ] Better error reporting (map coqc errors to Python source lines)
- [ ] LLM oracle reliability (better prompt, more retries, proof repair)
- [ ] CI — GitHub Action

### VSet completion
- [ ] Translator: `ast.Set` → `ASetLit`
- [ ] Linter: `visit_Set` → `SetExpr` IR node
- [ ] Negative test: set equality violation

---

## Next — Contract Language

- [ ] Implication in contracts: `A → B` (conditional guarantees)
- [ ] Branch-specific postconditions
- [ ] General quantifiers: `forall`/`exists` as IR nodes (beyond `all()`/`any()`)
- [ ] Relational properties: "output is a permutation of input"
- [ ] Multiple loop VCGs (currently only outermost/last loop gets VCG)

---

## Next — Effects & I/O

- [ ] Filesystem ghost state — `read_text`/`write_text` modeled as ghost map updates
- [ ] Path traversal safety proofs — `_resolve_local_path` never escapes root
- [ ] OCC (optimistic concurrency control) verification — hash-checked writes
- [ ] Database ghost state — SQL queries as ghost reads, transactions as ghost writes
- [ ] Network stubs — `httpx.get` as opaque axiom

---

## Backlog

### Proof strength
- [ ] Induction in VCG
- [ ] Non-linear arithmetic counterexample extraction
- [ ] Termination measures
- [ ] Supercompiler / symbolic evaluation of WP for concrete inputs

### Hard types
- [ ] `VComplex (re im : Z)` — two-component float
- [ ] `VGenerator` — lazy evaluation, state-capture semantics
- [ ] `VFunction` / `VMethod` — first-class functions

### Polish
- [ ] Delete dead code: `vcg_exit` Ltac, duplicate `return` in `_translate_for`
- [ ] Documentation — user guide, API reference
- [ ] Exception handling (try/except as black holes)
