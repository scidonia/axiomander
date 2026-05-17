# Kanban

## Done

- [x] IMP language + WP calculus + soundness (Coq)
- [x] `wp_reduce` / `wp_prove` structural automation (2 tactics, ~12 lines total)
- [x] `ABool : bexp → aexp` explicit cast (mutual induction aexp/bexp)
- [x] SMT VCG export (cvc4 subprocess, counterexample extraction)
- [x] Contract IR (Pydantic discriminated unions) — Coq + SMT-LIB compilation
- [x] LLM oracle wired to coqpyt (interactive proof validation)
- [x] Python contract linter (`assert` → IR → Coq), zero imports
- [x] Python → IMP body translator (assign, if/else, while, for, return, truthiness, augmented assignment)
- [x] VCG while-exit obligation generation + SMT/Lia proofs
- [x] Multi-loop VCG (nested/sequential heuristic)
- [x] Pydantic model encoding (Record types, field access)
- [x] Class param expansion, type annotation extraction
- [x] Negative tests: weak invariants → SMT counterexamples; body → WP contradiction
- [x] pytest test harness — **63 tests**
- [x] **Rebrand**: refactoring-robots → axiomander (opam, dune, docs, env vars, opencode config)
- [x] **MCP tools**: check-file, check-function, verify-function, verify-changed, verify-impacted, explain-cache
- [x] **CLI parity**: all 6 MCP tools exposed via Typer CLI
- [x] **Incremental cache**: body/contract/callee-contract discipline, dependency graph, transitive invalidation
- [x] **Purity analyzer**: black hole detection for impure calls, KNOWN_PURE builtins, stub contract awareness
- [x] **Frame conditions**: implicit field preservation for annotated class fields (by omission), old-value field captures
- [x] **Library stubs** (`.pyi`): requires/ensures/reads/writes docstring contracts, merge with source asserts
- [x] **wp_prove CIf handling**: automatic Z.leb/Z.eqb condition case splitting
- [x] **LSP server**: pygls v2, didOpen/didChange/didSave → debounced verification → publishDiagnostics
- [x] **Type annotation → Coq type mapping**: `int` → Z, `str` → list, `list[T]` → list

---

## Todo — Dogfood blockers (what we hit trying to verify our own code)

These are the features that prevented `check-function` from working on cached
axiomander source files when we tried to contract them:

### Method calls on self
- [x] `self.method(args)` → CCall translation. Currently only standalone functions work.
- [x] Object-level contracts: `self` as a parameter with pre/post/invariant asserts.
- [x] Class methods in `_build_contract_map` (walk ClassDef bodies for FunctionDef nodes).

### Python expressions outside IMP subset
- [x] Ternary: `x if cond else y` — translated to `CIf(cond, CAss(target, x), CAss(target, y))`.
- [x] Constructor calls with arguments: `list(expr)` → CListNew, `set(expr)` → deferred.
- [x] `and`/`or` with non-boolean semantics: `x or y` → `CIf(x, x, y)`, `x and y` → `CIf(x, y, x)`.

### Imports and module resolution
- [x] Relative/external imports — silently skipped in IMP translation (see note below).
  - Note: imports inside function bodies are skipped; module-level imports are ignored.
  - Resolution of imported names for contract lookup is not yet implemented.

### String operations
- [x] `str.lower()`, `str.strip()` — already supported via while-loop encoding.
- [x] String concatenation: `s1 + s2` → while-loop CListAppend (creates new array, copies both).
- [ ] `str.split()` — not implemented.

### Control flow
- [x] `break` / `continue` in nested positions — recursive `_has_break_continue` + `_desugar_break_continue`.

### Contracts for complex types
- [x] `Optional[T]`, `Union[T, ...]`, `dict[K,V]`, `typing.List`, `typing.Dict` → Coq type mapping in `_py_type_to_coq`.
- [ ] Pydantic/BaseModel support for `@dataclass`-style classes beyond `ast.ClassDef` with `AnnAssign`.
- [ ] Float type: currently maps to `Z` (truncating). Needs `PrimFloat.float` in Coq IMP model.

### List comprehension with filter
- [x] `[f(x) for x in lst if p(x)]` — filter clauses (gen.ifs) already supported in `_translate_list_comp`.

---

## Todo — Expressiveness

### Two-state predicates
- [x] `old()` — `param_old = param` convention works, linter guards against misuse
- [x] Frame conditions — implicit field preservation for class fields (by omission)
- [ ] Relational properties — "output is a permutation of input", "output ⊆ input"

### Contract language
- [ ] Implication in contracts: `A → B` (conditional guarantees)
- [ ] Branch-specific postconditions — different branches need different guarantees (the `guard_pattern` problem)
- [ ] Quantified invariants: `forall i, 0 <= i < len(lst) → lst[i] <= lst[i+1]` (general quantifiers, not just all/any)
- [ ] Contract inheritance at call sites (frame composition across calls)
- [ ] Multiple loop VCGs (currently only outermost/last loop gets VCG)
- [ ] VCG carries pre-loop state context (avoid redundant invariants for unchanging facts)

### Data types & operations
- [ ] `ASlice` constructor for IMP (list slicing in body)
- [ ] Float/reals (currently only Z)
- [ ] String methods: `strip()`, `split()`, `replace()`, `lower()`, concatenation
- [ ] `for x in lst if p(x)` filter clauses in comprehensions
- [ ] Dict/set comprehensions

### Proof strength
- [ ] Induction in VCG (invariant + exit → post isn't always enough)
- [ ] Non-linear arithmetic counterexample extraction (currently falls through to unproved)
- [ ] Termination measures
- [ ] Supercompiler / symbolic evaluation of WP for concrete inputs

---

## Todo — Polish

- [x] Incremental verification cache (re-verify changed functions only)
- [x] Purity analysis / black hole detection
- [x] Library stub support (`.pyi` with requires/ensures/reads/writes)
- [x] LSP server for real-time diagnostics
- [ ] Better error reporting (map coqc errors to Python source lines)
- [ ] Eliminate regex in VCG variable extraction (`re.findall` → proper AST/IR walk)
- [ ] Delete dead code: `vcg_exit` Ltac, duplicate `return` in `_translate_for`, dead copy-paste blocks
- [ ] `_fresh_var` generator for loop counters (eliminate `_i` / `_k` hardcoding)
- [ ] LLM oracle reliability (better prompt, more retries, proof repair)
- [ ] Documentation — user guide, API reference
- [ ] CI — GitHub Action
- [ ] Exception handling (try/except as black holes)
- [ ] Branch-specific postconditions (the `guard_pattern` / `conditional_with_computation` problem)
