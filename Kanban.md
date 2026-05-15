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
- [x] MCP server `check-file` / `check-function` with `hint` param (v0.3.0)
- [x] opencode MCP integration
- [x] VCG while-exit obligation generation + SMT/Lia proofs
- [x] Multi-loop VCG (nested/sequential heuristic)
- [x] Pydantic model encoding (Record types, field access)
- [x] Class param expansion, type annotation extraction
- [x] For-loop range (1/2/3-arg, negative step)
- [x] for-in-string (`for c in text:`)
- [x] for-in-tuple (`for n in *args:`)
- [x] for-in-field (`for x in obj.field:`)
- [x] **for-in-list** (`for x in lst:`) — via `_build_for_in_name`, nested and simple
- [x] List ops: ALen, AIndex, CListNew, CListAppend, CListSet, CListPop
- [x] List slicing in contracts (SliceLenExpr) and body (slice copy)
- [x] Dict ops: CDictSet, CDictGet, CDictEnsureList, CDictAppend, CDictAppendKv, ADictLen, ADictCount
- [x] Dict iteration: `for v in d.values()`, `for k in d.keys()`, `for k,v in d.items()`
- [x] Set ops: set(), set.add(), x in set (dict-as-set model)
- [x] String parameter support (Z-array encoding, len, index, `==` literal comparison)
- [x] Boolean assignment, truthiness conversion
- [x] Function call verification (CCall with AST-based contract registry)
- [x] all() / any() predicates (SMT quantifiers), **including `range(n)` iterators**
- [x] min() / max() / sum() in contracts
- [x] List comprehension: `[f(x) for x in range(n)]`
- [x] Full Python arg lists (posonly, kwonly, vararg)
- [x] SMT counterexample extraction + `GoalStatus.counterexample` dict
- [x] SMT counterexample surfaced in MCP output
- [x] ProofLevel.COUNTEREXAMPLE and Action.PROPERTY_FALSE
- [x] VCG preconditions passed as hypotheses
- [x] Coq keyword renaming (`end` → `end_var`, etc.)
- [x] BAnd/Or exit condition extraction (De Morgan for while conds)
- [x] Result scaffold depth-aware parser (replaces regex)
- [x] Subscript in exit conditions (e.g. `stack[len(stack)-1]`) + `_coq_safe_id` sanitization
- [x] Paperchecker example: `find_brace_content` (brace-matching with depth counter)
- [x] Data contracts: char-set, sorted list, controlled vocabulary, ISO date, uniqueness
- [x] **User-defined predicates — Phase 1: simple inlining** (non-recursive, non-looping, single return)
- [x] User-defined predicates — `_param_coq_map` for correct Coq variable naming (list→lst__len)
- [x] User-defined predicates — `PredicateCallExpr` IR node for opaque (looping/recursive)
- [x] Range quantifiers in invariants: `all(p(x) for x in range(n))` + SMT NIA logic switch
- [x] SMT quantifier variable extraction fix (forall/exists/int excluded from declare-fun)
- [x] Negative tests: weak invariants → SMT counterexamples; body → WP contradiction
- [x] Off-by-one loop detection (wrong while condition → SMT counterexample)
- [x] Semantic contracts: `depth >= 0` (no unmatched bracket) + `dots <= i` (count bounded)
- [x] pytest test harness — **60 tests** (46 positive + 14 negative)

---

## Todo — Predicates (Phase 2)

- [ ] **Fix opaque predicates** — current `_holds` is vacuous (WP of while = invariant = True). Need proper verification:
  - Option A: Inline predicate's loop invariant(s) as the mathematical property
  - Option B: Verify predicate separately, use its theorem as lemma in callers
  - Predicates without invariants should be rejected (can't determine what they mean)
- [ ] Self-recursive predicates (CCall in IMP body for predicate calling itself)
- [ ] Mutually recursive predicates

---

## Todo — Expressiveness

### Two-state predicates
- [ ] `old()` / `\old(x)` — reference pre-state value in postcondition
- [ ] Frame conditions — "this function only modifies X, Y, Z"
- [ ] Relational properties — "output is a permutation of input", "output ⊆ input"

### Contract language
- [ ] Implication in contracts: `A → B` (conditional guarantees)
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
- [ ] `break` / `continue` in loops

### Proof strength
- [ ] Induction in VCG (invariant + exit → post isn't always enough)
- [ ] Non-linear arithmetic counterexample extraction (currently falls through to unproved)
- [ ] Termination measures
- [ ] Supercompiler / symbolic evaluation of WP for concrete inputs (make `_holds` meaningful)

---

## Todo — Polish

- [ ] Better error reporting (map coqc errors to Python source lines)
- [ ] Eliminate regex in VCG variable extraction (`re.findall` → proper AST/IR walk)
- [ ] Delete dead code: `vcg_exit` Ltac, duplicate `return` in `_translate_for`, dead copy-paste blocks
- [ ] `_fresh_var` generator for loop counters (eliminate `_i` / `_k` hardcoding)
- [ ] LLM oracle reliability (better prompt, more retries, proof repair)
- [ ] Documentation — user guide, API reference
- [ ] Performance — cache Coq compilation
- [ ] CI — GitHub Action
- [ ] Exception handling (try/except as black holes)
- [ ] Side-effect detection (flag impure calls)
- [ ] Incremental verification (re-verify changed functions only)
