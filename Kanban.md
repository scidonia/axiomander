# Kanban

## Done

- [x] IMP language + WP calculus + soundness (Coq)
- [x] `wp_reduce` / `wp_prove` automation tactics
- [x] Coq-hammer integration (cvc4 + eprover)
- [x] `--hint hammer` CLI flag (From Hammer Require Import, ATP limits, try lia; try hammer)
- [x] coq-lsp + coqpyt installed; `coqpyt_session.py` for live proof interaction
- [x] LLM oracle wired to coqpyt — validates proofs via live LSP session (replaces coqc)
- [x] BOr conditional handling — `Bool.orb_*_iff` in auto-gen template + LLM prompt
- [x] Python contract linter (`assert` → classified + Coq translation)
- [x] Python → IMP body translator
- [x] MCP server (`check-file`, `check-function`)
- [x] opencode integration (global `verify-contracts-mcp`)
- [x] VCG while-exit obligation generation + lia-based proofs
- [x] VCG while-exit proof for linear loops (count_to example)
- [x] Conditional branch handling (if/else, nested — lia's Z.leb support)
- [x] Auto-generated proof template (intros + wp_reduce + conditional split)
- [x] LLM oracle context fix (valid Coq only in validation source)
- [x] Black hole theory (havoc semantics, condition splitting)
- [x] Pydantic model encoding (Record types, field access, store/load)
- [x] Auth0 user database example (verified round-trip, session isolation)
- [x] Binary search specification + simple cases
- [x] Invariant guard (blocks false positives on weak invariants)
- [x] Missing contract detection + adornment suggestions
- [x] LLM-powered guidance (templated fallback, DeepSeek-ready)
- [x] Class param expansion (account → account_balance, account_overdraft in Coq theorem)
- [x] Type annotation extraction — Python `int→Z`, `bool→bool`, `str→string` in Coq params
- [x] For-loop range translation (1/2/3-arg variants, default invariants, `i+1<=n` condition)
- [x] VCG proof fix — `apply Z.leb_gt in Hexit` + dynamic intros pattern
- [x] Name leak bug — `for name in re.findall(...)` overwrote function name

## In Progress

- [ ] LLM prompt tuning — teach division/non-linear patterns, improve error recovery
- [ ] VCG: invariants should include unaffected-variable constraints (s"n" = n)

## Todo — Blockers for Real Programs

### Record Types & Objects
- [x] Generate `Record` definitions from Python `class`/`@dataclass`
- [x] State-scoped attribute access (`account.balance` → `s "account.balance"%string`)
- [x] Proper AST-based scoping (no regex hacks)
- [x] Context-aware linter (preconditions use params, postconditions use state)
- [x] Init state for class params (generate `store_field` calls for each field)
- [x] Class param expansion (account → account_balance, account_overdraft in Coq theorem)
- [ ] Handle nested objects (`order.customer.name`)

### IMP Language Extensions
- [x] Add `AMod` (modulo) and `ADiv` (division) to `aexp`
- [x] Add `BOr` constructor to `bexp` (short-circuit `or`)
- [x] Extend `beval` for `BOr`
- [x] Extend Python translator for `AMod`, `ADiv`, `BOr`

### For Loops
- [x] Fix `CSeq` arity bug in for-loop body translation
- [x] Translate `for i in range(n): body` → `i=0; while i+1<=n: body; i+=1`
- [x] Support `range(start, stop)`, `range(start, stop, step)` variants
- [x] Default invariant generation for for-loops (bounds derived from range args)
- [x] User-provided invariants from for-loop body asserts (via InvariantFinder)
- [x] For-loop `i < n` → `BLe (i+1) n` (not `BLe i n` — off-by-one fixed)
- [x] VCG exit condition: `apply Z.leb_gt in Hexit` in the proof
- [x] For-loop triggers VCG generation (was only checking `ast.While`)
- [ ] Extract variant (termination measure) from `range` bounds

### Variable Scoping
- [x] Fix `_scope_vars` to wrap ALL non-parameter variables as `s "name"%string`
- [x] Handle `result` in postconditions
- [ ] Handle loop variables (`i`, `j`) in invariants — scoped via `_scope_vars`

### Collections & Strings

Blocked on: IMP language extensions for heap/collections, Python→IMP translator
support for list/dict AST nodes, and WP semantics for collection operations.

#### List / Array (bounded-length)
- [ ] Add `list Z` type to IMP state model (keyed by `"name" ++ index`)
- [ ] Add `ALen`, `AIndex`, `ASlice` constructors to `aexp`
- [ ] Add `CAssignIndex` (list assignment: `lst[i] = e`) to `com`
- [ ] Extend `aeval`/`ceval` for list operations
- [ ] WP semantics: `wp (CAssignIndex name idx val) Q s` = ... ?
- [ ] Support `len(lst)`, `lst[i]`, `lst[i:j]` in contracts
- [ ] Support `lst.append(e)`, `lst.pop()` as command translations

#### For loops over collections
- [ ] Translate `for x in lst: body` → IMP while loop with index variable
- [ ] Translate `for i in range(n): body` → `i=0; while i<n: body; i+=1`
- [ ] Extract invariant from loop body assertions in for-loops
- [ ] Extract variant (termination measure) from `range` bounds

#### Comprehensions
- [ ] List comprehension: `[f(x) for x in lst if p(x)]` → IMP loop + accumulator
- [ ] Dict comprehension: `{k: v for x in lst if p(x)}` → IMP loop + dict model
- [ ] Set comprehension: `{x for x in lst if p(x)}` → IMP loop + list model (dedup)
- [ ] Postcondition generation for comprehension results

#### Predicates
- [ ] Support `all(p(x) for x in lst)` in contracts — ∀ quantifier over list
- [ ] Support `any(p(x) for x in lst)` in contracts — ∃ quantifier over list
- [ ] Support `sum(lst)`, `min(lst)`, `max(lst)` in contracts

#### Dictionaries
- [ ] Add dict type to IMP state model (keyed by `"name.key"` string)
- [ ] Support `d[key]`, `key in d`, `d.get(key, default)`, `len(d)`
- [ ] Handle `d[key] = value` as state update
- [ ] Model `dict.items()`, `dict.keys()`, `dict.values()` iteration

#### Strings
- [ ] String operations (`s[0]`, `s.strip()`, `len(s)`, `s.split()`)
- [ ] String concatenation and slicing in contracts
- [ ] `in` / `not in` operators for substring matching

## Todo — Completeness

- [x] Wire DeepSeek LLM oracle (prove VCG obligations, generate invariant suggestions)
- [x] Prompt improvement: include store_field/upd/flat_key definitions in LLM context
- [ ] VCG proofs for division-using invariants (need nia or different encoding)
- [x] Path obligations: nested CIf handled by lia's Z.leb support in Coq 8.20+ (see clamp test)
- [x] LLM oracle context fix — separated Coq-valid context from LLM guidance text (hint param)
- [x] Auto-generated proof template fix — added missing `intros.` before conditional proofs
- [x] `--hint hammer` — imports hammer, sets ATP limits, uses `try lia; try hammer` fallback
- [ ] SMT export — dump Coq goals to SMT-LIB, call Z3 directly
- [ ] Type inference from Python annotations (`x: int` → `Z`, `x: str` → `string`)
- [ ] Loop termination measures (`assert n - i >= 0`)
- [ ] Function composition — verify callers using callee contracts
- [ ] Exception handling — model `try/except` as black holes
- [ ] Side-effect detection — flag impure calls (`print`, `open`, I/O)
- [ ] Incremental verification — re-verify only changed functions

## Todo — Polish

- [ ] Better error reporting — map coqc errors to Python source lines
- [ ] Counterexample extraction — when SMT finds SAT, show violating input
- [ ] Test suite — pytest for linter, translator, MCP tools
- [ ] Documentation — user guide, API reference, example walkthrough
- [ ] Performance — cache Coq compilation, parallel function verification
- [ ] CI integration — GitHub Action that runs verification on PRs
