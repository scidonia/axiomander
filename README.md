# axiomander 🦎

**Iterated specification management for Python.**  Axiomander treats
specifications as the primary artifact and implementations as a
secondary concern.  The user interacts with a minimal top-level
contract — a single surface of understanding — and the rest of the
software's specifications (callee contracts, loop invariants, frame
conditions, stub axioms) exist in support of it.  The system maintains
a persistent evidence graph that tracks which contracts are proved,
which depend on which, and which become stale when a callee changes.
Verification is not a one-time check; it is a living relationship
between specifications and code.

Write contracts as ordinary Python `assert` statements or verifier-only
`axiomander:` docstring blocks — no runtime imports, decorators, or
contract library required.  The pipeline lowers Python to an IMP
verification language, generates Coq proof obligations, proves the
deterministic cases directly, dispatches harder residuals to SMT/Hammer,
and falls back to a rocq-piler/LLM oracle.

```
Python asserts + axiomander docstrings
        │
        ▼
  contract_linter.py  →  Contract IR
        │
        ▼
  py_to_imp.py        →  IMP body
        │
        ▼
  Coq obligations     →  deterministic proof scripts (L1)
        │                                      │
        ▼                                      ▼
  residual obligations only              SMT/Hammer (L2)
                                                │
                                                ▼
                                      rocq-piler + LLM oracle (L3)
```

## Quick Start

```bash
git clone https://github.com/scidonia/axiomander
cd axiomander
uv pip install -e .

# Run the test suite
eval $(opam env)
PYTHONPATH=py .venv/bin/python -m pytest py/tests/ -v
```

## Usage

Axiomander supports two contract carriers:

1. ordinary Python `assert` statements, still useful for executable checks;
2. verifier-only `axiomander:` docstring blocks, preferred for ghost state, frames, non-runtime specifications, regex gating, and dimensional annotations.

The full contract sublanguage is documented in **[docs/CONTRACT_LANGUAGE.md](docs/CONTRACT_LANGUAGE.md)** — operators, sections, quantifiers, regex, units, exceptions, Pydantic support.

### Assert Contracts

Leading assertions are preconditions. Trailing assertions after the result assignment are postconditions. Loop-body assertions are invariants.

```python
def clamp(val: int, lo: int, hi: int) -> int:
    assert lo <= hi
    if val < lo:
        result = lo
    elif val > hi:
        result = hi
    else:
        result = val
    assert lo <= result <= hi
    assert implies(val < lo, result == lo)
    assert implies(val > hi, result == hi)
    return result
```

### Exception Contracts

Exceptions are modelled as **outcomes** — first-class values in the WP calculus. A function produces either `OReturn(result, final_state)` or `ORaise(exception_value, raise_state)`. Exception postconditions constrain what is true at the raise point.

Use the docstring `raises:` section — it is verifier-only and does not execute at runtime:

```python
def safe_divide(a: int, b: int) -> int:
    """
    axiomander:
        requires:
            a >= 0
            b >= 0
        ensures:
            result >= 0
        raises:
            ValueError: b == 0
    """
    if b == 0:
        raise ValueError
    result = a // b
    return result
```

The `raises:` section lists `ExcType: condition` pairs. Multiple exception types are each on their own line:

```text
axiomander:
    requires:
        n >= 0
    ensures:
        result >= 0
    raises:
        ValueError: n < 0
        OverflowError: n > 1000000
```

Internally, the postcondition becomes an outcome predicate:

```coq
fun o =>
  match o with
  | OReturn s => (* ensures condition *)
  | ORaise (VString "ValueError"%string) s => (* raises condition *)
  | _ => True
  end
```

### Dogfooding — Axiomander verifies its own code

Axiomander carries contracts on its own logic and verifies them. The
best example is `GoalStatus.is_proved` — the function that tells the
pipeline whether a verification goal passed:

```python
class GoalStatus:
    level: ProofLevel

    def is_proved(self) -> bool:
        """
        axiomander:
            ensures:
                implies(self.level == ProofLevel.UNPROVED,
                        result == False)
                implies(self.level == ProofLevel.COUNTEREXAMPLE,
                        result == False)
                implies(self.level != ProofLevel.UNPROVED
                        and self.level != ProofLevel.COUNTEREXAMPLE,
                        result == True)
        """
        return self.level not in (
            ProofLevel.UNPROVED, ProofLevel.COUNTEREXAMPLE)
```

This proves at Level 1 (wp_reduce + lia).  The contract uses real enum
names (`ProofLevel.UNPROVED` — Axiomander resolves them to integer
encodings from the AST), `implies()` for each conditional case, and
`self.level` attribute access (auto-flattened to `self_level: Z`).

A more complex example: `_is_string_param`, the function that determines
Coq parameter types for every other verified function.  It uses
`isinstance(annotation, ast.Name)` which Axiomander lowers to an integer
tag comparison (`annotation_tag = 1`) via the type-tag convention.
The `annotation.id == "str"` check becomes a heap variable lookup, and
`_expand_params` automatically adds `annotation_id : string` to the
Coq forall binders.  The entire decision tree proves at Level 1:

```python
def _is_string_param(annotation) -> bool:
    """
    axiomander:
        ensures:
            implies(result == True, annotation_tag == 1)
    """
    if annotation is None:
        return False
    if isinstance(annotation, ast.Name) and annotation.id == "str":
        return True
    return False
```

Other self-verified functions:

| Function | Level | What it proves |
|---|---|---|
| `GoalStatus.is_proved` (real) | 1 | Enum resolution + implies + `not in` tuple body |
| `_is_string_param` | 1 | isinstance AST dispatch via type-tag lowering |
| `_is_list_param` | 1 | isinstance + `annotation.value.id` dotted field |
| `_is_dict_param` | 1 | isinstance + `Optional[dict]` union handling |
| `_is_float_param` | 1 | isinstance + `Optional[float]` recursion |
| `_py_type_to_coq` | 1 | Python annotation → Coq type string dispatch |
| `_coq_type_of_param` | 1 | Suffix-based param type classification |
| `classify_failure` (real) | 3 | String methods + `in` operator + branch priority |
| `_escape_field` | 3 | String replacement in body |
| `_sha256` | 1 | Hash function with black-hole purity warning |
| `get_callers`/`get_callees` | 3 | list() constructor + `self.nodes` attribute access |
| `get_transitive_callers` | 3 | while+list+set with string-keyed sets |
| `build_report` | 3 | PipelineReport object construction |
| `CoqVar.to_coq` | 3 | String concatenation + contains in postcondition |
| `lower_expr` (PyIR) | 3 | Expression dispatch over PyExpr AST nodes |

Remaining gaps are tracked in [the self-verification plan](docs/self-verification-plan.md).

### Docstring Contracts

Docstring contracts are verifier-only. They do not execute at runtime and are the preferred place for ghost bindings and frame declarations.

```python
def inc(x: int) -> int:
    """
    axiomander:
        requires:
            x >= 0
        modifies:
            none
        ensures:
            result == x + 1
    """
    result = x + 1
    return result
```

Supported sections:

```text
axiomander:
    where:
        old_a: int = a
    requires:
        a >= 0
    reads:
        a
    modifies:
        none
    ensures:
        result == old_a
    raises:
        ValueError: a < 0
```

`old(x)` is shorthand for a logical pre-state binding:

```python
def frame_old_unchanged(a: int) -> int:
    """
    axiomander:
        requires:
            a >= 0
        ensures:
            result == old(a)
    """
    discard = inc(5)
    result = a
    return result
```

This is equivalent to introducing a ghost binding `old_a = a`, but without adding any Python variable.

### Function Calls and Frames

`reads:` and `modifies:` describe a callee's frame. Callers may rely on variables outside `target :: modifies` being preserved.

```python
def inc(x: int) -> int:
    """
    axiomander:
        requires:
            x >= 0
        modifies:
            none
        ensures:
            result == x + 1
    """
    result = x + 1
    return result

def frame_two_calls(a: int, b: int) -> int:
    """
    axiomander:
        requires:
            a >= 0
            b >= 0
        ensures:
            a == old(a)
            b == old(b)
            result == a + b + 2
    """
    a2 = inc(a)
    b2 = inc(b)
    result = a2 + b2
    return result
```

For CCall-heavy functions, Axiomander generates decomposed Coq obligations: frame lemmas, one stage lemma per call, a post lemma, and a composition theorem using `wp_seq_decompose`.

### Loops and Quantifiers

Runtime `assert` statements remain the current source for loop invariants and many executable facts:

```python
def build_sorted(n: int):
    assert n >= 0
    result = []
    i = 0
    while i < n:
        assert len(result) == i
        assert i <= n
        assert all(result[j] == j for j in range(i))
        result.append(i)
        i += 1
    assert all(result[j] == j for j in range(n))
    return result
```

### Dimensional Analysis — `units:`

Axiomander can track **physical and financial dimensions** through arithmetic, catching unit errors before the Coq proof runs.  Declare dimensions in a `units:` section:

```python
def gdp_per_capita(gdp: float, population: int) -> float:
    """
    axiomander:
        units:
            gdp:        [USD]
            population: [person]
            result:     [USD/person]
        requires:
            population > 0
        ensures:
            result >= 0
    """
    result = gdp / population
    return result
```

Base dimensions are **arbitrary strings** — `USD`, `GBP`, `person`, `item`, `m`, `kg`, `s`.  Incompatible dimensions are rejected as a dimension error (returns `COUNTEREXAMPLE`, skips the proof).  Exchange rates carry dimension: `rate: [USD/GBP]`.  See the [full contract language reference](docs/CONTRACT_LANGUAGE.md#5-dimensional-analysis--units) for the complete dimension expression grammar and composition rules.

### Regex Gating — `s.re_match(pattern)`

A verifier-only predicate for regex membership in contracts:

```python
def accept_phone(phone: str) -> str:
    """
    axiomander:
        requires:
            phone.re_match("[0-9]{3}-[0-9]{3}-[0-9]{4}")
        ensures:
            result.re_match("[0-9-]+")
    """
    result = phone
    return result
```

The theory-SMT oracle (Level 2b) verifies subsumption between regex patterns and produces **concrete typed counterexamples** when a postcondition contradicts a precondition.  Uses Python's `sre_parse` for pattern translation — no hand-written regex parser.  See [Section 4](docs/CONTRACT_LANGUAGE.md#4-regex-contracts--sre_matchpattern).

### Level 2b — Theory-SMT Oracle

A fourth proof tier between SMT (Level 2) and the LLM oracle (Level 3):

| Level | Mechanism | What it handles |
|---|---|---|
| 2b — theory-SMT | Z3 / CVC5 string theory | String equality, contains, prefix, suffix, regex subsumption/contradiction, float dimension scaling |

String contract goals that survive `wp_reduce` are dispatched to the `QF_SLIA` SMT logic.  Proved goals emit oracle-backed Coq axioms tagged with query hashes.  Counterexamples carry typed `TheoryValue` objects (quoted strings, unscaled floats) and are surfaced in the verification report with an explanation of which postcondition failed.

See **[docs/CONTRACT_LANGUAGE.md](docs/CONTRACT_LANGUAGE.md)** for the oracle architecture and **[docs/case-dispatch-verification.md](docs/case-dispatch-verification.md)** for the case-analysis pattern that extends this to universal properties over finite dispatch tables.

## Pipeline Tiers

| Level | Mechanism | What it handles |
|---|---|---|
| 1 — deterministic Coq | Generated obligations + bounded tactics | Assignments, conditionals, loops, decomposed CCall/frame obligations |
| 2 — SMT/Hammer | Per-obligation ATP/SMT fallback | Arithmetic and first-order residual goals |
| 3 — LLM oracle | rocq-piler + LLM | Residual proof repair over the same generated obligation file |

## Frame Conditions

Function calls use explicit frame information. A callee's docstring `modifies:` section becomes the CCall write set. The verifier proves that variables outside `target :: modifies` are unchanged across the call.

```python
def mutate(a: int) -> int:
    """
    axiomander:
        requires:
            a >= 0
        modifies:
            a
        ensures:
            result >= 0
    """
    result = a + 1
    return result
```

If a caller later tries to prove `a == old(a)` across `mutate(a)`, verification fails because `a` is declared writable.

Pure functions normally say:

```text
modifies:
    none
```

Library functions can also declare `reads`/`writes` in `.pyi` stubs. The docstring syntax and stub syntax both lower to the same internal contract map.

MCP tool `frame-report` shows contracts and frame conditions for any function.

## Testing

```bash
eval $(opam env)
PYTHONPATH=py .venv/bin/python -m pytest py/tests/ -v
```

130 pipeline tests covering arithmetic, loops, lists, dicts, sets, strings, class fields, predicates, function calls, docstring contracts, old-state syntax, reads/modifies frames, range quantifiers, stub integration, tuple/bytes/dict/set/None value comparisons, implication, loop-predicate contract inlining, user-defined predicates, exception contracts, validate_assignment enforcement, nested Pydantic models, constructor CCalls, isinstance dispatch with type-tag lowering, and collection fields.

Plus **60 dimensional analysis tests** (`py/tests/test_dim_analysis.py`) covering DimVec algebra, expression parsing, constraint checking, and end-to-end violation detection for financial, physical, and cardinality dimensions.

Plus **51 theory-SMT tests** (`py/tests/test_theory_smt.py`) covering regex translation via sre_parse, string contains/prefix dispatch, typed counterexample generation, phone-gate subsumption/contradiction, and two-function CCall regex gating.

Plus **14 case-dispatch tests** (`py/tests/test_case_extractor.py`) covering CIf/CSeq tree extraction, nested conditionals, path-condition accumulation, mutual exclusivity heuristics, and loop rejection.

## Dependencies

| Tool | Purpose |
|---|---|
| Python ≥ 3.10 | Runtime + test harness |
| OCaml ≥ 5.2 + Coq ≥ 9.0 | Proof kernel |
| dune | OCaml/Coq build |
| cvc4 or cvc5 | SMT solver (Level 2) |
| z3 | SMT solver (Level 2 — preferred for string/float theories) |
| coqpyt | Interactive Coq proof session (LLM oracle) |

## MCP Setup

Axiomander exposes its tools as an MCP server. Wire it into your editor for inline verification.

**Cursor / VS Code / Claude Desktop** — add to your MCP config (`~/.cursor/mcp.json`, `~/.vscode/mcp.json`, or `claude_desktop_config.json`):

```json
{
  "mcpServers": {
    "axiomander": {
      "command": "uv",
      "args": ["run", "python", "-m", "oracle.mcp_server"],
      "cwd": "/path/to/axiomander",
      "env": {
        "AXIOMANDER_ROOT": "/path/to/axiomander",
        "DEEPSEEK_API_KEY": "sk-...",
        "PATH": "/usr/bin:/bin:/usr/local/bin"
      }
    }
  }
}
```

**Tools exposed:**

| Tool | What it does |
|---|---|
| `check-file` | Analyze a file for contract adornment opportunities |
| `check-function` | Verify a single function (Level 1) + suggest contracts |
| `verify-function` | Full verification (Level 1 → 2 → 3) |
| `verify-changed` | Incremental — re-verify only changed functions |
| `verify-impacted` | Dry-run — show what would be re-verified |
| `explain-cache` | Show cache state for a function |
| `frame-report` | Show pre/post/invariant + frame conditions |

**Requirements:** `uv` installed, `eval $(opam env)` in the environment. The MCP server starts Coq and SMT on demand. First verification run compiles Coq (a few seconds); subsequent runs use the cache (milliseconds).

## Architecture

![Axiomander Architecture](docs/architecture.png)

```
py/
  oracle/
    contract_linter.py   # Python AST → IR (Coq + SMT targets)
    contract_ir.py       # Expression IR (Pydantic models)
    python_to_imp.py     # Python AST → IMP commands
    py_to_imp.py         # PyIR → IMP IR lowering pass
    py_ir.py             # Python function IR
    imp_ir.py            # IMP command/expression IR
    mcp_server.py        # MCP server + all tools
    purity_analyzer.py   # Purity detection + frame condition generation
    stub_loader.py       # .pyi stub parser for library contracts
    cache.py             # Incremental verification cache + dependency graph
    smt_export.py        # Coq → SMT-LIB export
    theory_smt.py        # Theory-dispatched SMT oracle (strings, floats, regex)
    client.py            # LLM oracle client
    coqpyt_session.py    # Interactive Coq proof session
    reporting.py         # Goal status + report generation
    theorem_ir.py        # Coq theorem IR generation
    obligation_gen.py    # Per-obligation Coq theorem generator
    dim_ir.py            # Dimensional analysis IR (DimVec, parsing, constraints)
    dim_checker.py       # Dimension checker (AST walker)
    shape_ir.py          # Pydantic/dataclass shape registry
    docstring_contracts.py  # axiomander: docstring parser
    advisor.py           # Contract guidance and structural hints

coq/
  Imp.v                  # IMP language (value: VZ | VBool | VUnit), clobber
  Wp.v                   # WP calculus with CCall writes enforcement
  WpTactics.v            # wp_reduce/wp_prove/frame_prove automation
  Pydantic.v             # Pydantic model support (store_field, load_field)
  RegMatch.v             # re_match placeholder definition

docs/
  CONTRACT_LANGUAGE.md   # Full contract sublanguage reference
  case-dispatch-verification.md  # Herbrand instantiation over finite dispatch
  
stubs/
  builtins.pyi           # Stub contracts for pop, add, get, len, etc.
  math_stubs.pyi         # Stub contracts for math functions
```

## Contract Discipline

- **`axiomander:` docstrings** carry rich contracts: requires, ensures, where, reads, modifies, raises, units. Full reference: [docs/CONTRACT_LANGUAGE.md](docs/CONTRACT_LANGUAGE.md).
- **`assert`** captures what types can't: `assert len(lst) > 0`, `assert depth >= 0`
- **Type annotations** carry contracts: `x: int` constrains the parameter type, `-> bool` constrains the return value
- **SMT counterexamples** tell you exactly what's missing from weak invariants. Dimension errors give typed violation reports with mismatched dimensions.
- **Loop predicates** are verified as standalone functions and inlined at call sites
- **Frame conditions** are explicit via `modifies:` section; the verifier enforces preservation of unlisted variables
