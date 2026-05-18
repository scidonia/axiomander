# axiomander

A Hoare-logic verification pipeline for Python. Write contracts as plain `assert` statements. The pipeline translates them into IMP, formalises proof obligations in Coq, dispatches easy goals to SMT (cvc4), and falls back to an LLM oracle.

```
Python assert contracts
        │
        ▼
  contract_linter.py  →  IR (Pydantic AST)  →  Coq  →  wp_prove (L1)
        │                                      │
        ▼                                      ▼
  python_to_imp.py   →  IMP body              SMT (cvc4)  (L2)
                                                   │
                                                   ▼
                                              LLM oracle  (L3)
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

Contracts are plain `assert` statements — the verifier classifies them by position:

```python
# Implication — conditional guarantees via implies()
def clamp(val, lo, hi):
    assert lo <= hi                         # precondition
    if val < lo: result = lo
    elif val > hi: result = hi
    else: result = val
    assert lo <= result <= hi               # postcondition
    assert implies(val < lo, result == lo)  # branch-precise: "if too low, clamped to lo"
    assert implies(val > hi, result == hi)  # "if too high, clamped to hi"
    return result

# Dicts + key operations — test membership, insert, aggregate
def count_groups(mappings):
    assert len(mappings) > 0                 # precondition: non-empty
    result = {}
    i = 0
    count = 0
    while i < len(mappings):
        assert count == i                     # invariant: processed count
        assert i <= len(mappings)
        key = mappings[i]
        if key not in result:                  # membership test
            result[key] = []                  # insert new key
        result[key].append(1)                 # mutate value
        count += 1
        i += 1
    assert count == len(mappings)            # postcondition: all elements counted
    return count

# Quantifiers — all() with generator expressions
def build_sorted(n):
    assert n >= 0                            # precondition
    result = []
    i = 0
    while i < n:
        assert len(result) == i               # invariant: length tracks progress
        assert i <= n
        assert all(result[j] == j for j in range(i))  # invariant: all elements correct
        result.append(i)
        i += 1
    assert all(result[j] == j for j in range(n))     # postcondition: fully sorted
    return result

# Dict group-by — counted aggregation
def count_groups(mappings):
    assert len(mappings) > 0                 # precondition
    result = {}
    i = 0
    count = 0
    while i < len(mappings):
        assert count == i                     # invariant: processed count
        assert i <= len(mappings)
        key = mappings[i]
        if key not in result:
            result[key] = []
        result[key].append(1)
        count += 1
        i += 1
    assert count == len(mappings)            # postcondition: all elements counted
    return count
```

## CLI

```bash
# Analyze a file for contract opportunities
axiomander-mcp check-file path/to/file.py

# Verify a single function
axiomander-mcp check-function --function add path/to/file.py

# Verify with hammer hint (SMT ATP fallback)
axiomander-mcp check-function --function add --hint hammer path/to/file.py
```

## MCP Integration

Add to your `~/.config/opencode/opencode.json`:

```json
"axiomander": {
  "type": "local",
  "command": ["bash", "-c", "eval $(opam env) 2>/dev/null; exec axiomander-mcp"],
  "enabled": true,
  "environment": {
    "DEEPSEEK_API_KEY": "{env:DEEPSEEK_API_KEY}",
    "AXIOMANDER_ROOT": "/path/to/axiomander",
    "PYTHONPATH": "/path/to/axiomander/py"
  }
}
```

## Supported Operations

| Category | Operations |
|---|---|
| Arithmetic | +, -, *, /, //, %, ** |
| Comparisons | <, <=, >, >=, ==, !=, is, is not, in, not in |
| Logic | and, or, not |
| Lists | `len()`, `lst[i]`, `lst.append()`, `lst.pop()`, `lst = []`, `lst[i:j]` |
| Dicts | `d[key]`, `key in d`, `d[key] = val`, `len(d)`, `d.keys()`, `d.values()`, `d.items()` |
| Sets | `set()`, `s.add(x)`, `x in s` |
| Strings | `len(s)`, `s[i]`, `s == "literal"` |
| Functions | `min()`, `max()`, `sum()`, `all()`, `any()`, `abs()`, `len()` |
| Loops | `while`, `for i in range(n)`, `for x in lst`, `for c in s`, `for x in d.values()` |
| Conditionals | `if/else`, `elif`, `or`/`and` in conditions |
| Functions | Cross-function verification via CCall |
| Builtins | `isinstance()`, `int()`, `float()`, `bool()` |

## Pipeline Tiers

| Level | Mechanism | What it handles |
|---|---|---|
| 1 — `wp_prove` | Structural recursion + `lia` | Assignments, conditionals, linear arithmetic |
| 2 — SMT | cvc4 subprocess (QF_NIA) | Non-linear VCG, division, multiplication |
| 3 — LLM oracle | DeepSeek via coqpyt | Complex invariants, quantifiers |

## Frame Conditions

Functions carry implicit frame conditions via `CCall` with a `writes` set. The verifier proves that variables outside a callee's declared writes are unchanged across the call. Callers can snapshot values before a call and assert they survive.

```python
def inc(x: int):
    assert x >= 0
    result = x + 1           # writes: {result}
    return result

def frame_old_unchanged(a: int):
    assert a >= 0
    old_a = a                # snapshot
    discard = inc(5)
    assert a == old_a        # frame: inc didn't touch 'a'
    return a
```

Library functions declare `reads`/`writes` in `.pyi` stubs:

```python
# stubs/builtins.pyi
def pop(lst: list) -> int:
    """requires: True
    ensures:  True
    reads:    lst
    writes:   lst"""         # pop mutates the list
```

MCP tool `frame-report` shows contracts and frame conditions for any function:

```
## `frame_stub_pop`
### Preconditions
  assert x>=0
### Postconditions
  assert result >= old_x
### Frame
  preserves: {x}
### Callee Effects
  ↳ `pop()` reads {lst} writes {lst}
```

## Testing

```bash
eval $(opam env)
PYTHONPATH=py .venv/bin/python -m pytest py/tests/ -v
```

85 tests (17 negative, 68 positive) covering arithmetic, loops, lists, dicts, sets, strings, class fields, predicates, function calls, range quantifiers, frame conditions, stub integration, tuple/bytes/dict/set/None value comparisons, and implication.

## Architecture

```
py/
  oracle/
    contract_linter.py   # Python AST → IR (Coq + SMT targets)
    contract_ir.py       # Expression IR (Pydantic models)
    python_to_imp.py     # Python AST → IMP commands
    mcp_server.py        # MCP server + all tools
    purity_analyzer.py   # Purity detection + frame condition generation
    stub_loader.py       # .pyi stub parser for library contracts
    cache.py             # Incremental verification cache + dependency graph
    smt_export.py        # Coq → SMT-LIB export
    client.py            # LLM oracle client
    coqpyt_session.py    # Interactive Coq proof session
    reporting.py         # Goal status + report generation

coq/
  Imp.v                  # IMP language (value: VZ | VBool | VUnit), clobber
  Wp.v                   # WP calculus with CCall writes enforcement
  WpTactics.v            # wp_reduce/wp_prove/frame_prove automation
  Pydantic.v             # Pydantic model support (store_field, load_field)
stubs/
  builtins.pyi           # Stub contracts for pop, add, get, len, etc.
  math_stubs.pyi         # Stub contracts for math functions
```

## Contract Discipline

- **Type annotations** document preconditions: `def f(x: int, lst: list[str]) -> bool`
- **`assert`** captures what types can't: `assert len(lst) > 0`, `assert depth >= 0`
- **Contracts** document pre/post/invariant in docstrings
- **SMT counterexamples** tell you exactly what's missing from weak invariants
