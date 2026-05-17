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

```python
def add(a, b):
    assert True              # precondition
    result = a + b
    assert result == a + b   # postcondition
    return result

def sum_to(n):
    assert n >= 0            # precondition
    acc = 0
    i = 0
    while i < n:
        assert acc == i * (i + 1) // 2   # invariant
        assert i <= n                     # invariant
        i = i + 1
        acc = acc + i
    assert acc == n * (n + 1) // 2       # postcondition
    assert i == n                         # postcondition
    return acc
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

## Testing

```bash
eval $(opam env)
PYTHONPATH=py .venv/bin/python -m pytest py/tests/ -v
```

34 tests covering the full feature set.

## Architecture

```
py/
  oracle/
    contract_linter.py   # Python AST → IR (Coq + SMT targets)
    contract_ir.py       # Expression IR (Pydantic models)
    python_to_imp.py     # Python AST → IMP commands
    mcp_server.py        # MCP server (check-file, check-function)
    smt_export.py        # Coq → SMT-LIB export
    client.py            # LLM oracle client
    coqpyt_session.py    # Interactive Coq proof session
    reporting.py         # Goal status + report generation

coq/
  Imp.v                  # IMP language + aexp/bexp (mutual), ae/beval, com, ceval
  Wp.v                   # WP calculus + VCG definitions
  WpTactics.v            # wp_reduce/wp_prove automation
```

## Contract Discipline

- **Type annotations** document preconditions: `def f(x: int, lst: list[str]) -> bool`
- **`assert`** captures what types can't: `assert len(lst) > 0`, `assert depth >= 0`
- **Contracts** document pre/post/invariant in docstrings
- **SMT counterexamples** tell you exactly what's missing from weak invariants
