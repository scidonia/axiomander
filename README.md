# axiomander 🦎

**A gold standard verification system for Python.** Write contracts as plain `assert` statements — no imports, no decorators, no DSL. The pipeline formalises proof obligations in Coq, dispatches easy goals to SMT, and falls back to an LLM oracle. Aims to bring theorem-prover-grade verification to a mass audience with a near-zero barrier to entry, while remaining competitive with bespoke systems like [F*](https://en.wikipedia.org/wiki/F*) and [Dafny](https://en.wikipedia.org/wiki/Dafny).

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
# Contracts are plain assert statements — zero imports, zero decorators.
# Under python -O, all asserts are stripped. Ghost snapshots inside
# if __debug__: blocks are stripped too. Verification has zero runtime cost.

# Field constraints lifted to compile-time proof (Pydantic in spirit)
def transfer(balances: dict[str, int], sender: str, receiver: str, amount: int) -> int:
    assert amount >= 0
    assert sender in balances
    assert balances[sender] >= amount            # precondition: sufficient funds
    if __debug__:
        old_sender = balances[sender]
        if receiver in balances:
            old_receiver = balances[receiver]
        else:
            old_receiver = 0
    balances[sender] -= amount
    if receiver not in balances:
        balances[receiver] = 0
    balances[receiver] += amount
    result = 1
    assert balances[sender] >= 0                 # constraint preserved: no overdraft
    assert (balances[sender] + balances[receiver] == 
            old_sender + old_receiver)           # conservation of money
    assert result == 1
    return result

# Implication — conditional guarantees via implies()
def clamp(val: int, lo: int, hi: int):
    assert lo <= hi                         # precondition
    if val < lo: result = lo
    elif val > hi: result = hi
    else: result = val
    assert lo <= result <= hi               # postcondition
    assert implies(val < lo, result == lo)  # branch-precise: "if too low, clamped to lo"
    assert implies(val > hi, result == hi)  # "if too high, clamped to hi"
    return result

# Dicts — build and verify with assertions only (Python -O drops them)
# The semantic property lives in a pure predicate, inlined at the call site.
def is_square_dict(d: dict[int, int], n: int) -> bool:
    return all(d[j] == j * j for j in range(n))

def square_dict(n: int):
    assert n >= 0                            # precondition
    result = {}
    i = 0
    while i < n:
        assert i <= n                         # invariant: bounds
        assert all(result[j] == j * j for j in range(i))  # invariant: partial dict
        result[i] = i * i                     # store square
        i += 1
    assert is_square_dict(result, n)          # postcondition: every key maps to its square
    return result

# Pydantic-style field constraints — automatic from Field(ge=0)
class Account:
    balance: int = Field(ge=0)
    overdraft_limit: int = Field(ge=0)

def withdraw(acct: Account, amount: int) -> int:
    """Withdraw amount. Returns 1 on success, 0 if insufficient funds."""
    assert amount >= 0
    if __debug__:
        old_balance = acct.balance
    if amount > acct.balance + acct.overdraft_limit:
        result = 0
        assert result == 0
        return result
    acct.balance -= amount
    result = 1
    assert acct.balance + acct.overdraft_limit >= 0  # constraint preserved
    assert result == 1
    return result

# Quantifiers — all() with generator expressions
def build_sorted(n: int):
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

# Loop predicates — predicates with loops are verified separately;
# their postconditions are inlined at call sites.
def geq_loop(x: int, n: int) -> bool:
    assert n >= 0                               # precondition
    r = x
    while r < n:
        r = r + 1
    result = (r >= n)
    assert implies(result == 1, x >= n)         # semantic postcondition
    return result

def double(n: int):
    assert n >= 0
    result = n * 2
    assert geq_loop(result, n)                  # expands to: n*2 >= n
    return result

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
    """requires: len(lst) >= 1
    ensures:  True
    reads:    lst
    writes:   lst"""         # pop mutates the list; returns list element (not necessarily int)
```

MCP tool `frame-report` shows contracts and frame conditions for any function:

```
## `frame_stub_pop`
### Preconditions
  assert x>=0
### Postconditions
  assert result >= old_x
### Callee Effects
  ↳ `pop()` requires len(lst) >= 1, reads {lst} writes {lst}
```

## Testing

```bash
eval $(opam env)
PYTHONPATH=py .venv/bin/python -m pytest py/tests/ -v
```

108 tests (32 negative, 76 positive) covering arithmetic, loops, lists, dicts, sets, strings, class fields, predicates, function calls, range quantifiers, frame conditions, stub integration, tuple/bytes/dict/set/None value comparisons, implication, and loop-predicate contract inlining.

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

- **Type annotations** carry contracts: `x: int` constrains the parameter type, `-> bool` constrains the return value
- **`assert`** captures what types can't: `assert len(lst) > 0`, `assert depth >= 0`
- **`if __debug__:`** marks ghost snapshots: `if __debug__: old_x = x`. Stripped by `python -O`.
- **`python -O`** strips all assert statements and `if __debug__:` blocks. Verification has zero production overhead.
- **Contracts** document pre/post/invariant in docstrings
- **SMT counterexamples** tell you exactly what's missing from weak invariants
- **Loop predicates** are verified as standalone functions. Their semantic postconditions (guarded by `implies(result == 1, ...)`) are inlined at call sites. Pure predicates are inlined directly; predicates without postconditions are rejected.
