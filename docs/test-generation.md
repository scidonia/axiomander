# Axiomander Test Generation

Axiomander can generate executable tests from contracts — turning static proofs
into runnable Hypothesis property tests, a pytest verification gate, and
concrete regression tests from SMT counterexamples.

## Overview

Contracts are plain Python `assert` statements.  Because they are valid Python
expressions, they can be *executed* at runtime, not just proved statically.
This gives three levels of test generation:

| Level | What it does | Entry point |
|-------|-------------|-------------|
| A | Emit `@given` Hypothesis property tests | `axiomander gen-tests` CLI |
| B | Run formal verification as a pytest gate | `pytest_axiomander` plugin |
| C | Turn SMT counterexamples into regression tests | `counterexample_to_test()` |

---

## Level A -- Hypothesis Generator

### Usage

```bash
# Generate tests for all functions in a file
axiomander gen-tests py/examples/pydantic_contracts.py

# Generate tests for a single function
axiomander gen-tests py/examples/pydantic_contracts.py --func validate_age

# Write output to a file
axiomander gen-tests py/examples/pydantic_contracts.py -o py/tests/test_pydantic_generated.py
```

### How it works

1. **Contract extraction** (`extract_function_contracts`): parses the source
   with `ast`, classifies `assert` statements by position (before first
   assignment = precondition, after `result =` = postcondition).

2. **Strategy narrowing**: preconditions of the form `x >= N`, `x <= N`,
   `0 <= x <= N`, `len(s) > 0` are absorbed into Hypothesis strategy
   parameters (`min_value`, `max_value`, `min_size`) so Hypothesis generates
   valid inputs directly rather than filtering with `assume()`.

3. **Derived parameters**: when a precondition is `n == len(xs)`, `n` is
   marked as derived from `xs` and emitted as `n = len(xs)` in the test body
   rather than as an independent `@given` argument.

4. **`old()` snapshots**: postconditions referencing `old(x)` produce an
   `_OldSnapshot` capture before the function call.

5. **Output**: a self-contained `.py` file with `from hypothesis import given,
   assume, settings`, one `@given`-decorated test per function, and a
   `# from <module> import ...` stub at the top.

### Example output

```python
# Auto-generated property tests -- do not edit by hand.
# axiomander gen-tests py/examples/demo.py

from hypothesis import given, assume, settings
from hypothesis import strategies as st
from oracle.contract_runtime import implies, is_valid, is_shape, _OldSnapshot

# from demo import add

@given(
    x=st.integers(min_value=0),
    y=st.integers(min_value=0),
)
@settings(max_examples=200)
def test_add_contracts(x, y):
    result = add(x, y)
    assert result >= x
```

---

## Level B -- pytest Plugin

The `pytest_axiomander` plugin runs formal verification at pytest collection
time.  Install it by adding `pytest_axiomander` to `conftest.py` or
`pyproject.toml`.

### Outcome mapping

| Verifier result | pytest outcome |
|----------------|---------------|
| `PROVED` | pass |
| `COUNTEREXAMPLE` | fail (SMT model printed) |
| `UNPROVED` / `LEVEL3` | xfail (marked, not blocking) |

### Configuration

```toml
# pyproject.toml
[tool.pytest.ini_options]
axiomander_verify = true          # enable verification gate (default: false)
axiomander_timeout = 30           # seconds per function (default: 30)
axiomander_xfail_unproved = true  # xfail instead of fail for UNPROVED
```

### Usage

```bash
# Run with verification gate enabled
pytest --axiomander-verify py/tests/

# Run without gate (normal pytest)
pytest py/tests/
```

---

## Level C -- Counterexample to Regression Test

When the SMT solver returns a counterexample, `counterexample_to_test()`
emits a concrete failing pytest case with the exact inputs.

### API

```python
from oracle.property_test_gen import counterexample_to_test

rendered = counterexample_to_test(
    func_name="bounded_add",
    params=["x", "y"],
    counterexample={"x": 101, "y": 50},
    postcond_src="result <= 200",
)
```

### Example output

```python
def test_bounded_add_regression_counterexample():
    """
    Regression test: SMT counterexample for bounded_add.
    Postcondition that failed: result <= 200
    """
    x = 101
    y = 50
    result = bounded_add(x, y)
    assert result <= 200
```

---

## Contract Runtime (`oracle.contract_runtime`)

The contract runtime provides executable versions of verifier-only builtins:

| Function | Semantics |
|----------|-----------|
| `implies(p, q)` | `not p or q` |
| `is_valid(value, type_name)` | conservative `True` for unknown types |
| `is_shape(value, model_type)` | conservative `True` for unknown models |
| `re_match_pred(s, pattern)` | `re.fullmatch(pattern, s) is not None` |
| `_OldSnapshot(**kwargs)` | immutable snapshot of pre-call values |

These are imported automatically in generated test files.

---

## Python API

```python
from oracle.property_test_gen import (
    generate_tests,           # str -> str: emit Hypothesis tests
    extract_function_contracts,  # str, str -> FunctionContracts
    counterexample_to_test,   # func_name, params, ce, postcond_src -> str
    FunctionContracts,        # dataclass
    ParamStrategy,            # dataclass with .to_hypothesis() -> str
)
```

### `generate_tests(source, func_name=None, module_path="")`

- `source`: Python source code string
- `func_name`: if given, generate tests only for this function
- `module_path`: used to emit `from <module> import ...` in the header
- Returns: a string of valid Python source

### `extract_function_contracts(source, func_name)`

Returns a `FunctionContracts` dataclass with:
- `func_name`, `params`, `param_types`
- `preconditions`, `postconditions` (AST nodes)
- `precond_sources`, `postcond_sources` (source strings)
- `old_bindings` (dict mapping `old_x` -> expression)
- `strategies` (list of `ParamStrategy`)

### `ParamStrategy.to_hypothesis()`

Returns the Hypothesis strategy expression string, e.g.
`"st.integers(min_value=0, max_value=100)"`.  Returns `""` for derived
parameters (they are emitted as assignments in the test body instead).

---

## Non-goals

- No changes to the Coq WP calculus.
- Changes to `pipeline.py` are out of scope.
- The generator does not run the generated tests -- use `pytest` for that.
