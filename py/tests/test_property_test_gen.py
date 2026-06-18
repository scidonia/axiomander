"""Tests for py/oracle/property_test_gen.py -- Hypothesis test generator.

Public API under test:
    generate_tests(source, func_name=None, module_path="") -> str
    extract_function_contracts(source, func_name) -> FunctionContracts
    counterexample_to_test(func_name, params, counterexample, postcond_src) -> str

Internal helpers tested via the public API only (no private-function imports).
"""

import ast
import textwrap
import pytest

from oracle.property_test_gen import (
    generate_tests,
    extract_function_contracts,
    counterexample_to_test,
    FunctionContracts,
    ParamStrategy,
)


# ---------------------------------------------------------------------------
# Source fixtures
# ---------------------------------------------------------------------------

SIMPLE_ADD = textwrap.dedent("""\
    def add(x: int, y: int) -> int:
        assert x >= 0
        assert y >= 0
        result = x + y
        assert result >= x
        return result
""")

BOUNDED_ADD = textwrap.dedent("""\
    def bounded_add(x: int, y: int) -> int:
        assert 0 <= x <= 100
        assert 0 <= y <= 100
        result = x + y
        assert result >= 0
        assert result <= 200
        return result
""")

STRING_FUNC = textwrap.dedent("""\
    def greet(name: str) -> str:
        assert len(name) > 0
        result = "Hello, " + name
        assert len(result) > len(name)
        return result
""")

LIST_FUNC = textwrap.dedent("""\
    def first_elem(xs: list, n: int) -> int:
        assert n == len(xs)
        assert n > 0
        result = xs[0]
        assert result >= 0
        return result
""")

NO_CONTRACTS = textwrap.dedent("""\
    def plain(x: int) -> int:
        return x + 1
""")

MULTI_FUNC = textwrap.dedent("""\
    def inc(x: int) -> int:
        assert x >= 0
        result = x + 1
        assert result > x
        return result

    def dec(x: int) -> int:
        assert x > 0
        result = x - 1
        assert result >= 0
        return result
""")

FLOAT_FUNC = textwrap.dedent("""\
    def scale(x: float, factor: float) -> float:
        assert factor > 0.0
        result = x * factor
        assert result >= 0.0
        return result
""")

OLD_FUNC = textwrap.dedent("""\
    def increment(x: int) -> int:
        assert x >= 0
        result = x + 1
        assert result == old(x) + 1
        return result
""")


# ---------------------------------------------------------------------------
# extract_function_contracts
# ---------------------------------------------------------------------------

class TestExtractFunctionContracts:
    def test_returns_function_contracts(self):
        fc = extract_function_contracts(SIMPLE_ADD, "add")
        assert isinstance(fc, FunctionContracts)
        assert fc.func_name == "add"

    def test_params_extracted(self):
        fc = extract_function_contracts(SIMPLE_ADD, "add")
        assert "x" in fc.params
        assert "y" in fc.params

    def test_param_types_int(self):
        fc = extract_function_contracts(SIMPLE_ADD, "add")
        assert fc.param_types.get("x") == "int"
        assert fc.param_types.get("y") == "int"

    def test_param_types_str(self):
        fc = extract_function_contracts(STRING_FUNC, "greet")
        assert fc.param_types.get("name") == "str"

    def test_param_types_list(self):
        fc = extract_function_contracts(LIST_FUNC, "first_elem")
        assert fc.param_types.get("xs") == "list"

    def test_param_types_float(self):
        fc = extract_function_contracts(FLOAT_FUNC, "scale")
        assert fc.param_types.get("x") == "float"

    def test_preconditions_extracted(self):
        fc = extract_function_contracts(SIMPLE_ADD, "add")
        assert len(fc.preconditions) >= 1

    def test_postconditions_extracted(self):
        fc = extract_function_contracts(SIMPLE_ADD, "add")
        assert len(fc.postconditions) >= 1

    def test_unknown_function_returns_empty(self):
        fc = extract_function_contracts(SIMPLE_ADD, "nonexistent")
        assert fc.func_name == "nonexistent"
        assert fc.params == []
        assert fc.preconditions == []

    def test_no_contracts_function(self):
        fc = extract_function_contracts(NO_CONTRACTS, "plain")
        assert fc.func_name == "plain"
        assert "x" in fc.params
        # No preconditions or postconditions
        assert fc.preconditions == []
        assert fc.postconditions == []

    def test_syntax_error_returns_empty(self):
        fc = extract_function_contracts("def broken(x:\n    pass", "broken")
        assert fc.func_name == "broken"
        assert fc.params == []

    def test_old_bindings_collected(self):
        fc = extract_function_contracts(OLD_FUNC, "increment")
        # old(x) should produce an old_x binding
        assert "old_x" in fc.old_bindings

    def test_precond_sources_populated(self):
        fc = extract_function_contracts(SIMPLE_ADD, "add")
        assert len(fc.precond_sources) >= 1
        # Source text should be non-empty strings
        for src in fc.precond_sources:
            assert isinstance(src, str)
            assert len(src) > 0

    def test_postcond_sources_populated(self):
        fc = extract_function_contracts(SIMPLE_ADD, "add")
        assert len(fc.postcond_sources) >= 1


# ---------------------------------------------------------------------------
# ParamStrategy.to_hypothesis
# ---------------------------------------------------------------------------

class TestParamStrategy:
    def test_int_no_bounds(self):
        s = ParamStrategy(name="x", py_type="int")
        h = s.to_hypothesis()
        assert "st.integers(" in h

    def test_int_min_value(self):
        s = ParamStrategy(name="x", py_type="int", min_value=0)
        h = s.to_hypothesis()
        assert "min_value=0" in h

    def test_int_max_value(self):
        s = ParamStrategy(name="x", py_type="int", max_value=100)
        h = s.to_hypothesis()
        assert "max_value=100" in h

    def test_int_both_bounds(self):
        s = ParamStrategy(name="x", py_type="int", min_value=0, max_value=100)
        h = s.to_hypothesis()
        assert "min_value=0" in h
        assert "max_value=100" in h

    def test_float_strategy(self):
        s = ParamStrategy(name="x", py_type="float")
        h = s.to_hypothesis()
        assert "st.floats(" in h
        assert "allow_nan=False" in h

    def test_str_strategy(self):
        s = ParamStrategy(name="name", py_type="str")
        h = s.to_hypothesis()
        assert "st.text(" in h

    def test_str_min_size(self):
        s = ParamStrategy(name="name", py_type="str", min_size=1)
        h = s.to_hypothesis()
        assert "min_size=1" in h

    def test_list_strategy(self):
        s = ParamStrategy(name="xs", py_type="list")
        h = s.to_hypothesis()
        assert "st.lists(" in h

    def test_bool_strategy(self):
        s = ParamStrategy(name="flag", py_type="bool")
        h = s.to_hypothesis()
        assert "st.booleans()" in h

    def test_derived_param_returns_empty(self):
        s = ParamStrategy(name="n", py_type="int", derived_from="xs", derived_expr="len(xs)")
        h = s.to_hypothesis()
        assert h == ""


# ---------------------------------------------------------------------------
# generate_tests -- integration
# ---------------------------------------------------------------------------

class TestGenerateTests:
    def test_simple_add_produces_valid_python(self):
        output = generate_tests(SIMPLE_ADD)
        ast.parse(output)  # must not raise

    def test_simple_add_has_hypothesis_import(self):
        output = generate_tests(SIMPLE_ADD)
        assert "from hypothesis import" in output

    def test_simple_add_has_strategies_import(self):
        output = generate_tests(SIMPLE_ADD)
        assert "strategies as st" in output

    def test_simple_add_has_test_function(self):
        output = generate_tests(SIMPLE_ADD)
        assert "def test_add_contracts(" in output

    def test_simple_add_has_given_decorator(self):
        output = generate_tests(SIMPLE_ADD)
        assert "@given(" in output

    def test_simple_add_has_assume(self):
        # SIMPLE_ADD preconditions (x >= 0, y >= 0) are absorbed into min_value=0
        # strategies, so no assume() is emitted.  Use STRING_FUNC which has a
        # len(name) > 0 precondition that cannot be absorbed into a strategy bound.
        output = generate_tests(STRING_FUNC)
        assert "assume(" in output

    def test_simple_add_has_assert(self):
        output = generate_tests(SIMPLE_ADD)
        assert "assert " in output

    def test_simple_add_calls_function(self):
        output = generate_tests(SIMPLE_ADD)
        assert "add(" in output

    def test_bounded_add_narrows_strategies(self):
        output = generate_tests(BOUNDED_ADD)
        # x in [0, 100] should produce max_value=100
        assert "100" in output

    def test_multi_func_generates_both(self):
        output = generate_tests(MULTI_FUNC)
        assert "def test_inc_contracts(" in output
        assert "def test_dec_contracts(" in output

    def test_filter_by_function_name_inc(self):
        output = generate_tests(MULTI_FUNC, func_name="inc")
        assert "def test_inc_contracts(" in output
        assert "def test_dec_contracts(" not in output

    def test_filter_by_function_name_dec(self):
        output = generate_tests(MULTI_FUNC, func_name="dec")
        assert "def test_dec_contracts(" in output
        assert "def test_inc_contracts(" not in output

    def test_no_contracts_skips_test(self):
        output = generate_tests(NO_CONTRACTS)
        # No postconditions -- should emit a comment, not a test function
        assert "def test_plain_contracts(" not in output
        assert "plain" in output  # but the function is mentioned

    def test_string_func_uses_text_strategy(self):
        output = generate_tests(STRING_FUNC)
        assert "st.text(" in output

    def test_list_func_uses_lists_strategy(self):
        output = generate_tests(LIST_FUNC)
        assert "st.lists(" in output

    def test_float_func_uses_floats_strategy(self):
        output = generate_tests(FLOAT_FUNC)
        assert "st.floats(" in output

    def test_module_path_in_import(self):
        output = generate_tests(SIMPLE_ADD, module_path="py/examples/demo.py")
        # module_path="py/examples/demo.py" -> base="demo" -> "from demo import add"
        assert "demo" in output

    def test_no_module_path_comment(self):
        output = generate_tests(SIMPLE_ADD, module_path="")
        # Without a module path, should emit a comment import
        assert "# from <module> import" in output

    def test_output_has_test_functions(self):
        output = generate_tests(SIMPLE_ADD)
        tree = ast.parse(output)
        func_names = [
            node.name for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef)
        ]
        assert any(n.startswith("test_") for n in func_names)

    def test_syntax_error_source_returns_comment(self):
        output = generate_tests("def broken(x:\n    pass")
        assert "axiomander" in output.lower() or "error" in output.lower()

    def test_empty_source_returns_comment(self):
        output = generate_tests("")
        # Empty source has no functions
        assert "no functions found" in output or output.strip() == ""

    def test_float_func_valid_python(self):
        output = generate_tests(FLOAT_FUNC)
        ast.parse(output)

    def test_old_func_snapshot_in_output(self):
        output = generate_tests(OLD_FUNC)
        # old() bindings should produce _OldSnapshot usage
        assert "_OldSnapshot" in output or "_snap" in output

    def test_contract_runtime_import_present(self):
        output = generate_tests(SIMPLE_ADD)
        assert "contract_runtime" in output

    def test_header_docstring_present(self):
        output = generate_tests(SIMPLE_ADD)
        assert "Auto-generated property tests" in output


# ---------------------------------------------------------------------------
# counterexample_to_test
# ---------------------------------------------------------------------------

class TestCounterexampleToTest:
    def test_basic_regression_function_name(self):
        rendered = counterexample_to_test(
            func_name="add",
            params=["x", "y"],
            counterexample={"x": 0, "y": -1},
        )
        assert "def test_add_regression_counterexample():" in rendered

    def test_inputs_bound(self):
        rendered = counterexample_to_test(
            func_name="add",
            params=["x", "y"],
            counterexample={"x": 5, "y": 3},
        )
        assert "x = 5" in rendered
        assert "y = 3" in rendered

    def test_function_called(self):
        rendered = counterexample_to_test(
            func_name="add",
            params=["x", "y"],
            counterexample={"x": 0, "y": -1},
        )
        assert "add(x, y)" in rendered

    def test_postcond_src_in_comment(self):
        rendered = counterexample_to_test(
            func_name="add",
            params=["x", "y"],
            counterexample={"x": 0, "y": -1},
            postcond_src="result >= x",
        )
        assert "result >= x" in rendered

    def test_missing_param_defaults_to_zero(self):
        rendered = counterexample_to_test(
            func_name="add",
            params=["x", "y"],
            counterexample={"x": 5},  # y missing
        )
        assert "y = 0" in rendered

    def test_string_input(self):
        # counterexample values are ints in the type signature; use 0 as a stand-in
        rendered = counterexample_to_test(
            func_name="greet",
            params=["name"],
            counterexample={"name": 0},  # type: ignore[dict-item]
        )
        assert "def test_greet_regression_counterexample():" in rendered

    def test_no_postcond_src(self):
        rendered = counterexample_to_test(
            func_name="inc",
            params=["x"],
            counterexample={"x": -1},
        )
        # Should still produce a valid function
        assert "def test_inc_regression_counterexample():" in rendered
        assert "x = -1" in rendered

    def test_output_is_valid_python(self):
        rendered = counterexample_to_test(
            func_name="add",
            params=["x", "y"],
            counterexample={"x": 1, "y": 2},
            postcond_src="result >= x",
        )
        # Wrap in a module to parse
        ast.parse(rendered)

    def test_docstring_present(self):
        rendered = counterexample_to_test(
            func_name="add",
            params=["x", "y"],
            counterexample={"x": 0, "y": -1},
            postcond_src="result >= x",
        )
        assert '"""' in rendered

    def test_empty_counterexample(self):
        rendered = counterexample_to_test(
            func_name="add",
            params=["x", "y"],
            counterexample={},
        )
        # Both params should default to 0
        assert "x = 0" in rendered
        assert "y = 0" in rendered


# ---------------------------------------------------------------------------
# Contract runtime (implies / is_shape / is_valid)
# ---------------------------------------------------------------------------

class TestContractRuntime:
    def test_implies_true_true(self):
        from oracle.contract_runtime import implies
        assert implies(True, True) is True

    def test_implies_true_false(self):
        from oracle.contract_runtime import implies
        assert implies(True, False) is False

    def test_implies_false_true(self):
        from oracle.contract_runtime import implies
        assert implies(False, True) is True

    def test_implies_false_false(self):
        from oracle.contract_runtime import implies
        assert implies(False, False) is True

    def test_is_valid_known_type_no_registry(self):
        from oracle.contract_runtime import is_valid
        # With no shape registry entry, is_valid is conservative (True)
        assert is_valid(42, "UnknownType") is True

    def test_is_valid_none_unknown_type(self):
        from oracle.contract_runtime import is_valid
        # Conservative: unknown type -> True even for None
        assert is_valid(None, "UnknownType") is True

    def test_is_shape_unknown_type_conservative(self):
        from oracle.contract_runtime import is_shape
        # Unknown model_type -> conservative True
        assert is_shape({"x": 1}, "UnknownModel") is True

    def test_re_match_pred_full_match(self):
        from oracle.contract_runtime import re_match_pred
        assert re_match_pred("hello123", r"[a-z]+\d+") is True

    def test_re_match_pred_no_match(self):
        from oracle.contract_runtime import re_match_pred
        assert re_match_pred("hello", r"\d+") is False

    def test_re_match_pred_partial_not_full(self):
        from oracle.contract_runtime import re_match_pred
        # fullmatch: "hello123extra" does not match "[a-z]+\d+"
        assert re_match_pred("hello123extra", r"[a-z]+\d+") is False

    def test_re_match_pred_invalid_pattern(self):
        from oracle.contract_runtime import re_match_pred
        # Invalid regex -> False (not an exception)
        assert re_match_pred("hello", r"[invalid") is False

    def test_old_snapshot_captures_values(self):
        from oracle.contract_runtime import _OldSnapshot
        snap = _OldSnapshot(x=5, balance=100)
        assert getattr(snap, "x") == 5
        assert getattr(snap, "balance") == 100

    def test_old_snapshot_is_immutable(self):
        from oracle.contract_runtime import _OldSnapshot
        snap = _OldSnapshot(x=5)
        # setattr always goes through __setattr__, which must raise AttributeError
        with pytest.raises(AttributeError):
            setattr(snap, "x", 10)

    def test_old_snapshot_repr(self):
        from oracle.contract_runtime import _OldSnapshot
        snap = _OldSnapshot(x=5)
        r = repr(snap)
        assert "_OldSnapshot" in r
        assert "x=5" in r
