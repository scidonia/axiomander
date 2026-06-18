"""
property_test_gen.py -- Hypothesis property-test generator from assert contracts.

Level A of the executable-tests feature.  Reads a Python source file,
extracts assert-based contracts (preconditions / postconditions) via the
existing ContractLinter, derives Hypothesis strategies from the IR, and
emits a runnable ``test_<module>_contracts.py`` module.

Public API
----------
generate_tests(source, func_name=None) -> str
    Return a string containing a complete pytest + Hypothesis test module.

extract_function_contracts(source, func_name) -> FunctionContracts
    Return the parsed pre/post IR for a single function.

counterexample_to_test(func_name, params, counterexample, postcond_src) -> str
    Emit a concrete regression test from an SMT counterexample dict.

CLI
---
Called via ``axiomander gen-tests <file> [--function F] [--output O]``.
"""

from __future__ import annotations

import ast
import inspect
import textwrap
from dataclasses import dataclass, field
from typing import Optional

from .contract_ir import (
    Expr, BinOp, Logical, IntLit, Var, LenExpr, ImpliesExpr,
    RaisesExpr, IsShape, IsValid, ReMatchExpr,
)
from .contract_linter import ContractLinter


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class ParamStrategy:
    """Hypothesis strategy for a single function parameter."""
    name: str
    py_type: str = "int"          # "int", "str", "float", "list", "bool", "Any"
    min_value: Optional[int] = None
    max_value: Optional[int] = None
    min_size: Optional[int] = None   # for lists/strings
    max_size: Optional[int] = None
    # If this param is derived from another (e.g. n == len(xs)), record the source.
    derived_from: Optional[str] = None
    derived_expr: Optional[str] = None  # Python expression, e.g. "len(xs)"

    def to_hypothesis(self) -> str:
        """Render as a Hypothesis strategy expression string."""
        if self.derived_from is not None:
            # Derived params are not passed to @given; they are computed in the body.
            return ""
        if self.py_type == "int":
            kwargs = []
            if self.min_value is not None:
                kwargs.append(f"min_value={self.min_value}")
            if self.max_value is not None:
                kwargs.append(f"max_value={self.max_value}")
            return "st.integers(" + ", ".join(kwargs) + ")"
        if self.py_type == "float":
            kwargs = ["allow_nan=False", "allow_infinity=False"]
            if self.min_value is not None:
                kwargs.append(f"min_value={self.min_value}")
            if self.max_value is not None:
                kwargs.append(f"max_value={self.max_value}")
            return "st.floats(" + ", ".join(kwargs) + ")"
        if self.py_type == "str":
            kwargs = []
            if self.min_size is not None:
                kwargs.append(f"min_size={self.min_size}")
            if self.max_size is not None:
                kwargs.append(f"max_size={self.max_size}")
            return "st.text(" + ", ".join(kwargs) + ")"
        if self.py_type == "bool":
            return "st.booleans()"
        if self.py_type == "list":
            inner = "st.integers()"
            kwargs = []
            if self.min_size is not None:
                kwargs.append(f"min_size={self.min_size}")
            if self.max_size is not None:
                kwargs.append(f"max_size={self.max_size}")
            return "st.lists(" + inner + (", " + ", ".join(kwargs) if kwargs else "") + ")"
        # Fallback
        return "st.integers()"


@dataclass
class FunctionContracts:
    """Parsed contracts for a single function."""
    func_name: str
    params: list[str] = field(default_factory=list)
    param_types: dict[str, str] = field(default_factory=dict)
    preconditions: list[Expr] = field(default_factory=list)
    postconditions: list[Expr] = field(default_factory=list)
    exception_postconditions: list[RaisesExpr] = field(default_factory=list)
    old_bindings: dict[str, str] = field(default_factory=dict)
    # Raw assert source text for each postcondition (for comments in output)
    postcond_sources: list[str] = field(default_factory=list)
    precond_sources: list[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Contract extraction
# ---------------------------------------------------------------------------

def _type_from_annotation(ann: Optional[ast.expr]) -> str:
    """Map a Python type annotation AST node to a strategy type string."""
    if ann is None:
        return "int"
    if isinstance(ann, ast.Name):
        name = ann.id
        if name in ("int",):
            return "int"
        if name in ("float",):
            return "float"
        if name in ("str",):
            return "str"
        if name in ("bool",):
            return "bool"
        if name in ("list", "List"):
            return "list"
        # Named class -- treat as int (field-based objects generated separately)
        return "int"
    if isinstance(ann, ast.Subscript):
        # list[int], List[int], etc.
        if isinstance(ann.value, ast.Name) and ann.value.id in ("list", "List"):
            return "list"
    return "int"


def _is_old_call(node: ast.AST) -> bool:
    """Return True if node is old(x)."""
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)  # type: ignore[union-attr]
        and node.func.id == "old"            # type: ignore[union-attr]
        and len(node.args) == 1              # type: ignore[union-attr]
    )


def _collect_old_bindings(assert_nodes: list[ast.Assert]) -> dict[str, str]:
    """Walk postcondition asserts and collect old(x) -> x mappings."""
    bindings: dict[str, str] = {}
    for node in assert_nodes:
        for subnode in ast.walk(node):
            if _is_old_call(subnode):
                call = subnode  # type: ignore[assignment]
                arg = call.args[0]  # type: ignore[attr-defined]
                if isinstance(arg, ast.Name):
                    bindings[f"old_{arg.id}"] = arg.id
                elif isinstance(arg, ast.Attribute):
                    key = f"old_{arg.attr}"
                    bindings[key] = f"{ast.unparse(arg)}"
    return bindings


def _classify_assert_simple(func_node: ast.FunctionDef, stmt: ast.Assert) -> str:
    """Lightweight classification: precondition / postcondition / general."""
    body = func_node.body
    # Postcondition: assert immediately before return (or chain of asserts before return)
    for i, s in enumerate(body):
        if s is stmt:
            j = i + 1
            while j < len(body) and isinstance(body[j], ast.Assert):
                j += 1
            if j < len(body) and isinstance(body[j], ast.Return):
                return "postcondition"
    # Precondition: at function start, before any non-assert code
    seen_code = False
    if stmt in body:
        idx = body.index(stmt)
        for s in body[:idx + 1]:
            is_doc = (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                      and isinstance(s.value.value, str))
            if not isinstance(s, ast.Assert) and not is_doc:
                if s is not stmt:
                    seen_code = True
        if not seen_code:
            return "precondition"
    return "general"


def extract_function_contracts(source: str, func_name: str) -> FunctionContracts:
    """Parse a Python source string and extract contracts for func_name.

    Returns a FunctionContracts with pre/post IR nodes and old() bindings.
    """
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return FunctionContracts(func_name=func_name)

    func_node: Optional[ast.FunctionDef] = None
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name == func_name:
                func_node = node  # type: ignore[assignment]
                break

    if func_node is None:
        return FunctionContracts(func_name=func_name)

    # Collect parameter names and types
    params: list[str] = []
    param_types: dict[str, str] = {}
    for arg in func_node.args.args:
        params.append(arg.arg)
        param_types[arg.arg] = _type_from_annotation(arg.annotation)

    # Collect assert nodes classified as pre/post
    pre_asserts: list[ast.Assert] = []
    post_asserts: list[ast.Assert] = []
    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Assert):
            cls = _classify_assert_simple(func_node, stmt)
            if cls == "precondition":
                pre_asserts.append(stmt)
            elif cls == "postcondition":
                post_asserts.append(stmt)

    # Collect old() bindings from postconditions
    old_bindings = _collect_old_bindings(post_asserts)

    # Lint each assert to get IR
    # ContractLinter(params, context) -- params=None means accept all variable names
    linter_pre = ContractLinter(None, "precondition")
    linter_post = ContractLinter(None, "postcondition")

    preconditions: list[Expr] = []
    precond_sources: list[str] = []
    for stmt in pre_asserts:
        result = linter_pre.lint_expression(stmt.test)
        if result.ir is not None:
            preconditions.append(result.ir)
            precond_sources.append(ast.unparse(stmt.test))

    postconditions: list[Expr] = []
    postcond_sources: list[str] = []
    exception_postconditions: list[RaisesExpr] = []
    for stmt in post_asserts:
        result = linter_post.lint_expression(stmt.test)
        if result.ir is not None:
            if isinstance(result.ir, RaisesExpr):
                exception_postconditions.append(result.ir)
            else:
                postconditions.append(result.ir)
                postcond_sources.append(ast.unparse(stmt.test))

    return FunctionContracts(
        func_name=func_name,
        params=params,
        param_types=param_types,
        preconditions=preconditions,
        postconditions=postconditions,
        exception_postconditions=exception_postconditions,
        old_bindings=old_bindings,
        postcond_sources=postcond_sources,
        precond_sources=precond_sources,
    )


# ---------------------------------------------------------------------------
# Strategy narrowing
# ---------------------------------------------------------------------------

def _narrow_strategies(
    params: list[str],
    param_types: dict[str, str],
    preconditions: list[Expr],
) -> dict[str, ParamStrategy]:
    """Build per-param strategies, narrowed by precondition IR.

    Handles:
    - ``a >= N``  -> min_value=N
    - ``a <= N``  -> max_value=N
    - ``a > N``   -> min_value=N+1
    - ``a < N``   -> max_value=N-1
    - ``0 <= a <= 100`` (chained via Logical.and)
    - ``n == len(xs)`` -> n is derived from xs
    """
    strategies: dict[str, ParamStrategy] = {}
    for p in params:
        strategies[p] = ParamStrategy(name=p, py_type=param_types.get(p, "int"))

    def _apply_binop(ir: BinOp) -> None:
        """Apply a single BinOp constraint to the strategy map."""
        op = ir.op
        left = ir.left
        right = ir.right

        # Pattern: param op literal  (e.g. a >= 0)
        if isinstance(left, Var) and isinstance(right, IntLit):
            name = left.name
            val = right.value
            if name not in strategies:
                return
            s = strategies[name]
            if op in (">=", "="):
                s.min_value = max(s.min_value, val) if s.min_value is not None else val
            if op in ("<=", "="):
                s.max_value = min(s.max_value, val) if s.max_value is not None else val
            if op == ">":
                nv = val + 1
                s.min_value = max(s.min_value, nv) if s.min_value is not None else nv
            if op == "<":
                nv = val - 1
                s.max_value = min(s.max_value, nv) if s.max_value is not None else nv

        # Pattern: literal op param  (e.g. 0 <= a)
        elif isinstance(left, IntLit) and isinstance(right, Var):
            name = right.name
            val = left.value
            if name not in strategies:
                return
            s = strategies[name]
            # 0 <= a  means a >= 0
            if op in ("<=", "="):
                s.min_value = max(s.min_value, val) if s.min_value is not None else val
            if op in (">=", "="):
                s.max_value = min(s.max_value, val) if s.max_value is not None else val
            if op == "<":
                nv = val + 1
                s.min_value = max(s.min_value, nv) if s.min_value is not None else nv
            if op == ">":
                nv = val - 1
                s.max_value = min(s.max_value, nv) if s.max_value is not None else nv

        # Pattern: n == len(xs)  -> n is derived
        elif (op == "=" and isinstance(left, Var) and isinstance(right, LenExpr)):
            n_name = left.name
            xs_name = right.name
            if n_name in strategies and xs_name in strategies:
                strategies[n_name].derived_from = xs_name
                strategies[n_name].derived_expr = f"len({xs_name})"

        elif (op == "=" and isinstance(right, Var) and isinstance(left, LenExpr)):
            n_name = right.name
            xs_name = left.name
            if n_name in strategies and xs_name in strategies:
                strategies[n_name].derived_from = xs_name
                strategies[n_name].derived_expr = f"len({xs_name})"

    def _walk_ir(ir: Expr) -> None:
        if isinstance(ir, BinOp):
            _apply_binop(ir)
        elif isinstance(ir, Logical) and ir.op == "and":
            for operand in ir.operands:
                _walk_ir(operand)
        elif isinstance(ir, ImpliesExpr):
            # Don't narrow from the consequent of an implication
            _walk_ir(ir.left)

    for pre in preconditions:
        _walk_ir(pre)

    return strategies


# ---------------------------------------------------------------------------
# Code generation
# ---------------------------------------------------------------------------

def _render_assume_checks(
    preconditions: list[Expr],
    strategies: dict[str, ParamStrategy],
) -> list[str]:
    """Emit ``assume(...)`` lines for preconditions that couldn't be narrowed.

    A precondition is "covered" if it only constrains a single param's
    min/max and was already absorbed into the strategy.  Everything else
    becomes an ``assume()``.
    """
    lines: list[str] = []
    for pre in preconditions:
        try:
            py = pre.to_python()
        except NotImplementedError:
            continue
        # Heuristic: if the expression is a simple BinOp on a param vs literal,
        # it was already absorbed into the strategy -- skip it.
        if isinstance(pre, BinOp):
            left, right = pre.left, pre.right
            if (isinstance(left, Var) and isinstance(right, IntLit)
                    and left.name in strategies
                    and strategies[left.name].derived_from is None):
                continue
            if (isinstance(right, Var) and isinstance(left, IntLit)
                    and right.name in strategies
                    and strategies[right.name].derived_from is None):
                continue
        lines.append(f"    assume({py})")
    return lines


def _render_postcond_asserts(
    postconditions: list[Expr],
    postcond_sources: list[str],
) -> list[str]:
    """Emit ``assert ...`` lines for each postcondition."""
    lines: list[str] = []
    for i, post in enumerate(postconditions):
        src = postcond_sources[i] if i < len(postcond_sources) else ""
        try:
            py = post.to_python()
            comment = f"  # {src}" if src else ""
            lines.append(f"    assert {py}{comment}")
        except NotImplementedError as exc:
            lines.append(f"    # axiomander: skipped -- {exc}")
    return lines


def _render_raises_blocks(
    exception_postconditions: list[RaisesExpr],
) -> list[str]:
    """Emit ``with pytest.raises(ExcType): ...`` blocks."""
    lines: list[str] = []
    for raises in exception_postconditions:
        lines.append(f"    with pytest.raises({raises.exc_type}):")
        try:
            cond_py = raises.cond.to_python()
            lines.append(f"        assert {cond_py}")
        except NotImplementedError:
            lines.append("        pass  # axiomander: condition not executable")
    return lines


def _render_test_function(
    contracts: FunctionContracts,
    module_import: str,
) -> str:
    """Render a single @given test function for contracts.func_name."""
    strategies = _narrow_strategies(
        contracts.params,
        contracts.param_types,
        contracts.preconditions,
    )

    # Separate free params (passed to @given) from derived params
    free_params = [p for p in contracts.params if strategies[p].derived_from is None]
    derived_params = [p for p in contracts.params if strategies[p].derived_from is not None]

    # Build @given decorator
    given_args = ", ".join(
        f"{p}={strategies[p].to_hypothesis()}"
        for p in free_params
        if strategies[p].to_hypothesis()
    )
    decorator = f"@given({given_args})"

    # Build function signature (free params only -- derived are computed inside)
    sig_params = ", ".join(free_params)
    func_sig = f"def test_{contracts.func_name}_contracts({sig_params}):"

    body_lines: list[str] = []

    # Derived param bindings
    for p in derived_params:
        s = strategies[p]
        body_lines.append(f"    {p} = {s.derived_expr}")

    # old() snapshot
    if contracts.old_bindings:
        snap_kwargs = ", ".join(
            f"{snap_name}={orig_expr}"
            for snap_name, orig_expr in contracts.old_bindings.items()
        )
        body_lines.append(f"    _snap = _OldSnapshot({snap_kwargs})")

    # assume() checks for non-narrowable preconditions
    assume_lines = _render_assume_checks(contracts.preconditions, strategies)
    body_lines.extend(assume_lines)

    # Call the function under test
    call_args = ", ".join(contracts.params)
    body_lines.append(f"    result = {contracts.func_name}({call_args})")

    # Postcondition asserts
    post_lines = _render_postcond_asserts(
        contracts.postconditions, contracts.postcond_sources
    )
    body_lines.extend(post_lines)

    # Exception postconditions
    raises_lines = _render_raises_blocks(contracts.exception_postconditions)
    body_lines.extend(raises_lines)

    if not body_lines:
        body_lines.append("    pass  # no executable postconditions")

    lines = [decorator, func_sig] + body_lines
    return "\n".join(lines)


def generate_tests(
    source: str,
    func_name: Optional[str] = None,
    module_path: str = "",
) -> str:
    """Generate a complete Hypothesis test module from source contracts.

    Parameters
    ----------
    source:
        Python source code containing functions with assert contracts.
    func_name:
        If given, generate tests only for this function.
        If None, generate tests for all functions that have contracts.
    module_path:
        Path to the source file (used for the import comment).

    Returns
    -------
    str
        A complete, importable pytest + Hypothesis test module as a string.
    """
    try:
        tree = ast.parse(source)
    except SyntaxError as exc:
        return f"# axiomander: could not parse source -- {exc}\n"

    # Collect function names to process
    func_names: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if func_name is None or node.name == func_name:
                func_names.append(node.name)

    if not func_names:
        return f"# axiomander: no functions found\n"

    # Determine module import path
    if module_path:
        import os
        base = os.path.splitext(os.path.basename(module_path))[0]
        import_line = f"from {base} import {', '.join(func_names)}"
    else:
        import_line = f"# from <module> import {', '.join(func_names)}"

    # Build header
    header_lines = [
        '"""',
        "Auto-generated property tests from assert contracts.",
        f"Source: {module_path or '<unknown>'}",
        "",
        "Generated by: axiomander gen-tests",
        "Do not edit -- regenerate with: axiomander gen-tests <file>",
        '"""',
        "",
        "import pytest",
        "from hypothesis import given, assume, settings",
        "from hypothesis import strategies as st",
        "",
        "from oracle.contract_runtime import implies, is_shape, is_valid, re_match_pred, _OldSnapshot",
        import_line,
        "",
        "",
    ]

    # Generate one test function per source function
    test_blocks: list[str] = []
    for fn in func_names:
        contracts = extract_function_contracts(source, fn)
        if not contracts.postconditions and not contracts.exception_postconditions:
            # No postconditions -- emit a placeholder
            test_blocks.append(
                f"# {fn}: no postconditions found -- skipping test generation\n"
            )
            continue
        block = _render_test_function(contracts, import_line)
        test_blocks.append(block + "\n")

    return "\n".join(header_lines) + "\n\n".join(test_blocks)


# ---------------------------------------------------------------------------
# Level C: counterexample -> regression test
# ---------------------------------------------------------------------------

def counterexample_to_test(
    func_name: str,
    params: list[str],
    counterexample: dict[str, int],
    postcond_src: str = "",
) -> str:
    """Emit a concrete regression test from an SMT counterexample dict.

    Parameters
    ----------
    func_name:
        Name of the function that failed verification.
    params:
        Ordered list of parameter names.
    counterexample:
        Dict mapping variable names to integer values (from SMT model).
    postcond_src:
        Optional: the postcondition source text that was violated.

    Returns
    -------
    str
        A ``def test_<func>_regression_counterexample():`` function body.
    """
    lines = [
        f"def test_{func_name}_regression_counterexample():",
        f'    """Regression test: SMT counterexample found by axiomander.',
    ]
    if postcond_src:
        lines.append(f"    Violated postcondition: {postcond_src}")
    lines.append('    """')

    # Emit concrete input bindings
    for p in params:
        if p in counterexample:
            lines.append(f"    {p} = {counterexample[p]}")
        else:
            lines.append(f"    {p} = 0  # not in counterexample model")

    call_args = ", ".join(params)
    lines.append(f"    # This call should expose the contract violation:")
    lines.append(f"    result = {func_name}({call_args})")
    if postcond_src:
        lines.append(f"    # Postcondition that was violated: {postcond_src}")
        lines.append(f"    # TODO: assert the correct behaviour here")
    lines.append("")
    return "\n".join(lines)
