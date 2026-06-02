"""
Purity Analyzer — classifies statements as pure/impure for frame-condition inference.

Conservative: unknown calls are impure. Only verified callees with contracts
are treated as safe (their frame conditions come from their contract summary).

The IMP subset is trusted — all IMP-translatable operations are pure.
"""

import ast
from dataclasses import dataclass, field
from typing import Optional
from .shape_ir import _escape_field


KNOWN_PURE = frozenset({
    "abs", "len", "min", "max", "sum", "sorted", "all", "any",
    "isinstance", "int", "float", "bool", "str", "ord", "chr",
    "range", "round", "pow",
})


@dataclass
class PurityReport:
    function_name: str
    is_pure: bool = True
    impure_calls: list[str] = field(default_factory=list)
    impure_lines: list[int] = field(default_factory=list)
    mutated_params: set[str] = field(default_factory=set)
    mutated_fields: list[tuple[str, str]] = field(default_factory=list)
    black_hole_reason: str = ""


def analyze_purity(
    func_node: ast.FunctionDef,
    tree: ast.Module,
    contract_map: dict[str, tuple[list[str], str, str, list[str], list[str]]],
    class_fields: dict[str, list[str]],
) -> PurityReport:
    """Analyze a function for purity.

    Args:
        func_node: The function AST node
        tree: The full module AST (for cross-reference)
        contract_map: Map of function_name -> (params, pre_coq, post_coq)
        class_fields: Map of class_name -> list of field names

    Returns:
        PurityReport with classification of the function's purity.
    """
    report = PurityReport(function_name=func_node.name)

    param_names = {arg.arg for arg in func_node.args.args}
    if func_node.args.vararg:
        param_names.add(func_node.args.vararg.arg)

    for stmt in ast.walk(func_node):
        # Calls inside assert statements are contracts, not body code — skip
        if isinstance(stmt, ast.Call):
            if _is_inside_assert(stmt, func_node):
                continue
            call_name = _get_call_name(stmt)
            if call_name:
                base = call_name.split(".")[0]
                if base in KNOWN_PURE or base in ("str",):
                    continue
                func_name = call_name.split(".")[-1]
                if func_name in contract_map:
                    # Check stub's writes for frame impact
                    _, _, _, _, writes = contract_map.get(func_name, ([], "", "", [], []))
                    _propagate_writes(stmt, report, writes, param_names, tree, class_fields)
                    continue
                if call_name in contract_map:
                    _, _, _, _, writes = contract_map[call_name]
                    _propagate_writes(stmt, report, writes, param_names, tree, class_fields)
                    continue
                # Check stub loader for external contracts
                from .stub_loader import get_stub_loader
                if get_stub_loader().has_contract(func_name) or get_stub_loader().has_contract(call_name):
                    continue
                report.impure_calls.append(call_name)
                report.impure_lines.append(stmt.lineno)
                report.is_pure = False

        # Assignments to parameter fields mutate state
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Attribute):
                    base = _get_attribute_base(target)
                    if base in param_names:
                        cls = _find_class_for_param(tree, base)
                        if cls and cls in class_fields:
                            for f in class_fields[cls]:
                                if target.attr == f:
                                    report.mutated_fields.append((base, f))
                                    report.mutated_params.add(base)

        # Augmented assignments to parameter fields
        if isinstance(stmt, ast.AugAssign):
            if isinstance(stmt.target, ast.Attribute):
                base = _get_attribute_base(stmt.target)
                if base in param_names:
                    cls = _find_class_for_param(tree, base)
                    if cls and cls in class_fields:
                        for f in class_fields[cls]:
                            if stmt.target.attr == f:
                                report.mutated_fields.append((base, f))
                                report.mutated_params.add(base)

    if report.impure_calls:
        unique = list(dict.fromkeys(report.impure_calls))
        report.black_hole_reason = (
            f"Impure calls: {', '.join(unique)}. "
            f"Variables after these calls may be silently mutated. "
            f"Frame conditions cannot be verified."
        )

    return report


def generate_frame_conditions(
    func_node: ast.FunctionDef,
    tree: ast.Module,
    class_fields: dict[str, list[str]],
    postcondition_asserts: list[ast.Assert],
) -> list[str]:
    """Generate implicit frame postconditions for class fields not referenced in user asserts.

    For each parameter that is a class instance, enumerate its fields.
    Any field not mentioned in a postcondition assert AND not mutated by the function
    gets an implicit 'field unchanged' postcondition.

    Returns list of Coq postcondition expressions like:
      's "account.owner_id"%string = account_owner_id'
    """
    param_names = {arg.arg for arg in func_node.args.args}
    if func_node.args.vararg:
        param_names.add(func_node.args.vararg.arg)

    # Collect all fields mentioned in user asserts (pre, post, invariant, general)
    mentioned_fields: set[tuple[str, str]] = set()
    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Assert):
            for node in ast.walk(stmt):
                if isinstance(node, ast.Attribute):
                    base = _get_attribute_base(node)
                    if base in param_names:
                        mentioned_fields.add((base, node.attr))
                if isinstance(node, ast.Name) and node.id.endswith("_old"):
                    pass

    # Collect fields that are mutated (assigned, aug-assigned) in the function body
    mutated_fields: set[tuple[str, str]] = set()
    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Attribute):
                    base = _get_attribute_base(target)
                    if base in param_names:
                        mutated_fields.add((base, target.attr))
        if isinstance(stmt, ast.AugAssign):
            if isinstance(stmt.target, ast.Attribute):
                base = _get_attribute_base(stmt.target)
                if base in param_names:
                    mutated_fields.add((base, stmt.target.attr))

    # Generate implicit frame conditions for unmentioned, unmutated fields
    frame_conditions: list[str] = []
    for param in sorted(param_names):
        cls = _find_class_for_param(tree, param)
        if cls and cls in class_fields:
            for f in class_fields[cls]:
                if (param, f) not in mentioned_fields and (param, f) not in mutated_fields:
                    frame_conditions.append(
                        f'asZ (s "{param}_{_escape_field(f)}"%string) = {param}_{_escape_field(f)}'
                    )

    return frame_conditions


def generate_havoc_body(imp_body: str, report: PurityReport) -> str:
    """Wrap the IMP body with CHavoc for impure calls.

    If the function has impure calls, we insert CHavoc after the IMP body
    to indicate that mutable state may have been modified beyond what IMP tracks.
    """
    if not report.impure_calls and not report.mutated_params:
        return imp_body

    havoc_vars: list[str] = []
    for param in sorted(report.mutated_params):
        for f in report.mutated_fields:
            if f[0] == param:
                havoc_vars.append(f'"{param}.{f[1]}"%string')

    if not havoc_vars and report.impure_calls:
        return imp_body

    havocs = " ".join(havoc_vars)
    return f"(CSeq {imp_body} (CHavoc [{havocs}]))"


def _is_inside_assert(node: ast.AST, root: ast.FunctionDef) -> bool:
    """Check whether an AST node is inside an assert statement (contract)."""
    for parent in ast.walk(root):
        if isinstance(parent, ast.Assert) and node in ast.walk(parent):
            # Only return True if the assert is the closest ancestor
            for inner in ast.walk(parent):
                if inner is node:
                    return True
    return False


def _get_call_name(node: ast.Call) -> str | None:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        parts = []
        c = func
        while isinstance(c, ast.Attribute):
            parts.append(c.attr)
            c = c.value
        if isinstance(c, ast.Name):
            parts.append(c.id)
        return ".".join(reversed(parts))
    return None


def _get_attribute_base(node: ast.Attribute) -> str | None:
    """Extract the base variable name from an attribute chain like a.b.c → 'a'."""
    if isinstance(node.value, ast.Name):
        return node.value.id
    if isinstance(node.value, ast.Attribute):
        return _get_attribute_base(node.value)
    return None


def _find_class_for_param(tree: ast.Module, param: str) -> str | None:
    """Find which class a parameter belongs to.

    Uses same convention as _expand_params:
    `account: Account` → param 'account' matches class 'Account' by lowered name.
    """
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            if node.name.lower() == param.lower():
                return node.name
    return None


def _caller_arg_names(call_node: ast.Call) -> list[str]:
    """Extract argument variable names from a call like `db_save(conn, 42)`."""
    names = []
    for arg in call_node.args:
        if isinstance(arg, ast.Name):
            names.append(arg.id)
        elif isinstance(arg, ast.Attribute):
            names.append(_get_attribute_base(arg) or "")
    return names


def _propagate_writes(
    call_node: ast.Call,
    report: PurityReport,
    writes: list[str],
    param_names: set[str],
    tree: ast.Module,
    class_fields: dict[str, list[str]],
) -> None:
    """Propagate callee's writes into the caller's mutation tracking.

    write_target names in the stub correspond to callee parameter names.
    We match them to the caller's argument variables at the call site.
    If a caller passes `conn` and the stub writes `conn`, all mutable
    fields of `conn` are marked as potentially mutated.
    """
    arg_names = _caller_arg_names(call_node)
    for write_target in writes:
        for i, arg_name in enumerate(arg_names):
            if write_target == arg_name and arg_name in param_names:
                cls = _find_class_for_param(tree, arg_name)
                if cls is None:
                    cls = _find_class_by_annotation(tree, arg_name)
                if cls and cls in class_fields:
                    for f in class_fields[cls]:
                        report.mutated_fields.append((arg_name, f))
                    report.mutated_params.add(arg_name)


def _find_class_by_annotation(tree: ast.Module, param: str) -> str | None:
    """Find a class by checking the type annotation of a parameter.
    `conn: Connection` → returns 'Connection'."""
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            for arg in node.args.args:
                if arg.arg == param and arg.annotation:
                    if isinstance(arg.annotation, ast.Name):
                        return arg.annotation.id
    return None
