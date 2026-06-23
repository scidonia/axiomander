"""Recursive predicate classification (WP-9).

Detects self-recursive `def` predicates in Python AST and classifies them
as structural (D1), measured (D2), or rejected — the totality gate for
recursive predicates described in fluid-lowerer-design.md section 9.3.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass
from enum import Enum


class RecKind(Enum):
    """Classification of a recursive predicate's decreasing argument."""
    NONREC = "nonrec"
    STRUCTURAL = "structural"
    MEASURED = "measured"
    REJECT = "reject"


@dataclass(frozen=True)
class PredicateDef:
    """A detected recursive predicate definition.

    name:      the predicate function name.
    params:    parameter names.
    body_expr: the original return-expression AST (for lowering).
    rec_kind:  how the recursion decreases.
    rec_arg:   the decreasing parameter name (STRUCTURAL) or measure text (MEASURED).
    reason:    diagnostic message when rec_kind is REJECT.
    """
    name: str
    params: list[str]
    body_expr: ast.expr | None
    rec_kind: RecKind
    rec_arg: str = ""
    reason: str = ""

    def is_recursive(self) -> bool:
        return self.rec_kind is not RecKind.NONREC


def classify_recursion(
    func_node: ast.FunctionDef,
    predicate_name: str | None = None,
) -> PredicateDef:
    """Classify a predicate function as recursive or not.

    Walks the body looking for self-calls (calls where the callee name
    matches *predicate_name* or the function's own name).  For each
    self-call, examines the arguments to determine the decreasing pattern.

    Returns:
        PredicateDef with rec_kind = NONREC     if no self-calls found.
        PredicateDef with rec_kind = STRUCTURAL  if all self-calls are
            structural reductions (e.g. `f(xs[1:])`) on the same param.
        PredicateDef with rec_kind = REJECT     if recursion is detected
            but no structural pattern or measure is found.
    """
    name = predicate_name or func_node.name
    params = [a.arg for a in func_node.args.args]
    calls = _find_self_calls(func_node, name)

    if not calls:
        return PredicateDef(
            name=name, params=params, body_expr=None,
            rec_kind=RecKind.NONREC,
        )

    # Extract the body expression (return value) for lowering.
    body_expr = _extract_return_expr(func_node)

    # Check for `# decreases:` annotation in the body.
    measure = _find_decreases_annotation(func_node)
    if measure:
        return PredicateDef(
            name=name, params=params, body_expr=body_expr,
            rec_kind=RecKind.MEASURED, rec_arg=measure,
        )

    # Try structural classification.
    rec_arg = _classify_structural(calls, params)
    if rec_arg is not None:
        return PredicateDef(
            name=name, params=params, body_expr=body_expr,
            rec_kind=RecKind.STRUCTURAL, rec_arg=rec_arg,
        )

    # Could not classify — reject.
    call_sites = [ast.unparse(c) for c in calls]
    return PredicateDef(
        name=name, params=params, body_expr=body_expr,
        rec_kind=RecKind.REJECT,
        reason=(
            f"'{name}' is recursive but the self-call(s) "
            f"{', '.join(call_sites)} do not structurally decrease "
            f"a parameter.  Add '# decreases: <expr>' to declare a measure."
        ),
    )


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _find_self_calls(
    node: ast.AST,
    name: str,
) -> list[ast.Call]:
    """Find all self-call sites (ast.Call nodes whose callee name is *name*)."""
    calls: list[ast.Call] = []

    class Visitor(ast.NodeVisitor):
        def visit_Call(self, node: ast.Call) -> None:
            if isinstance(node.func, ast.Name) and node.func.id == name:
                calls.append(node)
            self.generic_visit(node)

    Visitor().visit(node)
    return calls


def _extract_return_expr(func_node: ast.FunctionDef) -> ast.expr | None:
    """Extract the return expression from a single-expression body.

    For `def f(xs): return ...`, returns the expression.
    For a multi-statement body that ends with `return`, returns the
    last return value.  For a body that's just an expression (e.g.
    in the case of `def f(xs): expr` — though Python requires `return`),
    returns None.
    """
    for stmt in reversed(func_node.body):
        if isinstance(stmt, ast.Return) and stmt.value is not None:
            return stmt.value
    return None


def _find_decreases_annotation(func_node: ast.FunctionDef) -> str | None:
    """Look for `# decreases: <expr>` on the first line of the body."""
    for stmt in func_node.body:
        if (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)
                and isinstance(stmt.value.value, str)):
            comment = stmt.value.value.strip()
            if comment.startswith("decreases:"):
                return comment[len("decreases:"):].strip()
        break  # only check first statement
    return None


def _classify_structural(
    calls: list[ast.Call],
    params: list[str],
) -> str | None:
    """Check if all self-calls structurally decrease a single parameter.

    Returns the parameter name if found, or None.

    Structural decrease patterns recognized:
      - xs[1:]   (tail slice on a param)
    """
    if not calls:
        return None

    rec_arg: str | None = None

    for call in calls:
        if not call.args:
            return None
        arg_node = call.args[0]
        arg_name, structural = _is_structural_arg(arg_node, params)
        if not structural:
            return None
        if rec_arg is None:
            rec_arg = arg_name
        elif rec_arg != arg_name:
            return None  # different params in different self-calls

    return rec_arg


def _is_structural_arg(
    node: ast.expr,
    params: list[str],
) -> tuple[str | None, bool]:
    """Check if *node* is a structural reduction of a parameter.

    Returns (param_name, True) if it matches, or (None, False).

    Recognised patterns:
      - xs[1:]  →  tail slice  (match xs with [] | x :: rest)
    """
    # xs[1:] -> Subscript(value=Name('xs'), slice=Slice(lower=1, upper=None))
    if isinstance(node, ast.Subscript):
        if isinstance(node.value, ast.Name):
            param = node.value.id
            if param in params:
                sl = node.slice
                if isinstance(sl, ast.Slice):
                    lo = sl.lower
                    hi = sl.upper
                    # Tail: xs[1:]
                    if (isinstance(lo, ast.Constant) and lo.value == 1
                            and hi is None):
                        return param, True
                    # Tail with lower bound: xs[n:] (n is variable)
                    if (lo is not None and hi is None):
                        return param, True
    return None, False