"""
Loop-to-recursor mapper for user-defined predicates.

Detects common loop patterns in Python predicates and maps them
to pre-proved recursor combinators (forallb, existsb, countb, fold_left_acc).
"""

import ast
from enum import Enum
from typing import Optional


class Recursor(Enum):
    FORALLB = "forallb"     # all elements satisfy p → bool
    EXISTSb = "existsb"     # some element satisfies p → bool
    COUNTB  = "countb"      # count of elements satisfying p → nat
    FOLD_LEFT = "fold_left"  # accumulate over elements → value
    FILTERB = "filterb"     # list of elements satisfying p → list[A]
    NONE = "none"           # no pattern matched → fallback


def detect_loop_pattern(func_node: ast.FunctionDef) -> tuple[Recursor, Optional[str]]:
    """Attempt to classify a Python loop predicate into a recursor pattern.

    Returns (Recursor, predicate_lambda) or (NONE, None).
    The predicate_lambda is an AST expression for the per-element check.
    """
    non_doc = [s for s in func_node.body
               if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant))]

    if not non_doc:
        return Recursor.NONE, None

    # Pattern 1: for x in xs: if p(x): return True; return False → existsb
    # Pattern 2: for x in xs: if not p(x): return False; return True → forallb
    # Pattern 3: for x in xs: if p(x): count += 1; return count → countb
    # Pattern 4: for x in xs: acc += f(x); return acc → fold_left

    loops = [s for s in non_doc if isinstance(s, (ast.For, ast.While))]
    if not loops:
        return Recursor.NONE, None

    loop = loops[0]

    if isinstance(loop, ast.For):
        return _classify_for_loop(func_node, loop, non_doc)

    if isinstance(loop, ast.While):
        return _classify_while_loop(func_node, loop, non_doc)

    return Recursor.NONE, None


def _classify_for_loop(
    func_node: ast.FunctionDef, loop: ast.For, body: list[ast.stmt]
) -> tuple[Recursor, Optional[str]]:
    """Classify a `for x in xs:` loop."""
    # Check: iterator is a parameter name (list variable)
    if not isinstance(loop.iter, ast.Name):
        return Recursor.NONE, None
    iter_name = loop.iter.id
    loop_var = loop.target.id if isinstance(loop.target, ast.Name) else None
    if not loop_var:
        return Recursor.NONE, None

    param_names = {p.arg for p in func_node.args.args}
    if iter_name not in param_names:
        return Recursor.NONE, None

    # Check: loop body has a conditional return
    for stmt in loop.body:
        if isinstance(stmt, ast.If):
            test = stmt.test
            then_stmts = stmt.body
            if len(then_stmts) == 1 and isinstance(then_stmts[0], ast.Return):
                ret_val = then_stmts[0].value
                if isinstance(ret_val, ast.Constant) and ret_val.value is True:
                    # for x in xs: if p(x): return True; return False → existsb
                    return Recursor.EXISTSb, _extract_lambda(loop_var, test)

    # Check: loop body accumulates into a variable
    # for x in xs: acc = acc + f(x) → fold_left
    # for x in xs: if p(x): count += 1 → countb
    assigns = [s for s in loop.body if isinstance(s, (ast.Assign, ast.AugAssign))]
    if len(assigns) == 1:
        stmt = assigns[0]
        if isinstance(stmt, ast.AugAssign) and isinstance(stmt.op, ast.Add):
            var = stmt.target.id if isinstance(stmt.target, ast.Name) else None
            if var and var not in param_names:
                return Recursor.FOLD_LEFT, _extract_lambda(loop_var, stmt.value)

    return Recursor.NONE, None


def _classify_while_loop(
    func_node: ast.FunctionDef, loop: ast.While, body: list[ast.stmt]
) -> tuple[Recursor, Optional[str]]:
    return Recursor.NONE, None  # TODO


def _extract_lambda(loop_var: str, test: ast.expr) -> Optional[str]:
    """Extract a lambda string from an AST test that references the loop variable."""
    return ast.unparse(test) if test else None
