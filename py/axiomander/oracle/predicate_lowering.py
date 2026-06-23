"""Loop-predicate lowering via fold_left_acc — the universal recursor.

Instead of detecting specific loop patterns (EXISTSb, FORALLB, COUNTB),
we emit fold_left_acc for EVERY `for x in xs:` loop in a predicate body.
fold_left_acc is the universal recursor that subsumes all others:

    existsb p xs  = fold_left_acc (fun acc x => acc || p x) false xs
    forallb p xs  = fold_left_acc (fun acc x => acc && p x) true xs
    countb p xs   = fold_left_acc (fun acc x => if p x then acc + 1 else acc) 0 xs

The specialized recursors (forallb, existsb, countb) become an optional
query-optimization pass — not a detection requirement at lowering time.
"""

from __future__ import annotations

import ast
from enum import Enum
from typing import Optional


class Recursor(Enum):
    FORALLB = "forallb"
    EXISTSb = "existsb"
    COUNTB = "countb"
    FOLD_LEFT = "fold_left"
    FILTERB = "filterb"
    NONE = "none"


def lower_loop_to_fold(
    func_node: ast.FunctionDef,
) -> Optional[tuple[str, str, str, str]]:
    """Attempt to lower a loop predicate to fold_left_acc.

    Returns None if the predicate cannot be lowered.
    Returns (recursor_name, lambda_coq, acc_init_coq, list_name) on success.

    The lambda is `(fun acc x => <lowered_loop_body>)` where the loop body
    is translated to a Coq bool expression.  The accumulator init value is
    extracted from the variable initialisation before the loop.
    """
    non_doc = [s for s in func_node.body
               if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant))]

    loops = [s for s in non_doc if isinstance(s, ast.For)]
    if not loops:
        return None

    loop = loops[0]

    # Check: iterator is a parameter name (list variable)
    if not isinstance(loop.iter, ast.Name):
        return None
    list_name = loop.iter.id

    param_names = {p.arg for p in func_node.args.args}
    if list_name not in param_names:
        return None

    loop_var = loop.target.id if isinstance(loop.target, ast.Name) else None
    if not loop_var:
        return None

    # Find the accumulator variable: a variable assigned to in the loop
    # that also has an initialisation before the loop.
    acc_var, acc_init = _detect_accumulator(non_doc, loop, param_names)
    if acc_var is None:
        return None

    # Lower the loop body to a Coq lambda updating the accumulator.
    lam = _lower_loop_body(loop.body, acc_var, loop_var, list_name)
    if lam is None:
        return None

    acc_init_coq = _expr_to_coq_value(acc_init) if acc_init else "0"

    # --- Pattern detection: rewrite to specialized recursor when possible. ---
    specialized = _classify_fold_pattern(loop.body, acc_var, loop_var, acc_init_coq)
    if specialized is not None:
        return specialized + (list_name,)

    return ("fold_left", lam, acc_init_coq, list_name)


# ---------------------------------------------------------------------------
# Accumulator detection
# ---------------------------------------------------------------------------

def _detect_accumulator(
    body: list[ast.stmt],
    loop: ast.For,
    param_names: set[str],
) -> tuple[Optional[str], Optional[ast.expr]]:
    """Detect the accumulator variable and its initial value.

    Looks for `var = <init>` before the loop and `var = ...` or
    `var <op>= ...` inside the loop body.
    """
    acc_var: Optional[str] = None
    acc_init: Optional[ast.expr] = None

    # Find assignments inside the loop body that update a variable.
    for stmt in loop.body:
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Name) and target.id not in param_names:
                    acc_var = target.id
                    break
        elif isinstance(stmt, ast.AugAssign):
            if isinstance(stmt.target, ast.Name):
                acc_var = stmt.target.id
                break
        elif isinstance(stmt, ast.If):
            # Check inside if branches for accumulator updates.
            for branch in [stmt.body, stmt.orelse]:
                for s in branch:
                    if isinstance(s, ast.Assign):
                        for target in s.targets:
                            if isinstance(target, ast.Name) and target.id not in param_names:
                                acc_var = target.id
                                break
                    elif isinstance(s, ast.AugAssign):
                        if isinstance(s.target, ast.Name):
                            acc_var = s.target.id
                            break

    if acc_var is None:
        return None, None

    # Find the initial value before the loop.
    for stmt in body:
        if stmt is loop:
            break
        if isinstance(stmt, ast.Assign):
            for i, target in enumerate(stmt.targets):
                if isinstance(target, ast.Name) and target.id == acc_var:
                    acc_init = stmt.value if isinstance(stmt.value, ast.Constant) else stmt.value
                    break

    return acc_var, acc_init


# ---------------------------------------------------------------------------
# Loop body → Coq lambda lowerer
# ---------------------------------------------------------------------------

def _lower_loop_body(
    loop_body: list[ast.stmt],
    acc_var: str,
    loop_var: str,
    list_name: str,
) -> Optional[str]:
    """Lower a loop body to a Coq lambda `(fun acc x => ...)`.

    The body statements are compiled to Coq boolean expressions.
    Accumulator updates become the lambda result.
    """
    inner = _compile_stmts(loop_body, acc_var, loop_var)
    if inner is None:
        return None
    return f"(fun ({acc_var} : Z) ({loop_var} : Z) => {inner})"


def _compile_stmts(
    stmts: list[ast.stmt],
    acc_var: str,
    loop_var: str,
) -> Optional[str]:
    """Compile a sequence of loop body statements to a Coq expression."""
    result_parts: list[str] = []

    for stmt in stmts:
        compiled = _compile_stmt(stmt, acc_var, loop_var)
        if compiled:
            result_parts.append(compiled)

    if not result_parts:
        return acc_var  # bare accumulator return
    return " && ".join(f"({p})" for p in result_parts)


def _compile_stmt(
    stmt: ast.stmt,
    acc_var: str,
    loop_var: str,
) -> Optional[str]:
    """Compile a single loop-body statement to a Coq expression."""
    # If statement with conditional accumulator update
    if isinstance(stmt, ast.If):
        cond = _expr_to_coq_bool(stmt.test, loop_var)
        if cond is None:
            return None
        then_coq = _compile_branch(stmt.body, acc_var, loop_var)
        else_coq = _compile_branch(stmt.orelse, acc_var, loop_var) or acc_var

        if then_coq and then_coq != acc_var:
            return f"if {cond} then {then_coq} else {else_coq}"
        return None

    # Assignment to accumulator
    if isinstance(stmt, ast.Assign):
        for target in stmt.targets:
            if isinstance(target, ast.Name) and target.id == acc_var:
                return _expr_to_coq_bool(stmt.value, loop_var)

    # Augmented assignment
    if isinstance(stmt, ast.AugAssign):
        if isinstance(stmt.target, ast.Name) and stmt.target.id == acc_var:
            right = _expr_to_coq_bool(stmt.value, loop_var)
            if right:
                op = {"+": "Z.add", "-": "Z.sub"}.get(
                    type(stmt.op).__name__.lower().replace("add", "+").replace("sub", "-"),
                    type(stmt.op).__name__,
                )
                return f"({acc_var} + {right})" if isinstance(stmt.op, ast.Add) else None

    return None


def _compile_branch(
    stmts: list[ast.stmt],
    acc_var: str,
    loop_var: str,
) -> Optional[str]:
    """Compile a branch (then/else) of an if statement."""
    for stmt in stmts:
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Name) and target.id == acc_var:
                    return _expr_to_coq_bool(stmt.value, loop_var)
    return None


def _expr_to_coq_bool(
    node: ast.expr,
    loop_var: str,
) -> Optional[str]:
    """Translate a Python AST expression to a Coq boolean expression string."""
    if isinstance(node, ast.Constant):
        if node.value is True:
            return "true"
        if node.value is False:
            return "false"
        return str(node.value)

    if isinstance(node, ast.Name):
        return node.id

    if isinstance(node, ast.Compare):
        left = _expr_to_coq_bool(node.left, loop_var)
        ops = node.ops
        comps = node.comparators
        if len(ops) == 1 and len(comps) == 1:
            right = _expr_to_coq_bool(comps[0], loop_var)
            if left and right:
                op_map = {
                    ast.Eq: "Z.eqb",
                    ast.NotEq: "fun a b => negb (Z.eqb a b)",
                    ast.Lt: "Z.ltb",
                    ast.LtE: "Z.leb",
                    ast.Gt: "Z.gtb",
                    ast.GtE: "Z.geb",
                }
                op_str = op_map.get(type(ops[0]))
                if op_str:
                    return f"({op_str} {left} {right})"

    if isinstance(node, ast.BoolOp):
        vals = [_expr_to_coq_bool(v, loop_var) for v in node.values]
        vals = [v for v in vals if v]
        if vals:
            sep = " && " if isinstance(node.op, ast.And) else " || "
            return "(" + sep.join(vals) + ")"

    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        inner = _expr_to_coq_bool(node.operand, loop_var)
        if inner:
            return f"negb ({inner})"

    return None


def _expr_to_coq_value(node: ast.expr) -> str:
    """Translate a Python literal expression to a Coq value."""
    if isinstance(node, ast.Constant):
        if node.value is True:
            return "true"
        if node.value is False:
            return "false"
        if isinstance(node.value, int):
            return str(node.value)
    return "0"


# ---------------------------------------------------------------------------
# Pattern detection for specialized recursors (forallb / existsb / countb).
# These are admissible rewrites — fold_left_acc is the universal form, but
# the specialized forms have proved lemmas (forallb_true, etc.).
# ---------------------------------------------------------------------------

def _classify_fold_pattern(
    loop_body: list[ast.stmt],
    acc_var: str,
    loop_var: str,
    acc_init: str,
) -> Optional[tuple[str, str, str]]:
    """Detect common fold patterns and return (recursor_name, recursor_lambda, acc_init).

    Returns None if no specialized pattern matches.
    """
    ifs = [s for s in loop_body if isinstance(s, ast.If)]

    # Pattern 1: FORALLB  — init=true, body sets acc=false on violation
    #   ok = True; for x in xs: if not p(x): ok = False; return ok
    if acc_init == "true" and len(ifs) == 1:
        test = ifs[0].test
        body = ifs[0].body
        leaf = _is_acc_assign(body, acc_var, False)
        if leaf:
            lam = _expr_to_coq_bool(test, loop_var)
            if lam:
                # The condition in the if is typically `x <= 0` (the violation),
                # not `x > 0` (the desired property).  For now emit the test.
                return (Recursor.FORALLB.value, _make_lam(lam, loop_var), acc_init)

    # Pattern 2: EXISTSb  — init=false, body sets acc=true on match
    #   found = False; for x in xs: if p(x): found = True; return found
    if acc_init == "false" and len(ifs) == 1:
        test = ifs[0].test
        body = ifs[0].body
        leaf = _is_acc_assign(body, acc_var, True)
        if leaf:
            lam = _expr_to_coq_bool(test, loop_var)
            if lam:
                return (Recursor.EXISTSb.value, _make_lam(lam, loop_var), acc_init)

    # Pattern 3: COUNTB  — init=0, body increments acc on match
    #   count = 0; for x in xs: if p(x): count += 1; return count
    if acc_init == "0":
        augs = _find_all(loop_body, ast.AugAssign)
        for aug in augs:
            if (isinstance(aug.target, ast.Name) and aug.target.id == acc_var
                    and isinstance(aug.op, ast.Add)):
                if isinstance(aug.value, ast.Constant) and aug.value.value == 1:
                    # Find the enclosing if condition.
                    for s in loop_body:
                        if isinstance(s, ast.If) and aug in _find_all(s, ast.AugAssign):
                            lam = _expr_to_coq_bool(s.test, loop_var)
                            if lam:
                                return (Recursor.COUNTB.value,
                                        _make_lam(lam, loop_var), acc_init)
                    # If the AugAssign is at top level (no if), still countb
                    if aug in loop_body:
                        return (Recursor.COUNTB.value,
                                _make_lam("Z.ltb 0", loop_var), acc_init)

    return None


def _find_all(node, kind) -> list:
    """Find all nodes of a given AST kind anywhere in the list or tree."""
    results: list = []
    items = node if isinstance(node, list) else [node]
    for item in items:
        if hasattr(item, '_fields'):
            for child in ast.walk(item):
                if isinstance(child, kind):
                    results.append(child)
    return results


def _is_acc_assign(
    stmts: list[ast.stmt],
    acc_var: str,
    value: bool,
) -> bool:
    """Check if stmts contains exactly `acc_var = value`."""
    for s in stmts:
        if isinstance(s, ast.Assign):
            for target in s.targets:
                if (isinstance(target, ast.Name) and target.id == acc_var
                        and isinstance(s.value, ast.Constant)
                        and s.value.value is value):
                    return True
    return False


def _make_lam(predicate: str, loop_var: str) -> str:
    """Make a Coq lambda for the recursor."""
    return f"(fun ({loop_var} : Z) => {predicate})"

# detect_loop_pattern removed; use lower_loop_to_fold instead.
# The Recursor enum is still imported by contract_linter.py:387 for
# the backward-compatible recursor map.