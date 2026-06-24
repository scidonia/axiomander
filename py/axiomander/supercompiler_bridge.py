"""Bridge between contract_ir.Expr and the LambdaA supercompiler.

Provides:
- expr_to_p_expr(): compile contract expressions to LambdaA p_expr Coq syntax
- supercompile_expr(): call the Coq supercompiler via rocq compile + Compute
- p_expr_to_iris_prop(): embed supercompiled p_expr into an Iris-suitable Coq Prop
"""

from __future__ import annotations
import subprocess
import tempfile
import os
import re
from pathlib import Path
from typing import Optional, Union

from .oracle.contract_ir import (
    Var, IntLit, BoolLit, BinOp, Logical, LenExpr, StrLitExpr, FloatExpr,
    TupleExpr, DictExpr, SetExpr, ImpliesExpr, Expr
)


# ── Contract IR → LambdaA p_expr Coq syntax ────────────────────────

_BINOP_MAP = {
    "+": "PAddOp", "-": "PSubOp", "*": "PMulOp", "/": "PDivOp",
    "mod": "PModOp",
    "=": "PEqOp", "<>": "PNeOp", "<": "PLtOp", "<=": "PLeOp",
    ">": "PGtOp", ">=": "PGeOp",
}


def expr_to_p_expr(expr: Expr) -> Optional[str]:
    """Compile a contract_ir expression to LambdaA p_expr Coq syntax.

    Returns None if the expression cannot be represented in the pure
    LambdaA fragment (e.g. AllExpr, FieldAccess, IndexExpr).
    """
    k = getattr(expr, 'kind', None)

    if k == 'var':
        return _coq_pvar(expr.name)  # type: ignore[attr-defined]
    elif k == 'int':
        return _coq_plitint(expr.value)  # type: ignore[attr-defined]
    elif k == 'bool':
        return _coq_plitbool(expr.value)  # type: ignore[attr-defined]
    elif k == 'strlit':
        return _coq_plitstring(expr.value)  # type: ignore[attr-defined]
    elif k == 'float':
        return _coq_plitfloat(expr.value)  # type: ignore[attr-defined]
    elif k == 'tuple':
        return _coq_plittuple(expr.elements)  # type: ignore[attr-defined]
    elif k == 'dict':
        return _coq_plitdict(expr.elements)  # type: ignore[attr-defined]
    elif k == 'set':
        return _coq_plitset(expr.elements)  # type: ignore[attr-defined]
    elif k == 'binop':
        return _compile_binop(expr)  # type: ignore[attr-defined]
    elif k == 'logical':
        return _compile_logical(expr)  # type: ignore[attr-defined]
    elif k == 'implies':
        return _compile_implies(expr)  # type: ignore[attr-defined]
    elif k == 'len':
        return _compile_len(expr)  # type: ignore[attr-defined]

    return None


def _coq_pvar(name: str) -> str:
    return f'(PVar "{name}"%string)'


def _coq_plitint(n: int) -> str:
    if n >= 0:
        return f'(PVal (PLitInt {n}))'
    return f'(PVal (PLitInt (- {abs(n)})))'


def _coq_plitbool(b: bool) -> str:
    return f'(PVal (PLitBool {"true" if b else "false"}))'


def _coq_plitstring(s: str) -> str:
    return f'(PVal (PLitString "{s}"%string))'


def _coq_plitfloat(f: float) -> str:
    return f'(PVal (PLitFloat {f}%float))'


def _coq_plittuple(elements: list[Expr]) -> Optional[str]:
    compiled = _compile_elements(elements)
    if compiled is None:
        return None
    return f'(PVal (PLitTuple ({"; ".join(compiled)} :: nil)%list))'


def _coq_plitlist(elements: list[Expr]) -> Optional[str]:
    compiled = _compile_elements(elements)
    if compiled is None:
        return None
    return f'(PVal (PLitList ({"; ".join(compiled)} :: nil)%list))'


def _coq_plitdict(elements: list[Expr]) -> Optional[str]:
    pairs = _compile_pairs(elements)
    if pairs is None:
        return None
    return f'(PVal (PLitDict ({"; ".join(pairs)} :: nil)%list))'


def _coq_plitset(elements: list[Expr]) -> Optional[str]:
    compiled = _compile_elements(elements)
    if compiled is None:
        return None
    return f'(PVal (PLitSet ({"; ".join(compiled)} :: nil)%list))'


def _compile_elements(elements: list[Expr]) -> Optional[list[str]]:
    result = []
    for e in elements:
        pe = expr_to_p_expr(e)
        if pe is None:
            return None
        result.append(pe)
    return result


def _compile_pairs(elements: list[Expr]) -> Optional[list[str]]:
    pairs = []
    for i in range(0, len(elements), 2):
        k = expr_to_p_expr(elements[i])
        v = expr_to_p_expr(elements[i + 1]) if i + 1 < len(elements) else None
        if k is None or v is None:
            return None
        pairs.append(f"({k}, {v})")
    return pairs


def _compile_binop(expr) -> Optional[str]:
    op = expr.op
    coq_op = _BINOP_MAP.get(op)
    if coq_op is None:
        return None
    left = expr_to_p_expr(expr.left)
    right = expr_to_p_expr(expr.right)
    if left is None or right is None:
        return None
    return f"(PBinOp {coq_op} {left} {right})"


def _compile_logical(expr) -> Optional[str]:
    operands = expr.operands
    if not operands:
        return None
    if expr.op == "not":
        inner = expr_to_p_expr(operands[0])
        if inner is None:
            return None
        return f'(PBinOp PEqOp {inner} (PVal (PLitBool false)))'
    op = "PAndOp" if expr.op == "and" else "POrOp"
    result = expr_to_p_expr(operands[0])
    if result is None:
        return None
    for o in operands[1:]:
        right = expr_to_p_expr(o)
        if right is None:
            return None
        result = f"(PBinOp {op} {result} {right})"
    return result


def _compile_implies(expr) -> Optional[str]:
    ante = expr_to_p_expr(expr.antecedent)
    conse = expr_to_p_expr(expr.consequent)
    if ante is None or conse is None:
        return None
    return f"(PBinOp POrOp (PBinOp PEqOp {ante} (PVal (PLitBool false))) {conse})"


def _compile_len(expr) -> Optional[str]:
    var = expr_to_p_expr(Var(name=expr.name))
    if var is None:
        return None
    return f"(PBinOp PLenOp {var} (PVal PLitUnit))"


# ── Supercompiler invocation ───────────────────────────────────────

def _find_project_root() -> Path:
    """Find the axiomander project root."""
    # Start from this file's directory and search upward
    current = Path(__file__).resolve().parent
    for _ in range(10):
        if (current / "coq").is_dir() and (current / "_build").is_dir():
            return current
        if current.parent == current:
            break
        current = current.parent
    raise RuntimeError("Cannot find axiomander project root (coq/ + _build/ dirs)")


def supercompile_p_expr(p_expr_str: str, fn_table: str = "nil", fuel: int = 500) -> Optional[str]:
    """Supercompile a LambdaA p_expr expression via rocq compile.

    Args:
        p_expr_str: Coq p_expr term string (e.g. '(PBinOp PAddOp ...)')
        fn_table: Coq fn_table term (default: "nil" = empty table)
        fuel: Fuel limit for supercompilation

    Returns:
        Simplified p_expr Coq string, or None on failure.
    """
    root = _find_project_root()
    build_dir = root / "_build" / "default" / "coq"

    if not build_dir.is_dir():
        build_dir = root / "_build"

    coq_source = f"""From Stdlib Require Import ZArith String.
Require Import SCoqShared.D1Fold SCoqShared.LambdaA.
Open Scope Z_scope.

Compute (snd (supercompile_full {fn_table} {fuel} {p_expr_str})).
"""

    with tempfile.NamedTemporaryFile(
        mode='w', suffix='.v', delete=False, dir=root
    ) as f:
        f.write(coq_source)
        tmp_path = f.name

    try:
        result = subprocess.run(
            [
                "rocq", "compile",
                "-R", str(build_dir), "SCoqShared",
                "-Q", str(build_dir), "SCoqShared",
                tmp_path,
            ],
            capture_output=True, text=True, timeout=120,
            cwd=str(root),
        )
        if result.returncode != 0:
            stderr = result.stderr[:500]
            stdout = result.stdout[:500]
            return None

        return _parse_compute_output(result.stdout)

    except subprocess.TimeoutExpired:
        return None
    finally:
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
        # Clean up generated .vo/.glob files
        for ext in ['.vo', '.vos', '.vok', '.glob']:
            gen = tmp_path.replace('.v', ext)
            if os.path.exists(gen):
                try:
                    os.unlink(gen)
                except OSError:
                    pass


def _parse_compute_output(output: str) -> Optional[str]:
    """Extract the p_expr term from Compute output.

    Input looks like:
         = PVal (PLitInt 3)
         : p_expr
    or:
         = PBinOp ... \n         ...
         : p_expr
    """
    lines = output.strip().split('\n')
    # Find the '=' line
    result_lines = []
    started = False
    for line in lines:
        stripped = line.strip()
        if stripped.startswith('= '):
            result_lines.append(stripped[2:])  # Remove '= '
            started = True
        elif started and stripped.startswith(': '):
            break  # Type annotation line
        elif started:
            result_lines.append(stripped)
    if not result_lines:
        return None
    return ' '.join(result_lines)


# ── Contract-level API ─────────────────────────────────────────────

def supercompile_contract(expr: Expr, fn_table: str = "nil", fuel: int = 500) -> Optional[str]:
    """Supercompile a contract expression.

    Args:
        expr: contract_ir.Expr node
        fn_table: Coq fn_table term for predicate inlining
        fuel: Fuellimit for supercompilation

    Returns:
        Coq p_expr string (simplified), or None if expr can't be
        compiled to p_expr or supercompilation fails.
    """
    p_expr_str = expr_to_p_expr(expr)
    if p_expr_str is None:
        return None
    return supercompile_p_expr(p_expr_str, fn_table=fn_table, fuel=fuel)


def supercompile_contract_to_prop(expr: Expr, fn_table: str = "nil", fuel: int = 500) -> Optional[str]:
    """Supercompile a contract expression and produce a Coq Prop string.

    Returns a Coq term of type Prop (using p_expr_prop_Z) that can be
    embedded in Iris pre/postconditions.  Returns None if the
    expression cannot be compiled or supercompiled.
    """
    simplified = supercompile_contract(expr, fn_table=fn_table, fuel=fuel)
    if simplified is None:
        return None
    return f"(p_expr_prop_Z ({simplified}))"
