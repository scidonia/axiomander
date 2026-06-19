"""
Dimensional Analysis Checker for Axiomander.

Walks Python AST expressions and infers dimensions from the units: section
declarations. Generates DimConstraints at addition/subtraction nodes and
checks them for consistency.

This is a pre-pass that runs before the Coq WP proof. It catches structural
unit errors (adding USD to persons) that WP cannot see because the IMP model
treats all numeric values as VZ or VFloat without dimension information.

The checker operates on Python AST nodes (not PyIR) because dimension
information is attached to Python variable names, and the Python AST
preserves source locations for error reporting.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional

from .dim_ir import (
    DimVec,
    UnitsSection,
    DimConstraint,
    DimViolation,
    DimInference,
    check_constraints,
)


# ── Dimension environment ─────────────────────────────────────────

class DimEnv:
    """Dimension environment: maps variable names to DimVec.

    Supports scoped updates (for temporary assignments) and tracks
    variables whose dimensions are unknown (not yet declared or inferred).
    """

    def __init__(self, units: UnitsSection, param_names: list[str]):
        # Seed from the units: section declarations
        self._dims: dict[str, DimVec] = {}
        self._unknown: set[str] = set()

        for decl in units.declarations:
            # "result" is the return value -- not a local variable during inference
            if decl.var_name != "result" and "." not in decl.var_name:
                self._dims[decl.var_name] = decl.dim

    def get(self, name: str) -> Optional[DimVec]:
        """Return the dimension of a variable, or None if unknown."""
        return self._dims.get(name)

    def set(self, name: str, dim: DimVec) -> None:
        """Record the dimension of a variable."""
        self._dims[name] = dim
        self._unknown.discard(name)

    def mark_unknown(self, name: str) -> None:
        """Mark a variable as having unknown dimension."""
        if name not in self._dims:
            self._unknown.add(name)

    @property
    def unknown_vars(self) -> set[str]:
        return set(self._unknown)


# ── Dimension inference ───────────────────────────────────────────

class DimChecker(ast.NodeVisitor):
    """Infer dimensions for a function body and collect constraints.

    Walk order: statements first (to populate the environment from
    assignments), then check expression dimensions against declarations.
    """

    def __init__(self, func_node: ast.FunctionDef, units: UnitsSection):
        self._units = units
        self._constraints: list[DimConstraint] = []
        param_names = [arg.arg for arg in func_node.args.args]
        self._env = DimEnv(units, param_names)
        self._func_node = func_node

    def run(self) -> DimInference:
        """Run the dimension checker and return the inference result."""
        # First pass: walk the body to collect assignments and build env
        for stmt in self._func_node.body:
            self._check_stmt(stmt)

        # Check constraints
        violations = check_constraints(self._constraints)

        # Build var_dims snapshot
        var_dims: dict[str, DimVec] = {}
        for decl in self._units.declarations:
            var_dims[decl.var_name] = decl.dim

        return DimInference(
            var_dims=var_dims,
            constraints=self._constraints,
            violations=violations,
            unknown_vars=self._env.unknown_vars,
        )

    # ── Statement handlers ───────────────────────────────────────

    def _check_stmt(self, node: ast.stmt) -> None:
        if isinstance(node, ast.Assign):
            self._check_assign(node)
        elif isinstance(node, ast.AugAssign):
            self._check_augassign(node)
        elif isinstance(node, ast.AnnAssign):
            if node.value:
                rhs_dim = self._infer_expr(node.value)
                if isinstance(node.target, ast.Name) and rhs_dim:
                    self._env.set(node.target.id, rhs_dim)
        elif isinstance(node, ast.Return):
            if node.value:
                self._check_return(node)
        elif isinstance(node, (ast.If, ast.While, ast.For)):
            self._check_compound(node)
        elif isinstance(node, ast.Assert):
            # Asserts don't affect dimension inference
            pass

    def _check_assign(self, node: ast.Assign) -> None:
        rhs_dim = self._infer_expr(node.value)
        for target in node.targets:
            if isinstance(target, ast.Name):
                name = target.id
                declared = self._units.dim_of(name)
                if declared and rhs_dim:
                    # Check assignment is dimensionally consistent
                    if not rhs_dim.compatible_with(declared):
                        self._constraints.append(DimConstraint(
                            lhs_dim=declared,
                            rhs_dim=rhs_dim,
                            operation="=",
                            line=node.lineno,
                            context=f"{name} = {ast.unparse(node.value)}",
                        ))
                if rhs_dim:
                    self._env.set(name, rhs_dim)
                else:
                    self._env.mark_unknown(name)

    def _check_augassign(self, node: ast.AugAssign) -> None:
        if not isinstance(node.target, ast.Name):
            return
        name = node.target.id
        lhs_dim = self._env.get(name)
        rhs_dim = self._infer_expr(node.value)
        if lhs_dim and rhs_dim:
            if isinstance(node.op, (ast.Add, ast.Sub)):
                # Addition/subtraction: dimensions must match
                self._constraints.append(DimConstraint(
                    lhs_dim=lhs_dim,
                    rhs_dim=rhs_dim,
                    operation="+=" if isinstance(node.op, ast.Add) else "-=",
                    line=node.lineno,
                    context=f"{name} {'+=' if isinstance(node.op, ast.Add) else '-='} {ast.unparse(node.value)}",
                ))
            elif isinstance(node.op, ast.Mult):
                # a *= b -> dim(a) = dim(a) * dim(b)
                new_dim = lhs_dim * rhs_dim
                self._env.set(name, new_dim)
            elif isinstance(node.op, (ast.Div, ast.FloorDiv)):
                new_dim = lhs_dim / rhs_dim
                self._env.set(name, new_dim)

    def _check_return(self, node: ast.Return) -> None:
        if not node.value:
            return
        ret_dim = self._infer_expr(node.value)
        declared_result = self._units.dim_of("result")
        if declared_result and ret_dim:
            if not ret_dim.compatible_with(declared_result):
                self._constraints.append(DimConstraint(
                    lhs_dim=declared_result,
                    rhs_dim=ret_dim,
                    operation="return",
                    line=node.lineno,
                    context=f"return {ast.unparse(node.value)}",
                ))

    def _check_compound(self, node: ast.stmt) -> None:
        """Recurse into compound statements."""
        body: list[ast.stmt] = []
        if isinstance(node, ast.If):
            body = node.body + node.orelse
        elif isinstance(node, ast.While):
            body = node.body + node.orelse
        elif isinstance(node, ast.For):
            body = node.body + node.orelse
        for stmt in body:
            self._check_stmt(stmt)

    # ── Expression dimension inference ───────────────────────────

    def _infer_expr(self, node: ast.expr) -> Optional[DimVec]:
        """Infer the dimension of an expression.

        Returns None if the dimension cannot be determined (unknown variable,
        function call without declared return dimension, etc.).
        """
        if isinstance(node, ast.Constant):
            return self._infer_constant(node)
        if isinstance(node, ast.Name):
            return self._infer_name(node)
        if isinstance(node, ast.BinOp):
            return self._infer_binop(node)
        if isinstance(node, ast.UnaryOp):
            return self._infer_unary(node)
        if isinstance(node, ast.Call):
            return self._infer_call(node)
        if isinstance(node, ast.Attribute):
            return self._infer_attribute(node)
        if isinstance(node, ast.IfExp):
            # Ternary: a if cond else b -- both branches must have same dim
            then_dim = self._infer_expr(node.body)
            else_dim = self._infer_expr(node.orelse)
            if then_dim and else_dim:
                self._constraints.append(DimConstraint(
                    lhs_dim=then_dim,
                    rhs_dim=else_dim,
                    operation="ternary",
                    line=node.lineno,
                    context=ast.unparse(node),
                ))
            return then_dim or else_dim
        return None

    def _infer_constant(self, node: ast.Constant) -> DimVec:
        """Numeric literals are dimensionless."""
        if isinstance(node.value, (int, float)):
            return DimVec.dimensionless()
        return DimVec.dimensionless()

    def _infer_name(self, node: ast.Name) -> Optional[DimVec]:
        dim = self._env.get(node.id)
        if dim is None:
            self._env.mark_unknown(node.id)
        return dim

    def _infer_binop(self, node: ast.BinOp) -> Optional[DimVec]:
        left_dim  = self._infer_expr(node.left)
        right_dim = self._infer_expr(node.right)

        if isinstance(node.op, (ast.Add, ast.Sub)):
            # Addition/subtraction: both operands must have the same dimension.
            # The result has the same dimension as the operands.
            if left_dim and right_dim:
                self._constraints.append(DimConstraint(
                    lhs_dim=left_dim,
                    rhs_dim=right_dim,
                    operation="+" if isinstance(node.op, ast.Add) else "-",
                    line=node.lineno,
                    context=ast.unparse(node),
                ))
                return left_dim  # result has same dim as operands (if consistent)
            return left_dim or right_dim

        if isinstance(node.op, ast.Mult):
            # Multiplication: compose dimensions
            if left_dim and right_dim:
                return left_dim * right_dim
            if left_dim and right_dim is not None and right_dim.is_dimensionless():
                return left_dim
            if right_dim and left_dim is not None and left_dim.is_dimensionless():
                return right_dim
            return None

        if isinstance(node.op, (ast.Div, ast.FloorDiv)):
            # Division: subtract dimension exponents
            if left_dim and right_dim:
                result = left_dim / right_dim
                # If result is dimensionless, it's still a valid dimensionless value
                return result
            if left_dim and right_dim is not None and right_dim.is_dimensionless():
                return left_dim
            return None

        if isinstance(node.op, ast.Mod):
            # Modulo: result has same dimension as dividend
            return left_dim

        if isinstance(node.op, ast.Pow):
            # Power: only valid with literal integer exponent
            if left_dim and isinstance(node.right, ast.Constant):
                exp = node.right.value
                if isinstance(exp, int):
                    return left_dim ** exp
                # Fractional exponent -- not supported in integer dim system
                return None
            return left_dim

        return None

    def _infer_unary(self, node: ast.UnaryOp) -> Optional[DimVec]:
        """Unary minus/plus preserves dimension. 'not' is dimensionless."""
        if isinstance(node.op, (ast.USub, ast.UAdd)):
            return self._infer_expr(node.operand)
        return DimVec.dimensionless()

    def _infer_call(self, node: ast.Call) -> Optional[DimVec]:
        """Function calls: use declared return dimension if available.

        For built-ins (abs, round, int, float, len, sum, min, max):
          - abs(x): same dim as x
          - round(x): same dim as x
          - int(x), float(x): same dim as x (unit-preserving cast)
          - len(x): dimensionless (count of elements)
          - sum(x): same dim as elements of x (if known)
          - min(x), max(x): same dim as x

        For unknown functions: return None (dimension not tracked).
        """
        func_name = ""
        if isinstance(node.func, ast.Name):
            func_name = node.func.id
        elif isinstance(node.func, ast.Attribute):
            func_name = node.func.attr

        # Unit-preserving built-ins
        if func_name in ("abs", "round", "int", "float") and node.args:
            return self._infer_expr(node.args[0])

        # Dimensionless results
        if func_name in ("len", "bool", "str"):
            return DimVec.dimensionless()

        # min/max: result has same dim as arguments (check they match)
        if func_name in ("min", "max") and node.args:
            dims = [self._infer_expr(a) for a in node.args]
            known = [d for d in dims if d is not None]
            if known:
                # All known args should have same dimension
                for d in known[1:]:
                    self._constraints.append(DimConstraint(
                        lhs_dim=known[0],
                        rhs_dim=d,
                        operation=func_name,
                        line=node.lineno,
                        context=ast.unparse(node),
                    ))
                return known[0]
            return None

        # sum() over a list -- return None (elements not tracked)
        if func_name == "sum":
            return None

        # Unknown function -- don't track dimension
        return None

    def _infer_attribute(self, node: ast.Attribute) -> Optional[DimVec]:
        """Attribute access: look up result.field dimension declarations."""
        if isinstance(node.value, ast.Name):
            # result.field or param.field
            full_name = f"{node.value.id}.{node.attr}"
            declared = self._units.dim_of(full_name)
            if declared:
                return declared
            # Check if the object has a declared dimension
            obj_dim = self._env.get(node.value.id)
            return obj_dim  # propagate object dimension to field access (approximate)
        return None


# ── Public API ────────────────────────────────────────────────────

def check_dimensions(
    func_node: ast.FunctionDef,
    units: UnitsSection,
) -> DimInference:
    """Run dimensional analysis on a function given its units declarations.

    Returns a DimInference with any violations found.
    No SMT needed -- DimVec equality is decided by Python frozenset equality.
    """
    checker = DimChecker(func_node, units)
    return checker.run()


def check_dimensions_from_source(
    source: str,
    func_name: str,
    units_lines: list[str],
) -> DimInference:
    """Convenience: parse source, extract function, run dimension check.

    units_lines: lines from the units: section of the docstring.
    """
    from .dim_ir import parse_units_section
    tree = ast.parse(source)
    func_node = next(
        (n for n in ast.walk(tree)
         if isinstance(n, ast.FunctionDef) and n.name == func_name),
        None,
    )
    if func_node is None:
        raise ValueError(f"Function {func_name!r} not found in source")
    units = parse_units_section(units_lines)
    return check_dimensions(func_node, units)
