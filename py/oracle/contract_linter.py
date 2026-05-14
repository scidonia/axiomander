"""
Contract Expression Language — Linter + IR-based compilation to Coq and SMT-LIB.

Validates that `assert` expressions are pure and in the contract language,
then compiles them to a shared IR (contract_ir.Expr) which can emit
both Coq Prop strings and SMT-LIB formulas.
"""

import ast
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Optional

from .contract_ir import (
    Expr, Var, IntLit, BoolLit, BinOp, Logical, LenExpr, IndexExpr,
    DictLenExpr, DictCountExpr, AllExpr, AnyExpr, SliceLenExpr,
)


# ─── Language Definition ──────────────────────────────────────────

class ExprKind(Enum):
    OK = "ok"
    IMPURE_CALL = "impure_call"
    SIDE_EFFECT = "side_effect"
    TYPE_ERROR = "type_error"
    UNSUPPORTED = "unsupported"
    NOT_BOOLEAN = "not_boolean"


PURE_BUILTINS = frozenset({
    "abs", "round", "int", "float", "bool", "str",
    "len", "min", "max", "sum", "sorted", "all", "any",
    "isinstance", "ord", "chr", "range", "pow", "sqrt",
})

PURE_MODULE_FUNCTIONS = frozenset({
    "math.sqrt", "math.pow", "math.ceil", "math.floor",
    "math.log", "math.log2", "math.log10",
    "math.sin", "math.cos", "math.tan",
    "math.abs", "math.fabs",
})


@dataclass
class LintViolation:
    line: int
    col: int
    kind: ExprKind
    message: str
    expression_text: str = ""


@dataclass
class LintResult:
    expr_node: ast.expr
    violations: list[LintViolation] = field(default_factory=list)
    coq_translation: str = ""
    smt_translation: str = ""
    ir: Optional[Expr] = None

    @property
    def is_valid(self) -> bool:
        return len(self.violations) == 0


# ─── Linter (IR-emitting visitor) ─────────────────────────────────

class ContractLinter(ast.NodeVisitor):
    """Validates assert expressions and compiles to IR.

    Each visit_* method returns an Expr IR node (or None for unsupported).
    The IR can then emit both Coq and SMT-LIB output.
    """

    def __init__(self, params: list[str] | None = None, context: str = "postcondition"):
        self.violations: list[LintViolation] = []
        self.params = params or []
        self.context = context

    def lint_expression(self, node: ast.expr) -> LintResult:
        """Convert a Python expression to IR. Returns LintResult with coq/smt."""
        assert isinstance(node, ast.expr)
        self.violations = []
        ir = self.visit(node)
        coq = ir.to_coq(scoped=(self.context != "precondition")) if ir else ""
        smt = ir.to_smt() if ir else ""
        return LintResult(
            expr_node=node,
            violations=list(self.violations),
            coq_translation=coq,
            smt_translation=smt,
            ir=ir,
        )

    def _violation(self, node: ast.AST, kind: ExprKind, message: str):
        self.violations.append(LintViolation(
            line=getattr(node, "lineno", 0),
            col=getattr(node, "col_offset", 0),
            kind=kind, message=message,
            expression_text=ast.unparse(node) if hasattr(ast, "unparse") else str(node),
        ))

    # ─── Visitors (return Expr) ──────────────────────────────────

    def visit_Compare(self, node: ast.Compare) -> Optional[Expr]:
        if len(node.ops) == 1 and len(node.comparators) == 1:
            left = self.visit(node.left)
            right = self.visit(node.comparators[0])
            op = self._translate_compare_op(node.ops[0])
            if left and right:
                return BinOp(op=op, left=left, right=right)
            return None
        # Chained: a < b < c → (a < b) /\ (b < c)
        parts = [node.left] + node.comparators
        conjuncts = []
        for i, op in enumerate(node.ops):
            left = self.visit(parts[i])
            right = self.visit(parts[i + 1])
            op_str = self._translate_compare_op(op)
            if left and right:
                conjuncts.append(BinOp(op=op_str, left=left, right=right))
        return Logical(op="and", operands=conjuncts) if conjuncts else None

    def visit_BoolOp(self, node: ast.BoolOp) -> Optional[Expr]:
        operands = [self.visit(v) for v in node.values]
        operands = [o for o in operands if o]
        if not operands:
            return None
        op = "and" if isinstance(node.op, ast.And) else "or"
        if len(operands) == 1:
            return operands[0]
        return Logical(op=op, operands=operands)

    def visit_UnaryOp(self, node: ast.UnaryOp) -> Optional[Expr]:
        inner = self.visit(node.operand)
        if not inner:
            return None
        if isinstance(node.op, ast.Not):
            return Logical(op="not", operands=[inner])
        if isinstance(node.op, ast.USub):
            return BinOp("*", IntLit(value=-1), inner)
        return None

    def visit_BinOp(self, node: ast.BinOp) -> Optional[Expr]:
        op_map = {
            ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
            ast.Div: "/", ast.FloorDiv: "/", ast.Mod: "mod",
        }
        op = op_map.get(type(node.op))
        if not op:
            return None
        left = self.visit(node.left)
        right = self.visit(node.right)
        return BinOp(op=op, left=left, right=right) if left and right else None

    def visit_Call(self, node: ast.Call) -> Optional[Expr]:
        name = self._get_call_name(node)
        if not name:
            self._violation(node, ExprKind.IMPURE_CALL,
                          f"Function call cannot be resolved")
            return None
        if name not in PURE_BUILTINS and name not in PURE_MODULE_FUNCTIONS:
            self._violation(node, ExprKind.IMPURE_CALL,
                          f"Function '{name}' not in pure whitelist")
            return None
        return self._translate_pure_call(node, name)

    def visit_Constant(self, node: ast.Constant) -> Expr:
        if isinstance(node.value, bool):
            return BoolLit(value=node.value)
        if isinstance(node.value, int):
            return IntLit(value=node.value)
        if isinstance(node.value, str):
            # String literals → IntLit(value=0) approximation (no string support yet)
            return IntLit(value=0)
        return IntLit(value=0)

    def visit_Name(self, node: ast.Name) -> Expr:
        return Var(name=node.id)

    def visit_Attribute(self, node: ast.Attribute) -> Expr:
        if isinstance(node.value, ast.Subscript):
            # items[i].field → IndexExpr with compound key
            base = node.value.value
            if isinstance(base, ast.Name):
                name = f"{base.id}.{node.attr}"
            else:
                name = f"?.{node.attr}"
            idx = self.visit(node.value.slice) if isinstance(node.value.slice, ast.expr) else IntLit(value=0)
            if not idx:
                idx = IntLit(value=0)
            return IndexExpr(name=name, index=idx)
        path = self._attribute_path(node)
        if self.context == "precondition":
            return Var(name=path.replace(".", "_"))
        return Var(path)

    def visit_Subscript(self, node: ast.Subscript) -> Optional[Expr]:
        if isinstance(node.value, ast.Name):
            name = node.value.id
        else:
            name = self._attribute_path(node.value) if isinstance(node.value, ast.Attribute) else "?"
        idx = self.visit(node.slice) if isinstance(node.slice, ast.expr) else IntLit(value=0)
        if not idx:
            idx = IntLit(value=0)
        return IndexExpr(name=name, index=idx)

    def generic_visit(self, node: ast.AST) -> None:
        self._violation(node, ExprKind.UNSUPPORTED,
                       f"Unsupported construct: {type(node).__name__}")
        return None

    # ─── Helpers ──────────────────────────────────────────────────

    def _get_call_name(self, node: ast.Call) -> Optional[str]:
        """Extract the fully-qualified function name from a call node."""
        assert isinstance(node, ast.Call)
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

    def _attribute_path(self, node: ast.Attribute) -> str:
        parts = []
        current = node
        while isinstance(current, ast.Attribute):
            parts.append(current.attr)
            current = current.value
        if isinstance(current, ast.Name):
            parts.append(current.id)
        return ".".join(reversed(parts))

    def _translate_compare_op(self, op: ast.cmpop) -> str:
        op_map = {
            ast.Eq: "=", ast.NotEq: "<>", ast.Lt: "<", ast.LtE: "<=",
            ast.Gt: ">", ast.GtE: ">=", ast.Is: "=", ast.IsNot: "<>",
        }
        return op_map.get(type(op), "=")

    def _translate_pure_call(self, node: ast.Call, name: str) -> Optional[Expr]:
        if name == "len":
            if node.args and isinstance(node.args[0], ast.Subscript):
                sub = node.args[0]
                if isinstance(sub.slice, ast.Slice):
                    # len(lst[i:j]) → SliceLenExpr
                    if isinstance(sub.value, ast.Name):
                        dname = sub.value.id
                        start = self.visit(sub.slice.lower) if sub.slice.lower else None
                        end = self.visit(sub.slice.upper) if sub.slice.upper else None
                        return SliceLenExpr(name=dname, start=start, end=end)
                # len(dict[key]) → DictLenExpr
                if isinstance(sub.value, ast.Name):
                    dname = sub.value.id
                    key = self.visit(sub.slice) if isinstance(sub.slice, ast.expr) else IntLit(value=0)
                    if key:
                        return DictLenExpr(name=dname, key=key)
            if node.args and isinstance(node.args[0], ast.Name):
                lst_name = node.args[0].id
                return LenExpr(name=lst_name)
            return IntLit(value=0)
        if name in ("abs", "min", "max"):
            args = [self.visit(a) for a in node.args]
            args = [a for a in args if a]
            if not args:
                return IntLit(value=0)
        if name == "len":
            if node.args and isinstance(node.args[0], ast.Name):
                arg_name = node.args[0].id
                if self._is_dict_name(arg_name):
                    return DictCountExpr(name=arg_name)
                return LenExpr(arg_name)
            if node.args and isinstance(node.args[0], ast.Subscript):
                sub = node.args[0]
                if isinstance(sub.value, ast.Name):
                    dname = sub.value.id
                    key = self.visit(sub.slice) if isinstance(sub.slice, ast.expr) else IntLit(value=0)
                    if key:
                        return DictLenExpr(name=dname, key=key)
            return IntLit(value=0)
        if name == "isinstance":
            return BoolLit(value=True)
        if name in ("all", "any"):
            return self._translate_quantifier(node, name)
        return IntLit(value=0)

    def _translate_quantifier(self, node: ast.Call, name: str) -> Optional[Expr]:
        """Translate all(p(x) for x in lst) or any(...) to AllExpr/AnyExpr."""
        if node.args and isinstance(node.args[0], ast.GeneratorExp):
            gen = node.args[0]
            if gen.generators and len(gen.generators) == 1:
                comp = gen.generators[0]
                if isinstance(comp.target, ast.Name) and isinstance(comp.iter, ast.Name):
                    var = comp.target.id
                    lst = comp.iter.id
                    pred = self.visit(gen.elt)
                    if pred:
                        if name == "all":
                            return AllExpr(var=var, lst=lst, pred=pred)
                        return AnyExpr(var=var, lst=lst, pred=pred)
        return BoolLit(value=True)


# ─── File-level linter (unchanged classification logic) ───────────

@dataclass
class AssertInfo:
    node: ast.Assert
    lineno: int
    col_offset: int
    classification: str
    lint_result: LintResult


def lint_file(source: str | Path) -> list[AssertInfo]:
    if isinstance(source, Path):
        source = source.read_text()
    tree = ast.parse(source)
    linter = ContractLinter()
    results: list[AssertInfo] = []

    def is_docstring(s):
        return (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                and isinstance(s.value.value, str))

    def walk_body(body: list[ast.stmt], ctx: str, parent_node=None):
        seen_code = False
        for i, stmt in enumerate(body):
            if isinstance(stmt, ast.Assert):
                if (i + 1 < len(body) and isinstance(body[i + 1], ast.Return)):
                    classification = "postcondition"
                elif ctx == "function" and not seen_code:
                    classification = "precondition"
                elif ctx == "loop" and not seen_code:
                    classification = "invariant"
                else:
                    classification = "general"

                lint_result = linter.lint_expression(stmt.test)
                results.append(AssertInfo(
                    node=stmt, lineno=stmt.lineno, col_offset=stmt.col_offset,
                    classification=classification, lint_result=lint_result,
                ))
            elif is_docstring(stmt) or isinstance(stmt, ast.Return):
                continue
            else:
                seen_code = True

            if isinstance(stmt, (ast.For, ast.While)):
                walk_body(stmt.body, "loop", stmt)
            elif isinstance(stmt, ast.If):
                walk_body(stmt.body, "if_body", stmt)
                if stmt.orelse:
                    walk_body(stmt.orelse, "if_else", stmt)

    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.FunctionDef):
            walk_body(node.body, "function", node)

    return results
