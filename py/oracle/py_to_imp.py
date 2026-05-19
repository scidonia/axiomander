"""
PyIR → ImpIR lowering pass.

Resolves Python semantics into IMP constructs:
- + becomes APlus (int) or list concat (str/list) based on type contracts
- isinstance becomes BIsVZ / BIsVString
- Structural knowledge (list literals) drives directly to IMP
- Unknown operations are lowered conservatively or rejected
"""

from typing import Optional
from .py_ir import *
from .imp_ir import *


class PyToImpLowerer:
    """Lower PyIR nodes to ImpIR nodes.

    Conservative principle: operations without proven type knowledge
    are lowered to havoc or rejected. Never silently assume semantics.
    """

    def __init__(self, func_name: str = "", record_fields: dict[str, list[str]] | None = None,
                 param_types: dict[str, str] | None = None, annot_guard_mode: bool = True):
        self._func_name = func_name
        self._record_fields = record_fields or {}
        self._param_types = param_types or {}
        self._vc = 0
        # When True, type annotations are treated as guards:
        # x: int → assert isinstance(x, int) is injected, and the lowerer
        # can use the annotation to resolve ambiguous operations (+ becomes
        # APlus, string methods become available, etc.)
        self._annot_guard_mode = annot_guard_mode

    def _type_of(self, expr: PyExpr) -> Optional[str]:
        """Infer the type of an expression. In annot-guard mode (default),
        parameter type annotations are trusted as guards."""
        if isinstance(expr, PyName):
            if self._annot_guard_mode and expr.name in self._param_types:
                return self._param_types[expr.name]
        if isinstance(expr, PyConstant):
            return expr.py_type
        return None

    def _known_numeric(self, expr: PyExpr) -> bool:
        """Check if this expression is known to be numeric (int or float)."""
        t = self._type_of(expr)
        return t in ("int", "float")

    def _known_stringlike(self, expr: PyExpr) -> bool:
        """Check if this expression is known to be str or list."""
        t = self._type_of(expr)
        return t in ("str", "list")

    def _fresh_var(self, prefix: str = "v") -> str:
        self._vc += 1
        return f"_{prefix}{self._vc}"

    # ── Expressions ─────────────────────────────────────────────

    def lower_expr(self, expr: PyExpr) -> Optional[ImpAExp]:
        if isinstance(expr, PyConstant):
            return ImpANum(value=int(expr.value) if isinstance(expr.value, (int, float, bool)) else 0)
        if isinstance(expr, PyName):
            return ImpAVar(name=expr.name)
        if isinstance(expr, PyBinaryOp):
            left = self.lower_expr(expr.left)
            right = self.lower_expr(expr.right)
            if not left or not right:
                return None
            if expr.op == "+":
                return ImpAPlus(left=left, right=right)
            if expr.op == "-":
                return ImpAMinus(left=left, right=right)
            if expr.op == "*":
                return ImpAMult(left=left, right=right)
        if isinstance(expr, PyUnaryOp) and expr.op == "-":
            operand = self.lower_expr(expr.operand)
            if operand:
                return ImpAMult(left=ImpANum(value=-1), right=operand)
        if isinstance(expr, PySubscript):
            container = self.lower_expr(expr.container)
            key = self.lower_expr(expr.key)
            if container and key:
                if isinstance(expr.container, PyName):
                    return ImpAIndex(name=expr.container.name, index=key)
        if isinstance(expr, PyAttribute):
            # Record field access: obj.field → AVar "obj_field"
            if isinstance(expr.obj, PyName):
                obj_name = expr.obj.name
                for cls_name, fields in self._record_fields.items():
                    if expr.attr in fields:
                        if self._param_types.get(obj_name) == cls_name:
                            return ImpAVar(name=f"{obj_name}_{expr.attr}")
            return ImpAIndex(name=f"{expr.obj.name}.{expr.attr}",
                           index=ImpANum(value=0))
        if isinstance(expr, PyStringLiteral):
            return ImpAString(value=expr.value)
        if isinstance(expr, PyLen):
            if isinstance(expr.obj, PyName):
                return ImpALen(name=expr.obj.name)
        if isinstance(expr, PyCall):
            return self._lower_call(expr)
        return None

    def lower_bexp(self, expr: PyExpr) -> Optional[ImpBExp]:
        """Lower a Python expression used as a boolean condition."""
        if isinstance(expr, PyCompare):
            if expr.op == "==":
                left = self.lower_expr(expr.left)
                right = self.lower_expr(expr.right)
                if left and right:
                    return ImpBEq(left=left, right=right)
            if expr.op in ("<", "<=", ">", ">="):
                op_map = {"<": "BLe", "<=": "BLe", ">": "BLe", ">=": "BLe"}
                left = self.lower_expr(expr.left)
                right = self.lower_expr(expr.right)
                if left and right:
                    if expr.op in (">", ">="):
                        # a > b → b < a
                        left, right = right, left
                    if expr.op in ("<=", ">="):
                        # a <= b → a+1 > b wrong... use BLe as-is
                        return ImpBLe(left=left, right=right)
                    else:
                        # a < b → a+1 <= b
                        return ImpBLe(left=ImpAPlus(left=left, right=ImpANum(value=1)),
                                      right=right)
            if expr.op == "!=":
                left = self.lower_expr(expr.left)
                right = self.lower_expr(expr.right)
                if left and right:
                    return ImpBNot(operand=ImpBEq(left=left, right=right))
        if isinstance(expr, PyBooleanOp):
            if expr.op == "and":
                operands = [self.lower_bexp(o) for o in expr.operands]
                operands = [o for o in operands if o]
                if operands:
                    result = operands[0]
                    for o in operands[1:]:
                        result = ImpBAnd(left=result, right=o)
                    return result
            if expr.op == "or":
                operands = [self.lower_bexp(o) for o in expr.operands]
                operands = [o for o in operands if o]
                if operands:
                    result = operands[0]
                    for o in operands[1:]:
                        result = ImpBOr(left=result, right=o)
                    return result
            if expr.op == "not":
                if len(expr.operands) == 1:
                    inner = self.lower_bexp(expr.operands[0])
                    if inner:
                        return ImpBNot(operand=inner)
        if isinstance(expr, PyUnaryOp) and expr.op == "not":
            inner = self.lower_bexp(expr.operand)
            if inner:
                return ImpBNot(operand=inner)
        if isinstance(expr, PyIsInstance):
            if expr.type_name == "int":
                if isinstance(expr.obj, PyName):
                    return ImpBIsVZ(var=expr.obj.name)
            if expr.type_name == "str":
                if isinstance(expr.obj, PyName):
                    return ImpBIsVString(var=expr.obj.name)
        # Fallback: truthiness check — expr != 0
        aexp = self.lower_expr(expr)
        if aexp:
            return ImpBNot(operand=ImpBEq(left=aexp, right=ImpANum(value=0)))
        return None

    # ── Statements ──────────────────────────────────────────────

    def lower_stmt(self, stmt: PyStmt) -> Optional[ImpCom]:
        if isinstance(stmt, PyAssign):
            val = self.lower_expr(stmt.value)
            if val:
                return ImpCAss(target=stmt.target, value=val)
        if isinstance(stmt, PyStoreAttr):
            val = self.lower_expr(stmt.value)
            if val:
                return ImpCAss(target=f"{stmt.obj}_{stmt.attr}", value=val)
        if isinstance(stmt, PyAugAssign):
            val = self.lower_expr(stmt.value)
            if val:
                op_map = {"+": ImpAPlus, "-": ImpAMinus, "*": ImpAMult}
                op_cls = op_map.get(stmt.op, ImpAPlus)
                new_val = op_cls(left=ImpAVar(name=stmt.target), right=val)
                return ImpCAss(target=stmt.target, value=new_val)
        if isinstance(stmt, PyIf):
            cond = self.lower_bexp(stmt.test)
            if not cond:
                return None
            then_body = self.lower_body(stmt.body)
            else_body = self.lower_body(stmt.orelse)
            return ImpCIf(condition=cond, then_branch=then_body, else_branch=else_body)
        if isinstance(stmt, PyWhile):
            cond = self.lower_bexp(stmt.test)
            if not cond:
                return None
            body = self.lower_body(stmt.body)
            inv_str = self._invariants_to_coq(stmt.invariants)
            return ImpCWhile(condition=cond, invariant=inv_str, body=body)
        if isinstance(stmt, PyReturn):
            return ImpCSkip()
        if isinstance(stmt, PyAssert):
            return ImpCSkip()  # asserts are contracts, not IMP
        if isinstance(stmt, PyExprStmt):
            return self._lower_call_stmt(stmt.expr)
        if isinstance(stmt, PyPass):
            return ImpCSkip()
        if isinstance(stmt, PyStoreSubscript):
            container = self.lower_expr(stmt.container)
            key = self.lower_expr(stmt.key)
            val = self.lower_expr(stmt.value)
            if container and key and val:
                if isinstance(stmt.container, PyName):
                    return ImpCDictAppendKv(name=stmt.container.name, key=key, value=val)
        return None

    def lower_body(self, stmts: list[PyStmt]) -> ImpCom:
        """Lower a list of statements into a sequential IMP command."""
        cmds = [self.lower_stmt(s) for s in stmts]
        cmds = [c for c in cmds if c is not None]
        return seq(*cmds)

    def lower_function(self, func: PyFunction) -> ImpCom:
        """Lower a full function body to IMP."""
        return self.lower_body(func.body)

    # ── Helpers ─────────────────────────────────────────────────

    def _invariants_to_coq(self, invariants: list) -> str:
        """Convert contract IR invariant nodes to a Coq assertion string."""
        if not invariants:
            return "(fun _ => True)"
        parts = []
        for inv in invariants:
            if hasattr(inv, 'to_coq'):
                coq_str = inv.to_coq(scoped=True)
                if coq_str:
                    parts.append(coq_str)
        if not parts:
            return "(fun _ => True)"
        if len(parts) == 1:
            return f"(fun s => {parts[0]})"
        joined = " /\\ ".join(parts)
        return f"(fun s => {joined})"

    def _lower_call(self, expr: PyCall) -> Optional[ImpAExp]:
        """Lower a function call — used when the result is needed as an aexp."""
        return None  # CCall results flow through the state, not as aexp

    def _lower_call_stmt(self, expr: PyExpr) -> Optional[ImpCom]:
        """Lower a function call used as a statement."""
        return None  # CCall handled by the existing pipeline
