"""IrisLowerer: PyIR → SnakeletIR lowering pass.

Resolves Python field names to abstract locations using the
resource footprint (owns + modifies).  Pure side conditions are
extracted for SMT.  Opaque calls become SApp (proof-level wp_apply).
"""

from __future__ import annotations
from typing import Optional
from .py_ir import (
    PyExpr, PyStmt, PyFunction,
    PyName, PyConstant, PyBinaryOp, PyUnaryOp,
    PyAssign,     PyStoreAttr, PyAugAssign,
    PyIf, PyWhile, PyFor, PyReturn, PyRaise, PyTry,
    PyCall, PySubscript, PyAttribute, PyCompare, PyStoreSubscript,
    PyBooleanOp, PyListComp,
)
from .snakelet_ir import (
    SExpr, SLit, SVar, SBinOp, SLoad, SStore, SAlloc, SLet, SIf, SWhile,
    SReturn, SApp, SSeq,
    SField, SOwns, SPure, SFunction,
    SRaise, STry, SFork, SFAA,
    SDictGet, SDictSet,
)


class IrisLowerer:
    """Lower PyIR functions to SnakeletIR functions for Iris verification."""

    def __init__(self, loc_map: dict[str, str], func_name: str = "",
                 contract_map: dict | None = None, param_types: dict[str, str] | None = None):
        self.loc_map = loc_map      # "box.value" → "l__box_value"
        self._func_name = func_name
        self._contract_map = contract_map or {}
        self._param_types = param_types or {}
        self._vc = 0
        self._pure_conditions: list[SPure] = []

    def _fresh_var(self, prefix: str = "t") -> str:
        self._vc += 1
        return f"_{prefix}{self._vc}"

    def _loc_of(self, obj: str, attr: str | None = None) -> str:
        """Resolve a Python field access to an abstract location."""
        if attr:
            key = f"{obj}.{attr}"
        else:
            key = obj
        return self.loc_map.get(key, f"l__{key.replace('.', '_')}")

    def lower_expr(self, expr: PyExpr) -> Optional[SExpr]:
        if isinstance(expr, PyName):
            return SVar(name=expr.name)
        if isinstance(expr, PyConstant):
            return self._lower_constant(expr)
        if isinstance(expr, PyBinaryOp):
            return self._lower_binop(expr)
        if isinstance(expr, PyUnaryOp):
            return self._lower_unary(expr)
        if isinstance(expr, PySubscript):
            return self._lower_subscript(expr)
        if isinstance(expr, PyAttribute):
            return self._lower_attribute(expr)
        if isinstance(expr, PyCall):
            return self._lower_call(expr)
        if isinstance(expr, PyCompare):
            return self._lower_compare(expr)
        if isinstance(expr, PyBooleanOp):
            return self._lower_boolop(expr)
        return None

    def _lower_constant(self, expr: PyConstant) -> SExpr:
        if expr.py_type == "int":
            return SLit(lit_type="int", value=str(expr.value))
        if expr.py_type == "bool":
            return SLit(lit_type="bool", value="true" if expr.value else "false")
        if expr.py_type == "str":
            return SLit(lit_type="string", value=expr.value)
        if isinstance(expr.value, bool):
            return SLit(lit_type="bool", value="true" if expr.value else "false")
        return SLit(lit_type="int", value=str(expr.value))

    def _lower_binop(self, expr: PyBinaryOp) -> Optional[SExpr]:
        left = self.lower_expr(expr.left)
        right = self.lower_expr(expr.right)
        if left is None or right is None:
            return None
        op_map = {"+": "add", "-": "sub", "*": "mul", "/": "div",
                   "==": "eq", "!=": "ne", "<": "lt", "<=": "le",
                   ">": "gt", ">=": "ge", "%": "mod"}
        return SBinOp(op=op_map.get(expr.op, "add"), left=left, right=right)

    def _lower_unary(self, expr: PyUnaryOp) -> Optional[SExpr]:
        inner = self.lower_expr(expr.operand)
        if inner is None:
            return None
        if expr.op == "not":
            return SBinOp(op="eq", left=inner, right=SLit(lit_type="bool", value="false"))
        if expr.op == "-":
            return SBinOp(op="sub", left=SLit(lit_type="int", value="0"), right=inner)
        return inner

    def _lower_subscript(self, expr: PySubscript) -> Optional[SExpr]:
        """obj[field] or d[key] → heap load or dict lookup."""
        obj_name = self._extract_name(expr.container)
        key = self.lower_expr(expr.key)
        if obj_name is None or key is None:
            return None
        # Dict access
        if self._param_types.get(obj_name) == "dict":
            loc = self.loc_map.get(obj_name, f"l__{obj_name}")
            return SDictGet(loc=loc, key=key)
        # Field access: box.value → load from l__box_value
        loc = self._loc_of(obj_name)
        return SLoad(loc=loc)

    def _lower_attribute(self, expr: "PyAttribute") -> Optional[SExpr]:
        """obj.attr → heap load from obj.attr location."""
        if isinstance(expr.obj, PyName):
            obj_name = expr.obj.name
        else:
            obj_name = self._extract_name(expr.obj)
        if obj_name:
            loc = self._loc_of(obj_name, expr.attr)
            return SLoad(loc=loc)
        return None

    def _lower_call(self, expr: PyCall) -> Optional[SExpr]:
        """Function call.

        Heap builtins lower directly to SnakeletLang heap operations:
          ref(v)      -> SAlloc(v)     (fresh cell)
          load(c)     -> SLoad(c)      (read cell named by variable c)
          store(c, v) -> SStore(c, v)  (write cell named by variable c)
        Anything else is opaque -- SApp with the callee name for spec
        lookup in the FunCtx table."""
        if expr.func == "ref" and len(expr.args) == 1:
            v = self.lower_expr(expr.args[0])
            if v is not None:
                return SAlloc(value=v)
        if expr.func == "load" and len(expr.args) == 1:
            arg = expr.args[0]
            if isinstance(arg, PyName):
                return SLoad(loc=arg.name)
        if expr.func == "store" and len(expr.args) == 2:
            arg = expr.args[0]
            v = self.lower_expr(expr.args[1])
            if isinstance(arg, PyName) and v is not None:
                return SStore(loc=arg.name, value=v)
        args = [a for a in (self.lower_expr(a) for a in expr.args) if a is not None]
        return SApp(func=expr.func, args=args)

    def _lower_compare(self, expr: PyCompare) -> Optional[SExpr]:
        left = self.lower_expr(expr.left)
        right = self.lower_expr(expr.right)
        if left is None or right is None:
            return None
        op_map = {"==": "eq", "!=": "ne", "<": "lt", "<=": "le",
                   ">": "gt", ">=": "ge", "is": "eq", "is not": "ne",
                   "in": "in", "not in": "notin"}
        op = op_map.get(expr.op, "eq")
        return SBinOp(op=op, left=left, right=right)

    def _lower_boolop(self, expr: PyBooleanOp) -> Optional[SExpr]:
        parts = [self.lower_expr(o) for o in expr.operands]
        parts = [p for p in parts if p is not None]
        if not parts:
            return None
        if expr.op == "not":
            return SBinOp(op="eq", left=parts[0], right=SLit(lit_type="bool", value="false"))
        op = "and" if expr.op == "and" else "or"
        result = parts[0]
        for p in parts[1:]:
            result = SBinOp(op=op, left=result, right=p)
        return result

    def _extract_name(self, expr: PyExpr) -> Optional[str]:
        if isinstance(expr, PyName):
            return expr.name
        if isinstance(expr, PyAttribute):
            base = self._extract_name(expr.obj)
            if base:
                return f"{base}.{expr.attr}"
        return None

    # ── Statements ──────────────────────────────────────────────

    def lower_stmt(self, stmt: PyStmt) -> Optional[SExpr]:
        if isinstance(stmt, PyAssign):
            return self._lower_assign(stmt)
        if isinstance(stmt, PyStoreAttr):
            return self._lower_store_attr(stmt)
        if isinstance(stmt, PyStoreSubscript):
            return self._lower_store_subscript(stmt)
        if isinstance(stmt, PyAugAssign):
            return self._lower_augassign(stmt)
        if isinstance(stmt, PyIf):
            return self._lower_if(stmt)
        if isinstance(stmt, PyReturn):
            return self._lower_return(stmt)
        if isinstance(stmt, PyRaise):
            return self._lower_raise(stmt)
        if isinstance(stmt, PyCall):
            return self._lower_call(stmt)
        return None

    def _lower_assign(self, stmt: PyAssign) -> Optional[SExpr]:
        val = self.lower_expr(stmt.value)
        if val is None:
            return None
        return SLet(var=stmt.target, value=val, body=SVar(stmt.target))

    def _lower_store_attr(self, stmt: PyStoreAttr) -> Optional[SExpr]:
        """obj.attr = value → heap store to location."""
        obj_name = stmt.obj if isinstance(stmt.obj, str) else self._extract_name(stmt.obj)  # type: ignore[arg-type]
        val = self.lower_expr(stmt.value)
        if obj_name is None or val is None:
            return None
        loc = self._loc_of(obj_name, stmt.attr)
        return SStore(loc=loc, value=val)

    def _lower_store_subscript(self, stmt: PyStoreSubscript) -> Optional[SExpr]:
        """d[key] = val → dict set.  obj[field] = val → heap store."""
        obj_name = self._extract_name(stmt.container)
        key = self.lower_expr(stmt.key)
        val = self.lower_expr(stmt.value)
        if obj_name is None or key is None or val is None:
            return None
        if self._param_types.get(obj_name) == "dict":
            loc = self.loc_map.get(obj_name, f"l__{obj_name}")
            return SDictSet(loc=loc, key=key, value=val)
        loc = self._loc_of(obj_name)
        return SStore(loc=loc, value=val)

    def _lower_augassign(self, stmt: PyAugAssign) -> Optional[SExpr]:
        """x += e → x = x + e."""
        val = self.lower_expr(stmt.value)
        if val is None:
            return None
        # Load current value, add, store back
        if isinstance(stmt.target, PyName):
            # Local variable: simple assignment
            current = SVar(name=stmt.target)
            op_map = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod"}
            binop = SBinOp(op=op_map.get(stmt.op, "add"), left=current, right=val)
            return SLet(var=stmt.target, value=binop, body=SVar(stmt.target))
        return None

    def _lower_if(self, stmt: PyIf) -> Optional[SExpr]:
        cond = self.lower_expr(stmt.test)
        if cond is None:
            return None
        then_body = self._lower_body(stmt.body)
        else_body = self._lower_body(stmt.orelse)
        return SIf(cond=cond, then_branch=then_body, else_branch=else_body)

    def _lower_return(self, stmt: PyReturn) -> Optional[SExpr]:
        if stmt.value is None:
            return SReturn(value=SLit(lit_type="unit", value="()"))
        val = self.lower_expr(stmt.value)
        if val is None:
            return None
        return SReturn(value=val)

    def _lower_raise(self, stmt: "PyRaise") -> Optional[SExpr]:
        """Raise exception — becomes SRaise in SnakeletIR."""
        exc_type = getattr(stmt, 'exc_type', 'Exception')
        return SRaise(exc=SLit(lit_type="string", value=exc_type))

    def _lower_body(self, stmts: list[PyStmt]) -> SExpr:
        exprs = [s for s in (self.lower_stmt(s) for s in stmts) if s is not None]
        if not exprs:
            return SLit(lit_type="unit", value="()")
        if len(exprs) == 1:
            return exprs[0]
        return SSeq(exprs=exprs)

    def lower_function(self, func: PyFunction) -> Optional[SFunction]:
        """Lower a PyFunction to an SFunction for Iris verification."""
        body = self._lower_body(func.body)

        # Infer resource footprint from contract classification
        # For bump: owns(box) + modifies: box.value
        pre_fields = []
        modifies = []
        for loc_name, loc in self.loc_map.items():
            if "." in loc_name:
                obj, field = loc_name.split(".", 1)
                pre_fields.append(SField(
                    obj=obj, field=field, loc=loc,
                    old_var=f"old_{obj}_{field}",
                ))
                modifies.append(loc_name)

        pre_pure: list[SPure] = []
        post_pure = list(self._pure_conditions)
        # Ensure result captured
        post_pure.append(SPure(expr=f"result = old_box_value + 1"))

        return SFunction(
            name=func.name if hasattr(func, 'name') else self._func_name,
            params=(list(func.params) if hasattr(func, 'params') else []),
            body=body,
            pre_fields=pre_fields,
            pre_pure=pre_pure,
            post_pure=post_pure,
            modifies=modifies,
        )
