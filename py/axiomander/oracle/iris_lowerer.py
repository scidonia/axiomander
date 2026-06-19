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
    PyBooleanOp, PyListComp, PyListLiteral, PyDictLiteral,
    PySetLiteral, PyTupleLiteral,
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
                 contract_map: dict | None = None, param_types: dict[str, str] | None = None,
                 dict_params: set[str] | None = None,
                 list_params: set[str] | None = None):
        self.loc_map = loc_map      # "box.value" → "l__box_value"
        self._func_name = func_name
        self._contract_map = contract_map or {}
        self._param_types = param_types or {}
        self._dict_params = dict_params or set()
        self._list_params = list_params or set()
        self._set_vars: set[str] = set()   # local variables assigned a set literal
        self._vc = 0
        self._pure_conditions: list[SPure] = []
        self._var_renames: dict[str, str] = {}  # Py name → current IR name (SSA)
        self._rename_root: dict[str, str] = {}  # IR name → Py name (reverse)

    def _fresh_var(self, prefix: str = "t") -> str:
        self._vc += 1
        return f"_{prefix}{self._vc}"

    def _current_var(self, name: str) -> str:
        """Return the current IR variable name for a Python name (SSA tracking)."""
        return self._var_renames.get(name, name)

    def _loc_of(self, obj: str, attr: str | None = None) -> str:
        """Resolve a Python field access to an abstract location."""
        if attr:
            key = f"{obj}.{attr}"
        else:
            key = obj
        return self.loc_map.get(key, f"l__{key.replace('.', '_')}")

    def lower_expr(self, expr: PyExpr) -> Optional[SExpr]:
        if isinstance(expr, PyName):
            return SVar(name=self._current_var(expr.name))
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
        if isinstance(expr, PyListLiteral):
            return self._lower_compound(expr.elements, "list", "[]")
        if isinstance(expr, PyDictLiteral):
            keys = []
            vals = []
            for p in expr.pairs:
                k = self.lower_expr(p["key"])
                v = self.lower_expr(p["value"])
                if k is None or v is None:
                    return None
                if not isinstance(k, SLit) or not isinstance(v, SLit):
                    return None
                keys.append(k)
                vals.append(v)
            # Interleave keys and values: [k1, v1, k2, v2, ...]
            elements: list[SLit] = []
            for k, v in zip(keys, vals):
                elements.append(k)
                elements.append(v)
            return SLit(lit_type="dict", value="", elements=elements)
        if isinstance(expr, PySetLiteral):
            return self._lower_compound(expr.elements, "set", "{}")
        if isinstance(expr, PyTupleLiteral):
            return self._lower_compound(expr.elements, "tuple", "()")
        return None

    def _lower_compound(self, exprs, lit_type, empty_val):
        lowered = [self.lower_expr(e) for e in exprs]
        if any(l is None for l in lowered):
            return None
        items = [l for l in lowered if isinstance(l, SLit)]
        if len(items) != len(lowered):
            return None  # non-constant elements unsupported
        return SLit(lit_type=lit_type, value=empty_val, elements=items)

    def _lower_constant(self, expr: PyConstant) -> SExpr:
        if expr.py_type == "int":
            return SLit(lit_type="int", value=str(expr.value))
        if expr.py_type == "bool":
            return SLit(lit_type="bool", value="true" if expr.value else "false")
        if expr.py_type == "str":
            return SLit(lit_type="string", value=expr.value)
        if expr.py_type == "float":
            # Emit as LitFloat; Coq computes z2float at compile-time
            return SLit(lit_type="float", value=str(expr.value))
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
            if isinstance(inner, SLit) and inner.lit_type == "int":
                return SLit(lit_type="int", value=f"-{inner.value}")
            return SBinOp(op="sub", left=SLit(lit_type="int", value="0"), right=inner)
        return inner

    def _lower_subscript(self, expr: PySubscript) -> Optional[SExpr]:
        """obj[field] or d[key] → heap load or dict lookup."""
        obj_name = self._extract_name(expr.container)
        key = self.lower_expr(expr.key)
        if obj_name is None or key is None:
            return None
        # Dict access: lower to SApp call to transparent helper (not SDictGet)
        if self._param_types.get(obj_name) == "dict":
            return SApp(func="dict_index",
                        args=[SVar(name=obj_name), key])
        # String indexing: text[i] -> StrIndexOp
        if self._param_types.get(obj_name) in ("str", "string"):
            return SBinOp(op="str_index",
                          left=SVar(name=self._current_var(obj_name)),
                          right=key)
        # Field access: box.value → load from l__box_value
        loc = self._loc_of(obj_name)
        return SLoad(loc=loc)

    def _lower_attribute(self, expr: "PyAttribute") -> Optional[SExpr]:
        """obj.attr → heap load from obj.attr location, UNLESS obj.attr is
        an enum member -> IntLit, or obj is a model param -> SApp to
        field_access transparent helper."""
        if isinstance(expr.obj, PyName):
            obj_name = expr.obj.name
            # Check for enum member resolution (IntEnum in contracts)
            from axiomander.oracle.shape_ir import lookup_enum_value, lookup_shape
            ev = lookup_enum_value(obj_name, expr.attr)
            if ev is not None:
                return SLit(lit_type="int", value=str(ev))
            # Pydantic/dataclass model param: field access via helper
            model_type = self._param_types.get(obj_name, "")
            if model_type and lookup_shape(model_type) is not None:
                return SApp(func="field_access",
                            args=[SVar(name=obj_name),
                                  SLit(lit_type="string",
                                       value=expr.attr)])
        else:
            obj_name = self._extract_name(expr.obj)
        if obj_name:
            loc = self._loc_of(obj_name, expr.attr)
            return SLoad(loc=loc)
        return None

    def _lower_call(self, expr: PyCall) -> Optional[SExpr]:
        """Function call: heap builtins, method calls, or opaque SApp."""

        # -- Heap builtins: ref / load / store --
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

        # -- Collection constructors: set() / list() / dict() --
        if expr.func == "set" and not expr.args:
            return SLit(lit_type="set", value="{}")
        if expr.func == "list" and not expr.args:
            return SLit(lit_type="list", value="[]")
        if expr.func == "dict" and not expr.args:
            return SLit(lit_type="dict", value="{}")
        if expr.func == "isinstance" and len(expr.args) == 2:
            type_arg = expr.args[1]
            type_name = None
            if isinstance(type_arg, PyName):
                type_name = type_arg.name
            if type_name in ("int", "bool"):
                return SLit(lit_type="bool", value="true")
            return SLit(lit_type="bool", value="false")

        # -- len(xs): LengthOp.  For heap-allocated lists, load first;
        #    for list/string/dict parameters, use the variable directly
        #    (it holds a value after substitution, not a heap loc).
        if expr.func == "len" and len(expr.args) == 1:
            arg = expr.args[0]
            if isinstance(arg, PyName):
                if (arg.name in self._list_params
                        or self._param_types.get(arg.name) in ("str", "string", "dict", "set", "tuple")):
                    return SBinOp(op="length",
                                  left=SVar(name=self._current_var(arg.name)),
                                  right=SLit(lit_type="int", value="0"))
                else:
                    return SBinOp(op="length",
                                  left=SLoad(loc=arg.name),
                                  right=SLit(lit_type="int", value="0"))

        # -- Method calls: xs.append(v) / s.startswith(p) / d.get(k, d) --
        if expr.is_method and "." in expr.func:
            parts = expr.func.rsplit(".", 1)
            obj_name = parts[0]
            method = parts[1]
            if method in ("append", "add"):
                v = self.lower_expr(expr.args[0]) if expr.args else None
                if v is None:
                    return None
                op_name = "set_add" if method == "add" else "append"
                # Value-type param (list/dict/set/tuple): compute new value
                # via AppendOp/SetAddOp and rebind the variable for subsequent code.
                if (obj_name in self._list_params
                        or obj_name in self._set_vars
                        or self._param_types.get(obj_name) in
                        ("list", "dict", "set", "tuple", "str", "string")):
                    old_name = self._current_var(obj_name)
                    fresh = self._fresh_var(obj_name)
                    self._var_renames[obj_name] = fresh
                    self._rename_root[fresh] = obj_name
                    return SBinOp(op=op_name,
                                  left=SVar(name=old_name), right=v)
                # Heap-allocated list: load, append, store.
                tmp_var = self._fresh_var("_ap")
                return SLet(var=tmp_var,
                            value=SLoad(loc=obj_name),
                            body=SStore(loc=obj_name,
                                value=SBinOp(op="append",
                                    left=SVar(tmp_var),
                                    right=v)))
            # Other method calls: pass the object as first argument
            # so the callee table entry (params=[obj, ...]) matches.
            obj_expr = SVar(name=obj_name)
            args = [obj_expr] + [a for a in (
                self.lower_expr(a) for a in expr.args) if a is not None]
            if None in args:
                return None
            return SApp(func=expr.func, args=args)

        # -- Opaque: call to unknown / user function --
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
        if op == "notin":
            # Emit [in(left,right) == false]
            return SBinOp(op="eq",
                          left=SBinOp(op="in", left=left, right=right),
                          right=SLit(lit_type="bool", value="false"))
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
        # Mutable collections (empty lists/dicts) need heap allocation
        # so that append / len / subscript work via load/store.
        # Sets are value types (in/add work via binop_eval directly).
        if isinstance(val, SLit) and val.lit_type == "set":
            self._set_vars.add(stmt.target)
            return SLet(var=stmt.target, value=val, body=SVar(stmt.target))
        if isinstance(val, SLit) and val.lit_type in ("list", "dict"):
            if not val.elements:  # empty → need allocation
                val = SAlloc(value=val)
            else:
                pass  # non-empty literals passed as values (for for-loops)
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
        """d[key] = val → dict set (value-type) or heap store."""
        obj_name = self._extract_name(stmt.container)
        key = self.lower_expr(stmt.key)
        val = self.lower_expr(stmt.value)
        if obj_name is None or key is None or val is None:
            return None
        # Value-type dict: d[k] = v via DictSetOp with SSA rebinding
        if (self._param_types.get(obj_name) == "dict"
                or obj_name in self._dict_params):
            # The key and value are lowered; the tuple encoding
            # (LitTuple [k; v]) is constructed by the ANF pass /
            # call_transparent unfolding of the dict_set helper.
            return SApp(func="dict_set",
                        args=[SVar(name=self._current_var(obj_name)), key, val])
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
        """Raise exception — becomes SRaise of a LitExn (label + unit payload)."""
        exc_type = getattr(stmt, 'exc_type', 'Exception')
        return SRaise(exc=SLit(lit_type="exn", value=exc_type))

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
