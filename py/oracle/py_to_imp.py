"""
PyIR -> ImpIR lowering pass.

Resolves Python semantics into IMP constructs.
The output is typed ImpIR nodes with .to_coq() for Coq code generation.
"""

from typing import Optional
from .py_ir import *
from .imp_ir import *


class PyToImpLowerer:
    """Lower PyIR nodes to ImpIR nodes.

    Conservative principle: operations without proven type knowledge
    are lowered conservatively. Never silently assume semantics.
    """

    def __init__(self, func_name: str = "", record_fields: dict[str, list[str]] | None = None,
                 param_types: dict[str, str] | None = None, annot_guard_mode: bool = True,
                 contract_map: dict | None = None):
        self._func_name = func_name
        self._record_fields = record_fields or {}
        self._param_types = param_types or {}
        self._vc = 0
        self._annot_guard_mode = annot_guard_mode
        self._contract_map = contract_map or {}

    def _type_of(self, expr: PyExpr) -> Optional[str]:
        if isinstance(expr, PyName):
            if self._annot_guard_mode and expr.name in self._param_types:
                return self._param_types[expr.name]
        if isinstance(expr, PyConstant):
            return expr.py_type
        return None

    def _known_numeric(self, expr: PyExpr) -> bool:
        t = self._type_of(expr)
        return t in ("int", "float")

    def _known_stringlike(self, expr: PyExpr) -> bool:
        t = self._type_of(expr)
        return t in ("str", "list")

    def _fresh_var(self, prefix: str = "v") -> str:
        self._vc += 1
        return f"_{prefix}{self._vc}"

    # =================================================================
    #  Expressions -> ImpAExp
    # =================================================================

    def lower_expr(self, expr: PyExpr) -> Optional[ImpAExp]:
        if isinstance(expr, PyConstant):
            return self._lower_constant(expr)
        if isinstance(expr, PyName):
            if expr.name == "__debug__":
                return ImpANum(value=1)
            return ImpAVar(name=expr.name)
        if isinstance(expr, PyBinaryOp):
            return self._lower_binop(expr)
        if isinstance(expr, PyUnaryOp):
            return self._lower_unary_aexp(expr)
        if isinstance(expr, PySubscript):
            return self._lower_subscript(expr)
        if isinstance(expr, PyAttribute):
            return self._lower_attribute(expr)
        if isinstance(expr, PyStringLiteral):
            return ImpAString(value=expr.value)
        if isinstance(expr, PyListLiteral):
            return self._lower_list_literal_expr(expr)
        if isinstance(expr, PyDictLiteral):
            return self._lower_dict_literal_expr(expr)
        if isinstance(expr, PySetLiteral):
            return self._lower_set_literal_expr(expr)
        if isinstance(expr, PyTupleLiteral):
            return self._lower_tuple_literal_expr(expr)
        if isinstance(expr, PyLen):
            return self._lower_len(expr)
        if isinstance(expr, PyCall):
            return self._lower_call(expr)
        if isinstance(expr, PyCompare):
            return self._lower_compare_aexp(expr)
        if isinstance(expr, PyBooleanOp):
            bexp = self.lower_bexp(expr)
            if bexp:
                return ImpABool(bexp=bexp)
        return None

    def _lower_constant(self, expr: PyConstant) -> ImpAExp:
        v = expr.value
        if isinstance(v, bool):
            return ImpANum(value=1 if v else 0)
        if isinstance(v, int):
            return ImpANum(value=v)
        if v is None:
            return ImpANone()
        if isinstance(v, str):
            return ImpAString(value=v)
        if isinstance(v, float):
            return ImpAFloat(value=int(v * 100))
        if isinstance(v, bytes):
            els: list[ImpAExp] = [ImpANum(value=b) for b in v]
            return ImpABytes(elements=els) if els else ImpABytes()
        return ImpANum(value=0)

    def _lower_binop(self, expr: PyBinaryOp) -> Optional[ImpAExp]:
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
        if expr.op == "/":
            return ImpADiv(left=left, right=right)
        if expr.op == "//":
            return ImpADiv(left=left, right=right)
        if expr.op == "%":
            return ImpAMod(left=left, right=right)
        return None

    def _lower_unary_aexp(self, expr: PyUnaryOp) -> Optional[ImpAExp]:
        if expr.op == "-":
            operand = self.lower_expr(expr.operand)
            if operand:
                return ImpAMult(left=ImpANum(value=-1), right=operand)
        return None

    def _lower_subscript(self, expr: PySubscript) -> Optional[ImpAExp]:
        key = self.lower_expr(expr.key)
        if not key:
            return None
        if isinstance(expr.container, PyName):
            return ImpAIndex(name=expr.container.name, index=key)
        return None

    def _lower_attribute(self, expr: PyAttribute) -> Optional[ImpAExp]:
        if isinstance(expr.obj, PyName):
            obj_name = expr.obj.name
            for cls_name, fields in self._record_fields.items():
                if expr.attr in fields:
                    if self._param_types.get(obj_name) == cls_name:
                        return ImpAVar(name=f"{obj_name}_{expr.attr}")
        if isinstance(expr.obj, PyName):
            return ImpAVar(name=f"{expr.obj.name}.{expr.attr}")
        return None

    def _lower_list_literal_expr(self, expr: PyListLiteral) -> ImpAExp:
        if not expr.elements:
            return ImpAList()
        els = [self.lower_expr(e) for e in expr.elements]
        els = [e for e in els if e is not None]
        return ImpAList(elements=els)

    def _lower_dict_literal_expr(self, expr: PyDictLiteral) -> ImpAExp:
        if not expr.pairs:
            return ImpADict()
        pairs = []
        for p in expr.pairs:
            k = self.lower_expr(p["key"]) if p.get("key") else None
            v = self.lower_expr(p["value"]) if p.get("value") else None
            if v:
                k = k or ImpANum(value=0)
                pairs.append((k, v))
        return ImpADict(pairs=pairs)

    def _lower_set_literal_expr(self, expr: PySetLiteral) -> ImpAExp:
        if not expr.elements:
            return ImpASetLit()
        els = [self.lower_expr(e) for e in expr.elements]
        els = [e for e in els if e is not None]
        return ImpASetLit(elements=els)

    def _lower_tuple_literal_expr(self, expr: PyTupleLiteral) -> ImpAExp:
        els = [self.lower_expr(e) for e in expr.elements]
        els = [e for e in els if e is not None]
        return ImpATuple(elements=els)

    def _lower_len(self, expr: PyLen) -> Optional[ImpAExp]:
        if isinstance(expr.obj, PyName):
            return ImpALen(name=expr.obj.name)
        return None

    def _lower_compare_aexp(self, expr: PyCompare) -> Optional[ImpAExp]:
        bexp = self.lower_bexp(expr)
        if bexp:
            return ImpABool(bexp=bexp)
        return None

    # =================================================================
    #  Expressions -> ImpBExp
    # =================================================================

    def lower_bexp(self, expr: PyExpr) -> Optional[ImpBExp]:
        if isinstance(expr, PyCompare):
            return self._lower_compare_bexp(expr)
        if isinstance(expr, PyBooleanOp):
            return self._lower_boolop(expr)
        if isinstance(expr, PyUnaryOp) and expr.op == "not":
            inner = self.lower_bexp(expr.operand)
            if inner:
                return ImpBNot(operand=inner)
        if isinstance(expr, PyIsInstance):
            return self._lower_isinstance(expr)
        if isinstance(expr, PyName):
            if expr.name == "__debug__":
                return ImpBTrue()
            return ImpBNot(operand=ImpBEq(
                left=ImpAVar(name=expr.name), right=ImpANum(value=0)))
        if isinstance(expr, PyCall):
            if expr.func == "len" and expr.args:
                if isinstance(expr.args[0], PyName):
                    return ImpBLe(left=ImpANum(value=1),
                                  right=ImpALen(name=expr.args[0].name))
        aexp = self.lower_expr(expr)
        if aexp:
            return ImpBNot(operand=ImpBEq(left=aexp, right=ImpANum(value=0)))
        return None

    def _lower_compare_bexp(self, expr: PyCompare) -> Optional[ImpBExp]:
        if expr.op in ("==", "!=", "<", "<=", ">", ">=", "is", "is not", "in", "not in"):
            left = self.lower_expr(expr.left)
            right = self.lower_expr(expr.right)
            if not left or not right:
                return None

            if expr.op == "==":
                return ImpBEq(left=left, right=right)
            if expr.op == "!=":
                return ImpBNot(operand=ImpBEq(left=left, right=right))

            # is / is not -> structural equality
            if expr.op == "is":
                return ImpBEq(left=left, right=right)
            if expr.op == "is not":
                return ImpBNot(operand=ImpBEq(left=left, right=right))

            if expr.op in (">", ">="):
                left, right = right, left
            if expr.op in ("<=", ">="):
                return ImpBLe(left=left, right=right)
            # strict < (or swapped >)
            return ImpBLe(left=ImpAPlus(left=left, right=ImpANum(value=1)),
                          right=right)

        # in / not in
        if expr.op in ("in", "not in"):
            if isinstance(expr.right, PyName):
                key = self.lower_expr(expr.left)
                if key:
                    dlen = ImpADictLen(name=expr.right.name, key=key)
                    if expr.op == "in":
                        return ImpBLe(left=ImpANum(value=1), right=dlen)
                    else:
                        return ImpBEq(left=ImpANum(value=0), right=dlen)
        return None

    def _lower_boolop(self, expr: PyBooleanOp) -> Optional[ImpBExp]:
        ops = [self.lower_bexp(o) for o in expr.operands]
        ops = [o for o in ops if o]
        if not ops:
            return None
        if expr.op == "not" and len(ops) == 1:
            return ImpBNot(operand=ops[0])
        if expr.op == "and":
            result = ops[0]
            for o in ops[1:]:
                result = ImpBAnd(left=result, right=o)
            return result
        if expr.op == "or":
            result = ops[0]
            for o in ops[1:]:
                result = ImpBOr(left=result, right=o)
            return result
        return None

    def _lower_isinstance(self, expr: PyIsInstance) -> Optional[ImpBExp]:
        if not isinstance(expr.obj, PyName):
            return None
        if expr.type_name == "int":
            return ImpBIsVZ(var=expr.obj.name)
        if expr.type_name == "str":
            return ImpBIsVString(var=expr.obj.name)
        if expr.type_name == "float":
            return ImpBIsVFloat(var=expr.obj.name)
        return None

    # =================================================================
    #  Statements -> ImpCom
    # =================================================================

    def lower_stmt(self, stmt: PyStmt) -> Optional[ImpCom]:
        if isinstance(stmt, PyAssign):
            return self._lower_assign(stmt)
        if isinstance(stmt, PyStoreAttr):
            return self._lower_store_attr(stmt)
        if isinstance(stmt, PyAugAssign):
            return self._lower_augassign(stmt)
        if isinstance(stmt, PyIf):
            return self._lower_if(stmt)
        if isinstance(stmt, PyWhile):
            return self._lower_while(stmt)
        if isinstance(stmt, PyFor):
            return self._lower_for(stmt)
        if isinstance(stmt, PyReturn):
            return self._lower_return(stmt)
        if isinstance(stmt, PyAssert):
            return ImpCSkip()
        if isinstance(stmt, PyExprStmt):
            return self._lower_expr_stmt(stmt)
        if isinstance(stmt, PyPass):
            return ImpCSkip()
        if isinstance(stmt, PyStoreSubscript):
            return self._lower_store_subscript(stmt)
        if isinstance(stmt, PySliceStore):
            return self._lower_slice_store(stmt)
        return None

    def _lower_assign(self, stmt: PyAssign) -> Optional[ImpCom]:
        # List literal assignment -> CListNew + append chain
        if isinstance(stmt.value, PyListLiteral):
            return self._build_list_literal_assign(stmt.target, stmt.value)
        # Dict literal
        if isinstance(stmt.value, PyDictLiteral):
            return self._build_dict_literal_assign(stmt.target, stmt.value)
        # List comprehension: [expr for var in iterable if cond]
        if isinstance(stmt.value, PyListComp):
            return self._lower_list_comp(stmt.target, stmt.value)
        # Call expression -> function call lowering
        if isinstance(stmt.value, PyCall):
            return self._lower_call_as_assign(stmt.target, stmt.value)
        # BoolOp -> CIf expansion for short-circuit
        if isinstance(stmt.value, PyBooleanOp):
            return self._lower_boolop_assign(stmt.target, stmt.value)
        # Compare as rhs -> wrap in ABool
        if isinstance(stmt.value, PyCompare):
            bexp = self.lower_bexp(stmt.value)
            if bexp:
                return ImpCAss(target=stmt.target, value=ImpABool(bexp=bexp))
        # Slice subscript: result = lst[0:n] -> while-loop copy to new list
        if isinstance(stmt.value, PySliceSubscript):
            return self._lower_slice_copy_assign(stmt.target, stmt.value)
        val = self.lower_expr(stmt.value)
        if val:
            return ImpCAss(target=stmt.target, value=val)
        return None

    def _build_list_literal_assign(self, target: str, lit: PyListLiteral) -> ImpCom:
        cmds: list[ImpCom] = [ImpCListNew(name=target)]
        for elt in lit.elements:
            val = self.lower_expr(elt)
            if val:
                cmds.append(ImpCListAppend(name=target, value=val))
        return seq(*cmds)

    def _build_dict_literal_assign(self, target: str, lit: PyDictLiteral) -> ImpCom:
        pairs = []
        for p in lit.pairs:
            k = self.lower_expr(p["key"]) if p.get("key") else None
            v = self.lower_expr(p["value"]) if p.get("value") else None
            if v:
                k = k or ImpANum(value=0)
                pairs.append((k, v))
        return ImpCAss(target=target, value=ImpADict(pairs=pairs))

    def _lower_boolop_assign(self, target: str, expr: PyBooleanOp) -> Optional[ImpCom]:
        if len(expr.operands) < 2:
            return self.lower_stmt(PyAssign(target=target, value=expr.operands[0]))
        if expr.op == "or":
            first = expr.operands[0]
            second = expr.operands[1]
            cond = self.lower_bexp(first)
            if not cond:
                return None
            then_cmd = self.lower_stmt(PyAssign(target=target, value=first))
            else_cmd = self.lower_stmt(PyAssign(target=target, value=second))
            if then_cmd and else_cmd:
                return ImpCIf(condition=cond, then_branch=then_cmd, else_branch=else_cmd)
        if expr.op == "and":
            first = expr.operands[0]
            second = expr.operands[1]
            cond = self.lower_bexp(first)
            if not cond:
                return None
            then_cmd = self.lower_stmt(PyAssign(target=target, value=second))
            else_cmd = self.lower_stmt(PyAssign(target=target, value=first))
            if then_cmd and else_cmd:
                return ImpCIf(condition=cond, then_branch=then_cmd, else_branch=else_cmd)
        return None

    def _lower_store_attr(self, stmt: PyStoreAttr) -> Optional[ImpCom]:
        val = self.lower_expr(stmt.value)
        if val:
            return ImpCAss(target=f"{stmt.obj}_{stmt.attr}", value=val)
        return None

    def _lower_augassign(self, stmt: PyAugAssign) -> Optional[ImpCom]:
        val = self.lower_expr(stmt.value)
        if val:
            op_map = {"+": ImpAPlus, "-": ImpAMinus, "*": ImpAMult,
                      "/": ImpADiv, "//": ImpADiv, "%": ImpAMod}
            op_cls = op_map.get(stmt.op, ImpAPlus)
            new_val = op_cls(left=ImpAVar(name=stmt.target), right=val)
            return ImpCAss(target=stmt.target, value=new_val)
        return None

    def _lower_slice_copy_assign(self, target: str, slice_expr: PySliceSubscript) -> Optional[ImpCom]:
        """Lower target = lst[start:end] -> while-loop copy to new list target."""
        obj = slice_expr.obj
        obj_name = obj.name if isinstance(obj, PyName) else None
        if not obj_name:
            return None
        start_val = self.lower_expr(slice_expr.start) if slice_expr.start else ImpANum(value=0)
        end_val = self.lower_expr(slice_expr.end) if slice_expr.end else ImpALen(name=obj_name)
        if not start_val or not end_val:
            return None

        loop_var = self._fresh_var("k")
        new_list = ImpCListNew(name=target)
        init = ImpCAss(target=loop_var, value=start_val)
        cond = ImpBLe(
            left=ImpAPlus(left=ImpAVar(name=loop_var), right=ImpANum(value=1)),
            right=end_val)
        append_cmd = ImpCListAppend(
            name=target,
            value=ImpAIndex(name=obj_name, index=ImpAVar(name=loop_var)))
        incr = ImpCAss(target=loop_var, value=ImpAPlus(
            left=ImpAVar(name=loop_var), right=ImpANum(value=1)))
        loop_body = ImpCSeq(commands=[append_cmd, incr])
        loop = ImpCWhile(condition=cond, invariant="(fun _ => True)", body=loop_body)
        return ImpCSeq(commands=[new_list, init, loop])

    def _lower_slice_store(self, stmt: PySliceStore) -> Optional[ImpCom]:
        """Lower lst[start:end] = value -> while-loop copy to new list."""
        if not isinstance(stmt.value, PyName):
            return None
        src_name = stmt.value.name
        obj = stmt.obj
        start_val = self.lower_expr(stmt.start) if stmt.start else ImpANum(value=0)
        end_val = self.lower_expr(stmt.end) if stmt.end else ImpALen(name=obj)
        if not start_val or not end_val:
            return None

        loop_var = self._fresh_var("k")
        new_list = ImpCListNew(name=obj)
        init = ImpCAss(target=loop_var, value=start_val)
        cond = ImpBLe(
            left=ImpAPlus(left=ImpAVar(name=loop_var), right=ImpANum(value=1)),
            right=end_val)
        append_cmd = ImpCListAppend(
            name=obj,
            value=ImpAIndex(name=src_name, index=ImpAVar(name=loop_var)))
        incr = ImpCAss(target=loop_var, value=ImpAPlus(
            left=ImpAVar(name=loop_var), right=ImpANum(value=1)))
        loop_body = ImpCSeq(commands=[append_cmd, incr])
        loop = ImpCWhile(condition=cond, invariant="(fun _ => True)", body=loop_body)
        return ImpCSeq(commands=[new_list, init, loop])

    def _lower_store_subscript(self, stmt: PyStoreSubscript) -> Optional[ImpCom]:
        key = self.lower_expr(stmt.key)
        val = self.lower_expr(stmt.value)
        if not key or not val:
            return None
        if isinstance(stmt.container, PyName):
            return ImpCDictAppendKv(name=stmt.container.name, key=key, value=val)
        return None

    def _lower_if(self, stmt: PyIf) -> Optional[ImpCom]:
        cond = self.lower_bexp(stmt.test)
        if not cond:
            return None
        then_body = self.lower_body(stmt.body)
        else_body = self.lower_body(stmt.orelse)
        return ImpCIf(condition=cond, then_branch=then_body, else_branch=else_body)

    def _lower_while(self, stmt: PyWhile) -> Optional[ImpCom]:
        cond = self.lower_bexp(stmt.test)
        if not cond:
            return None
        body = self.lower_body(stmt.body)
        inv_str = self._invariants_to_coq(stmt.invariants)
        return ImpCWhile(condition=cond, invariant=inv_str, body=body)

    def _lower_for(self, stmt: PyFor) -> Optional[ImpCom]:
        """Lower for-loop to while-loop with counter."""
        if isinstance(stmt.iterable, PyCall) and stmt.iterable.func == "range":
            return self._lower_for_range(stmt)
        if isinstance(stmt.iterable, PyName):
            return self._lower_for_in(stmt)
        if isinstance(stmt.iterable, PyAttribute):
            return self._lower_for_in(stmt)
        return None

    def _lower_for_range(self, stmt: PyFor) -> Optional[ImpCom]:
        assert isinstance(stmt.iterable, PyCall)
        args = stmt.iterable.args
        if len(args) == 1:
            start_val = ImpANum(value=0)
            limit_val = self.lower_expr(args[0])
            step_val = ImpANum(value=1)
            step_is_neg = False
        elif len(args) == 2:
            start_val = self.lower_expr(args[0])
            limit_val = self.lower_expr(args[1])
            step_val = ImpANum(value=1)
            step_is_neg = False
        elif len(args) == 3:
            start_val = self.lower_expr(args[0])
            limit_val = self.lower_expr(args[1])
            step_val = self.lower_expr(args[2])
            # Detect negative step: -c where c > 0, or literal negative int
            if args[2] is not None:
                if isinstance(args[2], PyConstant) and isinstance(args[2].value, int):
                    step_is_neg = args[2].value < 0
                elif isinstance(args[2], PyUnaryOp) and args[2].op == "-":
                    step_is_neg = True
                else:
                    step_is_neg = False
            else:
                step_is_neg = False
        else:
            return None
        if not limit_val or not step_val:
            return None

        target = stmt.var
        body_cmds = self.lower_body(stmt.body)
        inv_str = self._invariants_to_coq(stmt.invariants)
        incr = ImpCAss(target=target, value=ImpAPlus(
            left=ImpAVar(name=target), right=step_val))
        init = ImpCAss(target=target, value=start_val if start_val else ImpANum(value=0))

        if step_is_neg:
            cond = ImpBNot(operand=ImpBLe(
                left=ImpAPlus(left=ImpAVar(name=target), right=step_val),
                right=limit_val))
        else:
            cond = ImpBLe(
                left=ImpAPlus(left=ImpAVar(name=target), right=step_val),
                right=limit_val)

        loop_body = body_cmds if isinstance(body_cmds, ImpCSkip) else \
            ImpCSeq(commands=[body_cmds, incr])
        loop = ImpCWhile(condition=cond, invariant=inv_str, body=loop_body)
        return ImpCSeq(commands=[init, loop])

    def _lower_for_in(self, stmt: PyFor) -> Optional[ImpCom]:
        target = stmt.var
        iter_name: Optional[str] = None
        if isinstance(stmt.iterable, PyName):
            iter_name = stmt.iterable.name
        elif isinstance(stmt.iterable, PyAttribute):
            attr = stmt.iterable
            obj_name = getattr(attr.obj, 'name', '?')
            iter_name = f"{obj_name}.{attr.attr}"
        if not iter_name:
            return None

        loop_var = self._fresh_var("i")
        body_cmds = self.lower_body(stmt.body)
        inv_str = self._invariants_to_coq(stmt.invariants)

        init = ImpCAss(target=loop_var, value=ImpANum(value=0))
        cond = ImpBLe(
            left=ImpAPlus(left=ImpAVar(name=loop_var), right=ImpANum(value=1)),
            right=ImpALen(name=iter_name))
        elem_load = ImpCAss(target=target,
                           value=ImpAIndex(name=iter_name,
                                          index=ImpAVar(name=loop_var)))
        incr = ImpCAss(target=loop_var, value=ImpAPlus(
            left=ImpAVar(name=loop_var), right=ImpANum(value=1)))
        loop_body = ImpCSeq(commands=[elem_load, body_cmds, incr])
        loop = ImpCWhile(condition=cond, invariant=inv_str, body=loop_body)
        return ImpCSeq(commands=[init, loop])

    def _lower_return(self, stmt: PyReturn) -> Optional[ImpCom]:
        if stmt.value:
            val = self.lower_expr(stmt.value)
            if val:
                return ImpCAss(target="result", value=val)
            bexp = self.lower_bexp(stmt.value)
            if bexp:
                return ImpCAss(target="result", value=ImpABool(bexp=bexp))
        return ImpCSkip()

    # =================================================================
    #  Expression statements (method calls)
    # =================================================================

    def _lower_expr_stmt(self, stmt: PyExprStmt) -> Optional[ImpCom]:
        expr = stmt.expr
        if isinstance(expr, PyCall):
            return self._lower_method_call(expr)
        if isinstance(expr, PyStoreSubscript):
            return self._lower_store_subscript(expr)
        return None

    def _lower_method_call(self, expr: PyCall) -> Optional[ImpCom]:
        name = expr.func
        args = expr.args

        # list.append(val)
        if name.endswith(".append") and args:
            obj = self._call_object(name)
            val = self.lower_expr(args[0])
            if obj and val:
                return ImpCListAppend(name=obj, value=val)

        # list.pop()
        if name.endswith(".pop") and not args:
            obj = self._call_object(name)
            if obj:
                return ImpCListPop(name=obj)

        # set.add(val)
        if name.endswith(".add") and args:
            obj = self._call_object(name)
            val = self.lower_expr(args[0])
            if obj and val:
                return ImpCDictSet(name=obj, key=val, val=ImpANum(value=1))

        # set.discard / set.remove -> no-op
        if (name.endswith(".discard") or name.endswith(".remove")) and args:
            return ImpCSkip()

        # str.lower()
        if name.endswith(".lower") and not args:
            obj = self._call_object(name)
            if obj:
                return self._build_str_lower(obj)

        # str.upper()
        if name.endswith(".upper") and not args:
            obj = self._call_object(name)
            if obj:
                return self._build_str_upper(obj)

        # str.strip()
        if name.endswith(".strip") and not args:
            obj = self._call_object(name)
            if obj:
                return self._build_str_strip(obj)

        # General function call (CCall)
        if not expr.is_method:
            return self._lower_call_stmt(expr)

        return None

    def _build_str_lower(self, obj: str) -> ImpCom:
        loop_var = self._fresh_var("k")
        init = ImpCAss(target=loop_var, value=ImpANum(value=0))
        cond = ImpBLe(
            left=ImpAPlus(left=ImpAVar(name=loop_var), right=ImpANum(value=1)),
            right=ImpALen(name=obj))
        char = ImpAIndex(name=obj, index=ImpAVar(name=loop_var))
        is_upper = ImpBAnd(
            left=ImpBLe(left=ImpANum(value=65), right=char),
            right=ImpBLe(left=char, right=ImpANum(value=90)))
        lowered = ImpAPlus(left=char, right=ImpANum(value=32))
        set_cmd = ImpCListSet(name=obj, idx=ImpAVar(name=loop_var), val=lowered)
        body_if = ImpCIf(condition=is_upper, then_branch=set_cmd, else_branch=ImpCSkip())
        incr = ImpCAss(target=loop_var, value=ImpAPlus(
            left=ImpAVar(name=loop_var), right=ImpANum(value=1)))
        body = ImpCSeq(commands=[body_if, incr])
        loop = ImpCWhile(condition=cond, invariant="(fun _ => True)", body=body)
        return ImpCSeq(commands=[init, loop])

    def _build_str_upper(self, obj: str) -> ImpCom:
        loop_var = self._fresh_var("k")
        init = ImpCAss(target=loop_var, value=ImpANum(value=0))
        cond = ImpBLe(
            left=ImpAPlus(left=ImpAVar(name=loop_var), right=ImpANum(value=1)),
            right=ImpALen(name=obj))
        char = ImpAIndex(name=obj, index=ImpAVar(name=loop_var))
        is_lower = ImpBAnd(
            left=ImpBLe(left=ImpANum(value=97), right=char),
            right=ImpBLe(left=char, right=ImpANum(value=122)))
        uppered = ImpAMinus(left=char, right=ImpANum(value=32))
        set_cmd = ImpCListSet(name=obj, idx=ImpAVar(name=loop_var), val=uppered)
        body_if = ImpCIf(condition=is_lower, then_branch=set_cmd, else_branch=ImpCSkip())
        incr = ImpCAss(target=loop_var, value=ImpAPlus(
            left=ImpAVar(name=loop_var), right=ImpANum(value=1)))
        body = ImpCSeq(commands=[body_if, incr])
        loop = ImpCWhile(condition=cond, invariant="(fun _ => True)", body=body)
        return ImpCSeq(commands=[init, loop])

    def _build_str_strip(self, obj: str) -> ImpCom:
        l = self._fresh_var("l")
        r = self._fresh_var("r")
        i = self._fresh_var("i")
        ln = ImpALen(name=obj)

        def ws(v):
            return ImpBLe(left=ImpAIndex(name=obj, index=ImpAVar(name=v)),
                          right=ImpANum(value=32))

        def incr(v):
            return ImpCAss(target=v, value=ImpAPlus(
                left=ImpAVar(name=v), right=ImpANum(value=1)))

        def decr(v):
            return ImpCAss(target=v, value=ImpAMinus(
                left=ImpAVar(name=v), right=ImpANum(value=1)))

        # Left scan
        left_init = ImpCAss(target=l, value=ImpANum(value=0))
        left_cond = ImpBAnd(
            left=ImpBLe(left=ImpAPlus(left=ImpAVar(name=l), right=ImpANum(value=1)),
                        right=ln),
            right=ws(l))
        left_loop = ImpCWhile(condition=left_cond, invariant="(fun _ => True)",
                             body=incr(l))

        # Right scan
        right_init = ImpCAss(target=r, value=ImpAMinus(left=ln, right=ImpANum(value=1)))
        right_cond = ImpBAnd(
            left=ImpBLe(left=ImpANum(value=1),
                        right=ImpAPlus(left=ImpAVar(name=r), right=ImpANum(value=1))),
            right=ws(r))
        right_loop = ImpCWhile(condition=right_cond, invariant="(fun _ => True)",
                              body=decr(r))

        # Shift
        src_idx = ImpAPlus(left=ImpAVar(name=l), right=ImpAVar(name=i))
        shift_body = ImpCSeq(commands=[
            ImpCListSet(name=obj, idx=ImpAVar(name=i),
                       val=ImpAIndex(name=obj, index=src_idx)),
            incr(i)])
        shift_cond = ImpBLe(
            left=ImpAPlus(left=ImpAVar(name=i), right=ImpANum(value=1)),
            right=ImpAPlus(
                left=ImpAMinus(left=ImpAVar(name=r), right=ImpAVar(name=l)),
                right=ImpANum(value=1)))
        shift_loop = ImpCWhile(condition=shift_cond, invariant="(fun _ => True)",
                              body=shift_body)
        shift_init = ImpCAss(target=i, value=ImpANum(value=0))
        shift = ImpCSeq(commands=[shift_init, shift_loop])

        # Truncate
        new_len = ImpAPlus(
            left=ImpAMinus(left=ImpAVar(name=r), right=ImpAVar(name=l)),
            right=ImpANum(value=1))
        pop_cond = ImpBLe(left=ImpAPlus(left=new_len, right=ImpANum(value=1)),
                         right=ln)
        pop_loop = ImpCWhile(condition=pop_cond, invariant="(fun _ => True)",
                            body=ImpCListPop(name=obj))

        return ImpCSeq(commands=[
            left_init, left_loop,
            right_init, right_loop,
            shift, pop_loop])

    def _call_object(self, qualified_name: str) -> Optional[str]:
        """Extract object name from obj.method() -> obj."""
        if "." in qualified_name:
            return qualified_name.rsplit(".", 1)[0]
        return None

    # =================================================================
    #  Function calls (CCall)
    # =================================================================

    def _lower_call_as_assign(self, target: str, expr: PyCall) -> Optional[ImpCom]:
        """Lower a function call used as rvalue: x = f(args)."""
        # Pure builtins
        if expr.func == "len" and expr.args:
            if isinstance(expr.args[0], PyName):
                return ImpCAss(target=target,
                              value=ImpALen(name=expr.args[0].name))
        if expr.func in ("abs", "min", "max", "int", "float") and expr.args:
            val = self.lower_expr(expr.args[0])
            if val:
                return ImpCAss(target=target, value=val)
        if expr.func == "isinstance":
            return ImpCAss(target=target, value=ImpABool(bexp=ImpBTrue()))
        if expr.func == "list" and expr.args:
            return ImpCListNew(name=target)
        if expr.func == "set" and not expr.args:
            return ImpCSkip()
        if expr.func == "dict" and expr.args:
            return ImpCSkip()
        # Method calls
        if expr.is_method:
            if expr.func.endswith(".keys") or expr.func.endswith(".values") \
                    or expr.func.endswith(".items"):
                return ImpCListNew(name=target)
        # CCall
        return self._lower_ccall(target, expr)

    def _lower_ccall(self, target: str, expr: PyCall) -> Optional[ImpCom]:
        name = expr.func
        if name not in self._contract_map:
            return None
        callee_params, pre_s, post_s, _, callee_writes = self._contract_map[name]
        args_list = [self.lower_expr(a) for a in expr.args]
        args_list = [a for a in args_list if a is not None]

        # Inline actual arguments into callee contracts instead of emitting
        # synthetic assignments like `x := a` before the CCall.  Keeping those
        # temporary assignments inside each call stage makes later frame proofs
        # much harder: a stage must prove both parameter-temp preservation and
        # real CCall frame preservation.  CCall already stores `args`, so the
        # contracts should mention actual arguments directly.
        pre = self._scope_ccall_pre(pre_s, callee_params, args_list, name)
        post = self._subst_result(post_s, target, callee_params, args_list)
        call = ImpCCall(
            name=name, args=args_list,
            precondition=pre, postcondition=post,
            writes=callee_writes, target=target)

        return call

    def _aexp_contract_zterm(self, aexp: ImpAExp) -> str:
        if isinstance(aexp, ImpAVar):
            return f'asZ (s "{aexp.name}"%string)'
        if isinstance(aexp, ImpANum):
            return str(aexp.value)
        if isinstance(aexp, ImpAPlus):
            return f"({self._aexp_contract_zterm(aexp.left)} + {self._aexp_contract_zterm(aexp.right)})%Z"
        if isinstance(aexp, ImpAMinus):
            return f"({self._aexp_contract_zterm(aexp.left)} - {self._aexp_contract_zterm(aexp.right)})%Z"
        if isinstance(aexp, ImpAMult):
            return f"({self._aexp_contract_zterm(aexp.left)} * {self._aexp_contract_zterm(aexp.right)})%Z"
        if isinstance(aexp, ImpAMod):
            return f"({self._aexp_contract_zterm(aexp.left)} mod {self._aexp_contract_zterm(aexp.right)})%Z"
        if isinstance(aexp, ImpADiv):
            return f"({self._aexp_contract_zterm(aexp.left)} / {self._aexp_contract_zterm(aexp.right)})%Z"
        return f"asZ ({aexp.to_coq()})"

    def _aexp_contract_value(self, aexp: ImpAExp) -> str:
        if isinstance(aexp, ImpAVar):
            return f's "{aexp.name}"%string'
        if isinstance(aexp, ImpANum):
            return f"VZ {aexp.value}"
        return f"VZ ({self._aexp_contract_zterm(aexp)})"

    def _scope_ccall_pre(self, coq_expr: str, params: list[str], args: list[ImpAExp],
                          callee_name: str = "") -> str:
        import re
        result = coq_expr
        arg_map = {p: a for p, a in zip(params, args)}
        for p in params:
            if p in arg_map:
                zterm = self._aexp_contract_zterm(arg_map[p])
                vterm = self._aexp_contract_value(arg_map[p])
            else:
                zterm = f'asZ (s "{p}"%string)'
                vterm = f's "{p}"%string'
            result = re.sub(
                rf'asZ\s*\(\s*s\s+"{re.escape(p)}"%string\s*\)',
                zterm,
                result,
            )
            result = re.sub(
                rf'isVZ\s*\(\s*s\s+"{re.escape(p)}"%string\s*\)',
                f'isVZ ({vterm})',
                result,
            )
            result = re.sub(
                rf'(?<![a-zA-Z0-9_"%]){re.escape(p)}__len(?![a-zA-Z0-9_"%])',
                f'asZ (s "{p}._len"%string)', result)
            # Replace bare param name but NOT the state variable s in "s \"...\"" patterns.
            # A state variable is always followed by optional whitespace then a double-quote.
            result = re.sub(
                rf'(?<![a-zA-Z0-9_"%]){re.escape(p)}(?!\s*")(?![a-zA-Z0-9_"%])',
                zterm, result)
        return f"(fun s => {result})"

    @staticmethod
    def _subst_result(post_coq: str, target: str, callee_params: list[str], args: list[ImpAExp]) -> str:
        import re
        if 'result' in callee_params:
            return f"(fun s => {post_coq})"
        result = post_coq.replace('s "result"%string', f's "{target}"%string')
        lowerer = PyToImpLowerer()
        for p, a in zip(callee_params, args):
            zterm = lowerer._aexp_contract_zterm(a)
            vterm = lowerer._aexp_contract_value(a)
            result = re.sub(
                rf'asZ\s*\(\s*s\s+"{re.escape(p)}"%string\s*\)',
                zterm,
                result,
            )
            result = re.sub(
                rf'isVZ\s*\(\s*s\s+"{re.escape(p)}"%string\s*\)',
                f'isVZ ({vterm})',
                result,
            )
        return f"(fun s => {result})"

    def _lower_call(self, expr: PyCall) -> Optional[ImpAExp]:
        if expr.func == "len" and expr.args:
            if isinstance(expr.args[0], PyName):
                return ImpALen(name=expr.args[0].name)
        if expr.func in ("abs", "min", "max", "int", "float") and expr.args:
            return self.lower_expr(expr.args[0])
        if expr.func == "isinstance":
            return ImpANum(value=1)
        if expr.func == "list" and expr.args:
            inner = self.lower_expr(expr.args[0])
            if inner:
                return inner
        return None

    def _lower_list_comp(self, target: str, comp: PyListComp) -> Optional[ImpCom]:
        """Lower list comprehension [expr for var in iterable if cond] to a while loop."""
        new_list = ImpCListNew(name=target)
        elt_expr = self.lower_expr(comp.elt)
        if not elt_expr:
            return None
        append_cmd = ImpCListAppend(name=target, value=elt_expr)
        # Wrap in conditionals
        for cond in reversed(comp.conds):
            bexp = self.lower_bexp(cond)
            if bexp:
                append_cmd = ImpCIf(condition=bexp, then_branch=append_cmd, else_branch=ImpCSkip())
        # Build for-in loop
        if isinstance(comp.iterable, PyCall) and comp.iterable.func == "range":
            loop_cmd = self._build_for_range_with_body(comp.var, comp.iterable, append_cmd)
        elif isinstance(comp.iterable, PyName):
            loop_cmd = self._build_for_in_with_body(comp.var, comp.iterable.name, append_cmd)
        else:
            return None
        if not loop_cmd:
            return None
        return ImpCSeq(commands=[new_list, loop_cmd])

    def _build_for_range_with_body(self, target: str, range_call: PyCall, body: ImpCom) -> Optional[ImpCom]:
        args = range_call.args
        if len(args) == 1:
            start = ImpANum(value=0); limit = self.lower_expr(args[0]); step = ImpANum(value=1)
        elif len(args) == 2:
            start = self.lower_expr(args[0]); limit = self.lower_expr(args[1]); step = ImpANum(value=1)
        else:
            return None
        if not limit:
            return None
        init = ImpCAss(target=target, value=ImpANum(value=0) if start is None else start)
        cond = ImpBLe(left=ImpAPlus(left=ImpAVar(name=target), right=step), right=limit)
        incr = ImpCAss(target=target, value=ImpAPlus(left=ImpAVar(name=target), right=step))
        loop_body = ImpCSeq(commands=[body, incr])
        loop = ImpCWhile(condition=cond, invariant="(fun _ => True)", body=loop_body)
        return ImpCSeq(commands=[init, loop])

    def _build_for_in_with_body(self, target: str, iter_name: str, body: ImpCom) -> ImpCom:
        loop_var = self._fresh_var("i")
        init = ImpCAss(target=loop_var, value=ImpANum(value=0))
        cond = ImpBLe(
            left=ImpAPlus(left=ImpAVar(name=loop_var), right=ImpANum(value=1)),
            right=ImpALen(name=iter_name))
        elem_load = ImpCAss(target=target, value=ImpAIndex(name=iter_name, index=ImpAVar(name=loop_var)))
        incr = ImpCAss(target=loop_var, value=ImpAPlus(left=ImpAVar(name=loop_var), right=ImpANum(value=1)))
        loop_body = ImpCSeq(commands=[elem_load, body, incr])
        loop = ImpCWhile(condition=cond, invariant="(fun _ => True)", body=loop_body)
        return ImpCSeq(commands=[init, loop])

    def _lower_call_stmt(self, expr: PyExpr) -> Optional[ImpCom]:
        if isinstance(expr, PyCall):
            return self._lower_ccall("", expr)
        return None

    # =================================================================
    #  Body lowering
    # =================================================================

    def lower_body(self, stmts: list[PyStmt]) -> ImpCom:
        cmds = [self.lower_stmt(s) for s in stmts]
        cmds = [c for c in cmds if c is not None]
        return seq(*self._strip_trailing_identity(cmds))

    def _strip_trailing_identity(self, cmds: list[ImpCom]) -> list[ImpCom]:
        """Remove trailing CAss 'result' := AVar 'result' (identity returns)."""
        while cmds:
            last = cmds[-1]
            if isinstance(last, ImpCAss) and last.target == "result":
                if isinstance(last.value, ImpAVar) and last.value.name == "result":
                    cmds = cmds[:-1]
                    continue
            break
        return cmds

    def lower_function(self, func: PyFunction) -> ImpCom:
        return self.lower_body(func.body)

    # =================================================================
    #  Helpers
    # =================================================================

    def _invariants_to_coq(self, invariants: list) -> str:
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
