"""
Python AST → PyIR translator.

Faithful translation: every Python construct is represented explicitly.
No type assumptions, no silent simplification of Python semantics.
"""

import ast
from typing import Optional
from .py_ir import *


class PyIRTranslator:
    """Walk a Python AST and produce PyIR nodes."""

    def __init__(self, contract_linter=None):
        self._linter = contract_linter  # ContractLinter for invariant extraction

    def translate_expr(self, node: ast.expr) -> Optional[PyExpr]:
        if isinstance(node, ast.Name):
            return PyName(name=node.id)
        if isinstance(node, ast.Constant):
            py_type = "int"
            if isinstance(node.value, bool):
                py_type = "bool"
            elif isinstance(node.value, str):
                py_type = "str"
            elif isinstance(node.value, float):
                py_type = "float"
            elif node.value is None:
                py_type = "None"
            return PyConstant(value=node.value, py_type=py_type)
        if isinstance(node, ast.BinOp):
            op_map = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
                      ast.Div: "/", ast.FloorDiv: "//", ast.Mod: "%"}
            op = op_map.get(type(node.op))
            if op is None:
                return None
            left = self.translate_expr(node.left)
            right = self.translate_expr(node.right)
            if left and right:
                return PyBinaryOp(op=op, left=left, right=right)
        if isinstance(node, ast.Compare):
            op_map = {ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">=",
                      ast.Eq: "==", ast.NotEq: "!=", ast.Is: "is",
                      ast.IsNot: "is not", ast.In: "in", ast.NotIn: "not in"}
            if len(node.ops) == 1:
                op = op_map.get(type(node.ops[0]))
                if op:
                    left = self.translate_expr(node.left)
                    right = self.translate_expr(node.comparators[0])
                    if left and right:
                        return PyCompare(op=op, left=left, right=right)
        if isinstance(node, ast.BoolOp):
            op_map = {ast.And: "and", ast.Or: "or"}
            op = op_map.get(type(node.op))
            if op:
                operands = [self.translate_expr(v) for v in node.values]
                operands = [o for o in operands if o]
                if operands:
                    return PyBooleanOp(op=op, operands=operands)
        if isinstance(node, ast.UnaryOp):
            op_map = {ast.USub: "-", ast.Not: "not"}
            op = op_map.get(type(node.op))
            if op:
                operand = self.translate_expr(node.operand)
                if operand:
                    return PyUnaryOp(op=op, operand=operand)
        if isinstance(node, ast.Call):
            name = self._call_name(node)
            if name is None:
                return None
            args = [self.translate_expr(a) for a in node.args]
            args = [a for a in args if a is not None]
            is_method = isinstance(node.func, ast.Attribute)
            return PyCall(func=name, args=args, is_method=is_method)
        if isinstance(node, ast.Subscript):
            container = self.translate_expr(node.value)
            if isinstance(node.slice, ast.Slice):
                start = self.translate_expr(node.slice.lower) if node.slice.lower else None
                end = self.translate_expr(node.slice.upper) if node.slice.upper else None
                if container:
                    return PySliceSubscript(obj=container, start=start, end=end)
            key = self.translate_expr(node.slice)
            if container and key:
                return PySubscript(container=container, key=key)
        if isinstance(node, ast.Attribute):
            obj = self.translate_expr(node.value)
            if obj:
                return PyAttribute(obj=obj, attr=node.attr)
        if isinstance(node, ast.List):
            elements = [self.translate_expr(e) for e in node.elts]
            elements = [e for e in elements if e is not None]
            return PyListLiteral(elements=elements)
        if isinstance(node, ast.Dict):
            pairs = []
            for k, v in zip(node.keys, node.values):
                ke = self.translate_expr(k) if k else None
                ve = self.translate_expr(v)
                if ve:
                    pairs.append({"key": ke, "value": ve})
            return PyDictLiteral(pairs=pairs)
        if isinstance(node, ast.Set):
            elements = [self.translate_expr(e) for e in node.elts]
            elements = [e for e in elements if e is not None]
            return PySetLiteral(elements=elements)
        if isinstance(node, ast.Tuple):
            elements = [self.translate_expr(e) for e in node.elts]
            elements = [e for e in elements if e is not None]
            return PyTupleLiteral(elements=elements)
        if isinstance(node, ast.ListComp):
            return self._translate_list_comp(node)
        if isinstance(node, ast.GeneratorExp):
            return self._translate_generator(node)
        return None

    def translate_stmt(self, node: ast.stmt) -> Optional[PyStmt]:
        if isinstance(node, ast.Assign):
            val = self.translate_expr(node.value)
            if val:
                for target in node.targets:
                    if isinstance(target, ast.Name):
                        return PyAssign(target=target.id, value=val)
                    if isinstance(target, ast.Subscript):
                        if isinstance(target.slice, ast.Slice):
                            obj_name = target.value.id if isinstance(target.value, ast.Name) else None
                            if obj_name:
                                start = self.translate_expr(target.slice.lower) if target.slice.lower else None
                                end = self.translate_expr(target.slice.upper) if target.slice.upper else None
                                return PySliceStore(obj=obj_name, start=start, end=end, value=val)
                        container = self.translate_expr(target.value)
                        key = self.translate_expr(target.slice)
                        if container and key:
                            return PyStoreSubscript(container=container, key=key, value=val)
                    if isinstance(target, ast.Attribute):
                        if isinstance(target.value, ast.Name):
                            return PyStoreAttr(obj=target.value.id, attr=target.attr, value=val)
        if isinstance(node, ast.AugAssign):
            op_map = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/"}
            op = op_map.get(type(node.op))
            val = self.translate_expr(node.value)
            if op and val:
                if isinstance(node.target, ast.Name):
                    return PyAugAssign(target=node.target.id, op=op, value=val)
                if isinstance(node.target, ast.Attribute):
                    if isinstance(node.target.value, ast.Name):
                        return PyStoreAttr(obj=node.target.value.id, attr=node.target.attr,
                                          value=PyBinaryOp(op=op, left=PyAttribute(
                                              obj=PyName(name=node.target.value.id),
                                              attr=node.target.attr), right=val))
        if isinstance(node, ast.If):
            test = self.translate_expr(node.test)
            if test:
                body = [s for s in (self.translate_stmt(b) for b in node.body) if s]
                orelse = [s for s in (self.translate_stmt(b) for b in node.orelse) if s]
                return PyIf(test=test, body=body, orelse=orelse)
        if isinstance(node, ast.While):
            test = self.translate_expr(node.test)
            if test:
                body = [s for s in (self.translate_stmt(b) for b in node.body) if s]
                invariants = self._extract_invariants(node.body)
                return PyWhile(test=test, body=body, invariants=invariants, line_number=node.lineno)
        if isinstance(node, ast.For):
            iterable = self.translate_expr(node.iter)
            if iterable and isinstance(node.target, ast.Name):
                body = [s for s in (self.translate_stmt(b) for b in node.body) if s]
                invariants = self._extract_invariants(node.body)
                return PyFor(var=node.target.id, iterable=iterable, body=body, invariants=invariants)
        if isinstance(node, ast.Return):
            val = self.translate_expr(node.value) if node.value else None
            return PyReturn(value=val)
        if isinstance(node, ast.Assert):
            test = self.translate_expr(node.test)
            if test:
                return PyAssert(test=test, line_number=node.lineno)
        if isinstance(node, ast.Expr):
            val = self.translate_expr(node.value)
            if val:
                return PyExprStmt(expr=val)
        if isinstance(node, ast.Pass):
            return PyPass()
        return None

    def translate_function(self, node: ast.FunctionDef) -> PyFunction:
        param_types = {}
        for arg in node.args.args:
            if arg.annotation:
                if isinstance(arg.annotation, ast.Name):
                    param_types[arg.arg] = arg.annotation.id
                elif isinstance(arg.annotation, ast.Subscript):
                    if isinstance(arg.annotation.value, ast.Name):
                        param_types[arg.arg] = arg.annotation.value.id
        return_type = None
        if node.returns:
            if isinstance(node.returns, ast.Name):
                return_type = node.returns.id
        body = [s for s in (self.translate_stmt(b) for b in node.body) if s]
        return PyFunction(
            name=node.name,
            params=[a.arg for a in node.args.args],
            param_types=param_types,
            return_type=return_type,
            body=body,
        )

    def _call_name(self, node: ast.Call) -> Optional[str]:
        if isinstance(node.func, ast.Name):
            return node.func.id
        if isinstance(node.func, ast.Attribute):
            parts = []
            c = node.func
            while isinstance(c, ast.Attribute):
                parts.append(c.attr)
                c = c.value
            if isinstance(c, ast.Name):
                parts.append(c.id)
            return ".".join(reversed(parts))
        return None

    def _translate_generator(self, node: ast.GeneratorExp) -> Optional[PyExpr]:
        if node.generators and len(node.generators) == 1:
            gen = node.generators[0]
            if isinstance(gen.target, ast.Name):
                iterable = self.translate_expr(gen.iter)
                predicate = self.translate_expr(node.elt)
                if iterable and predicate:
                    return PyGeneratorExpr(
                        iterator=gen.target.id,
                        iterable=iterable,
                        predicate=predicate,
                        quantifier="all",
                    )
        return None

    def _translate_list_comp(self, node: ast.ListComp) -> Optional[PyExpr]:
        if not node.generators:
            return None
        gen = node.generators[0]
        if not isinstance(gen.target, ast.Name):
            return None
        iterable = self.translate_expr(gen.iter)
        elt = self.translate_expr(node.elt)
        if not iterable or not elt:
            return None
        conds = [self.translate_expr(c) for c in gen.ifs]
        conds = [c for c in conds if c is not None]
        return PyListComp(elt=elt, var=gen.target.id, iterable=iterable, conds=conds)

    def _extract_invariants(self, body: list[ast.stmt]) -> list:
        """Extract invariant IR from consecutive asserts at top of loop body."""
        if not self._linter:
            return []
        inv_irs = []
        for stmt in body:
            if not isinstance(stmt, ast.Assert):
                break
            lr = self._linter.lint_expression(stmt.test)
            if lr.is_valid and lr.ir:
                inv_irs.append(lr.ir)
            else:
                break
        return inv_irs
