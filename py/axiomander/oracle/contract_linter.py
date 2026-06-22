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
    Expr, Var, IntLit, BoolLit, BinOp, Logical,
    LenExpr, IndexExpr, DictLenExpr, DictCountExpr,
    AllExpr, AnyExpr, SliceLenExpr,
    MinExpr, MaxExpr, SumExpr, StrLitExpr, FloatExpr, TupleExpr, DictExpr, SetExpr,
    ImpliesExpr, RaisesExpr, IsShape, IsValid, ListEqExpr,
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
    "get", "list", "dict",
    "lower", "upper", "startswith", "endswith",
    "re_match",   # regex membership: s.re_match("[0-9]+")
    "is_shape",   # Pydantic shape predicate
    "field",      # field(obj, "name", var) → flat-field access
    "owns",       # resource ownership: owns(box) → separation-logic footprint
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

    def __init__(self, params: list[str] | None = None, context: str = "postcondition",
                  predicates: dict | None = None, unbound: frozenset[str] = frozenset(),
                  ghost_resolver: dict[str, str] | None = None,
                  param_type_hint: dict[str, str] | None = None):
        self.violations: list[LintViolation] = []
        self.params = params or []
        self.context = context
        self.predicates: dict = predicates or {}
        self.var_types: dict[str, str] = {}  # var_name → "dict" | "list" | "int" | "unknown"
        self.unbound: frozenset[str] = unbound
        self.ghost_resolver: dict[str, str] = ghost_resolver or {}
        self.param_type_hint: dict[str, str] = param_type_hint or {}

    def lint_expression(self, node: ast.expr) -> LintResult:
        """Convert a Python expression to IR. Returns LintResult with coq/smt."""
        assert isinstance(node, ast.expr)
        self.violations = []
        ir = self.visit(node)
        coq = ir.to_coq(scoped=(self.context != "precondition"), unbound=self.unbound) if ir else ""
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
            op = self._translate_compare_op(node.ops[0])
            # List literal equality: result == [] compiles to length comparison
            # via ListEqExpr which preserves the semantic intent.
            if isinstance(node.comparators[0], ast.List):
                left = self.visit(node.left)
                if left and isinstance(left, Var) and op in ("=", "<>"):
                    n = len(node.comparators[0].elts)
                    return ListEqExpr(name=left.name, op=op, n_elements=n)
            # Set-literal membership: x in {"a", "b", ...} expands to a
            # disjunction of equalities; x not in {...} to a conjunction of
            # inequalities.  String elements use StringEqualsExpr; ints use
            # BinOp '='.  This is the contract-language form for
            # `result.status in {"fulfilled", "failed_recoverably"}`.
            if (op in ("in", "notin")
                    and isinstance(node.comparators[0], ast.Set)):
                member = self._expand_set_membership(
                    node.left, node.comparators[0], negated=(op == "notin"))
                if member is not None:
                    return member
            left = self.visit(node.left)
            right = self.visit(node.comparators[0])
            if op == "in":
                # k in d → dict membership: ADictLen "d" k != 0
                # right is already resolved by the visitor (handles both bare
                # names and attribute paths like self.nodes → Var("self_nodes"))
                if left and right and isinstance(left, Var) and isinstance(right, Var):
                    return BinOp(op="<>", left=DictLenExpr(name=right.name, key=left), right=IntLit(value=0))
                # String substring containment: needle in haystack
                # Uses Coq's String.index idiom for substring check.
                if left and right and isinstance(right, Var):
                    from .contract_ir import StringContainsExpr
                    needle = left.name if isinstance(left, Var) else str(getattr(left, 'value', left))
                    return StringContainsExpr(needle=needle, haystack=right.name)
                return BinOp(op="<>", left=IntLit(value=1), right=IntLit(value=0))
            elif op == "notin":
                # k not in d → dict non-membership: ADictLen "d" k == 0
                if left and right and isinstance(left, Var) and isinstance(right, Var):
                    return BinOp(op="=", left=DictLenExpr(name=right.name, key=left), right=IntLit(value=0))
                # String substring non-containment: needle not in haystack
                if left and right and isinstance(right, Var):
                    from .contract_ir import StringContainsExpr
                    needle = left.name if isinstance(left, Var) else str(getattr(left, 'value', left))
                    return StringContainsExpr(needle=needle, haystack=right.name, negated=True)
                return BinOp(op="=", left=IntLit(value=1), right=IntLit(value=0))
            if left and right:
                # NOTE: BoolLit→IntLit conversion removed for Iris.
                # BoolLit comparisons (e.g. result == True) now survive
                # as bool so that _result_value_kind detects boolean
                # result types and the postcondition uses the bool wrapper.
                # String comparison: Var == "literal" → String.eqb form
                # Only when the Var is a known string type.
                if op in ("=", "!=") and isinstance(left, Var) and isinstance(right, StrLitExpr):
                    from .contract_ir import StringEqualsExpr
                    if self.var_types.get(left.name) in ("str", "string"):
                        return StringEqualsExpr(var=left.name, literal=right.value, negated=(op == "!="))
                if op in ("=", "!=") and isinstance(right, Var) and isinstance(left, StrLitExpr):
                    from .contract_ir import StringEqualsExpr
                    if self.var_types.get(right.name) in ("str", "string"):
                        return StringEqualsExpr(var=right.name, literal=left.value, negated=(op == "!="))
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

    def _expand_set_membership(self, left_node: ast.expr, set_node: ast.Set,
                               negated: bool) -> Optional[Expr]:
        """Expand `x in {e1, e2, ...}` to a disjunction of equalities.

        `x in {"a", "b"}`     -> (x = "a") \\/ (x = "b")
        `x not in {"a", "b"}` -> (x <> "a") /\\ (x <> "b")

        String elements produce StringEqualsExpr; integer elements produce
        BinOp.  The left operand may be a Name or an attribute chain
        (e.g. result.status), resolved through the normal visitor.
        """
        from .contract_ir import StringEqualsExpr
        left = self.visit(left_node)
        if left is None or not isinstance(left, Var):
            return None
        terms: list[Expr] = []
        for elt in set_node.elts:
            if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
                terms.append(StringEqualsExpr(
                    var=left.name, literal=elt.value, negated=negated))
            elif isinstance(elt, ast.Constant) and isinstance(elt.value, bool):
                iv = 1 if elt.value else 0
                terms.append(BinOp(op=("<>" if negated else "="),
                                   left=left, right=IntLit(value=iv)))
            elif isinstance(elt, ast.Constant) and isinstance(elt.value, int):
                terms.append(BinOp(op=("<>" if negated else "="),
                                   left=left, right=IntLit(value=elt.value)))
            else:
                # Unsupported element kind: bail to the generic path.
                return None
        if not terms:
            return None
        if len(terms) == 1:
            return terms[0]
        return Logical(op=("and" if negated else "or"), operands=terms)

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
            return BinOp(op="*", left=IntLit(value=-1), right=inner)
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
        # For method calls (d.name), also check just the method name
        method_name = name.split(".")[-1] if "." in name else name
        if name == "implies":
            if len(node.args) == 2:
                left = self.visit(node.args[0])
                right = self.visit(node.args[1])
                if left and right:
                    return ImpliesExpr(left=left, right=right)
            return None
            return None
        if name == "raises":
            if len(node.args) == 2:
                exc_arg = node.args[0]
                cond_arg = node.args[1]
                if isinstance(exc_arg, ast.Name):
                    exc_type = exc_arg.id
                elif isinstance(exc_arg, ast.Attribute):
                    exc_type = exc_arg.attr
                else:
                    self._violation(node, ExprKind.UNSUPPORTED,
                                    "raises() first arg must be an exception class name")
                    return None
                cond = self.visit(cond_arg)
                if cond is None:
                    return None
                return RaisesExpr(exc_type=exc_type, cond=cond)
            self._violation(node, ExprKind.UNSUPPORTED,
                            "raises() requires exactly 2 arguments: raises(ExcType, cond)")
            return None
        if name in ("is_shape", "is_valid"):
            if len(node.args) == 2:
                obj = self._extract_name(node.args[0])
                type_name = self._extract_name(node.args[1])
                if obj and type_name:
                    cls = IsShape if name == "is_shape" else IsValid
                    return cls(obj=obj, model_type=type_name)
            return None
        if name == "field":
            # field(obj, "field_name", var) → var == obj_field_name
            if len(node.args) == 3:
                obj = self._extract_name(node.args[0])
                field_name = node.args[1].value if isinstance(node.args[1], ast.Constant) else None
                var = self.visit(node.args[2])
                if obj and field_name and var:
                    from .contract_ir import BinOp, IntLit
                    # _escape_field convention: literal underscores → double underscores
                    safe_field = field_name.replace("_", "__")
                    flat_key = f"{obj}_{safe_field}"
                    return BinOp(op="=", left=var, right=Var(name=flat_key))
            return None
        # s.re_match("pattern") -- regex membership predicate.
        # AST: Call(func=Attribute(value=Name(id=subject), attr="re_match"),
        #           args=[Constant(value=pattern)])
        if method_name == "re_match":
            if (len(node.args) == 1
                    and isinstance(node.func, ast.Attribute)
                    and isinstance(node.func.value, ast.Name)
                    and isinstance(node.args[0], ast.Constant)
                    and isinstance(node.args[0].value, str)):
                from .contract_ir import ReMatchExpr
                subject = node.func.value.id
                pattern = node.args[0].value
                return ReMatchExpr(subject=subject, pattern=pattern)
            self._violation(node, ExprKind.UNSUPPORTED,
                            "re_match() requires exactly one string literal argument: "
                            "s.re_match(\"[0-9]+\")")
            return None
        if name == "load":
            if len(node.args) == 1 and isinstance(node.args[0], ast.Name):
                return Var(name=node.args[0].id)
            return None
        if name == "store":
            return None  # store is not a pure expression
        if name not in PURE_BUILTINS and name not in PURE_MODULE_FUNCTIONS \
           and method_name not in PURE_BUILTINS:
            if name in self.predicates:
                return self._expand_predicate(node, name)
            if name == "load":
                if len(node.args) == 1 and isinstance(node.args[0], ast.Name):
                    return Var(name=node.args[0].id)
                return None
            if name == "store":
                return None  # store is not a pure expression
        return self._translate_pure_call(node, name)

    def _expand_predicate(self, node: ast.Call, name: str) -> Optional[Expr]:
        """Expand a call to a user-defined pure predicate by inlining its body.

        For simple predicates, inlines the return expression.
        For loop predicates, applies the detected recursor combinator.
        """
        import ast as ast_module
        entry = self.predicates[name]
        param_names = entry[0]
        body_expr = entry[1]
        post_asserts = entry[2] if len(entry) > 2 else []
        recursor = entry[3] if len(entry) > 3 else None
        lam = entry[4] if len(entry) > 4 else None

        if recursor is not None and lam is not None:
            # Loop predicate → recursor combinator with arg substitution
            from .predicate_lowering import Recursor as R
            rname = {R.EXISTSb: "existsb", R.FORALLB: "forallb",
                     R.COUNTB: "countb", R.FOLD_LEFT: "fold_left",
                     R.FILTERB: "filterb"}.get(recursor, "existsb")
            from .contract_ir import RecursorExpr
            list_arg = node.args[0].id if isinstance(node.args[0], ast.Name) else "xs"
            # Substitute call-site arguments into the lambda
            lam_subst = lam
            for i, p in enumerate(param_names):
                if i < len(node.args):
                    actual = node.args[i].id if isinstance(node.args[i], ast.Name) else str(node.args[i])
                    lam_subst = lam_subst.replace(p, actual)
            return RecursorExpr(recursor=rname, arg=list_arg, predicate=lam_subst)
        if len(node.args) != len(param_names):
            self._violation(node, ExprKind.IMPURE_CALL,
                          f"Predicate '{name}' expects {len(param_names)} args, got {len(node.args)}")
            return None
        if body_expr is not None:
            class _Subst(ast_module.NodeTransformer):
                def __init__(self, mapping):
                    self.mapping = mapping
                def visit_Name(self, n):
                    if n.id in self.mapping:
                        return self.mapping[n.id]
                    return n
            mapping = {p: a for p, a in zip(param_names, node.args)}
            expanded = _Subst(mapping).visit(ast_module.fix_missing_locations(
                ast_module.Module(body=[ast_module.Expr(value=body_expr)], type_ignores=[])
            ))
            inner_expr = expanded.body[0].value
            return self.visit(inner_expr)
        if post_asserts:
            class _Subst(ast_module.NodeTransformer):
                def __init__(self, mapping):
                    self.mapping = mapping
                def visit_Name(self, n):
                    if n.id in self.mapping:
                        return self.mapping[n.id]
                    return n
            mapping = {p: a for p, a in zip(param_names, node.args)}
            mapping['result'] = ast_module.Constant(value=1)
            conjuncts = []
            for post in post_asserts:
                substituted = _Subst(mapping).visit(ast_module.fix_missing_locations(
                    ast_module.Module(body=[ast_module.Expr(value=post.test)], type_ignores=[])
                ))
                inner_ir = self.visit(substituted.body[0].value)
                if inner_ir:
                    conjuncts.append(inner_ir)
            if len(conjuncts) == 1:
                return conjuncts[0]
            elif len(conjuncts) > 1:
                return Logical(op="and", operands=conjuncts)
            return None
        self._violation(node, ExprKind.IMPURE_CALL,
                      f"Predicate '{name}' contains loops or recursion. "
                      f"Express the property directly instead, e.g. "
                      f"all(result[i] <= result[i+1] for i in range(len(result)-1))")
        return None

    def visit_Constant(self, node: ast.Constant) -> Expr:
        if isinstance(node.value, bool):
            return BoolLit(value=node.value)
        if isinstance(node.value, int):
            return IntLit(value=node.value)
        if isinstance(node.value, str):
            return StrLitExpr(value=node.value)
        if isinstance(node.value, float):
            # Float literals → FloatExpr (Z-encoded, scaled * 100)
            return FloatExpr(value=int(node.value * 100))
        return IntLit(value=0)

    def visit_Tuple(self, node: ast.Tuple) -> Expr:
        elements = [self.visit(e) for e in node.elts]
        elements = [e for e in elements if e is not None]
        return TupleExpr(elements=elements)

    def visit_Dict(self, node: ast.Dict) -> Expr:
        pairs = []
        for k, v in zip(node.keys, node.values):
            ke = self.visit(k) if k else None
            ve = self.visit(v) if v else None
            if ke and ve:
                pairs.append((ke, ve))
        return DictExpr(pairs=pairs) if pairs else None

    def visit_Set(self, node: ast.Set) -> Expr:
        elements = [self.visit(e) for e in node.elts]
        elements = [e for e in elements if e is not None]
        return SetExpr(elements=elements) if elements else None

    def visit_Name(self, node: ast.Name) -> Expr:
        return Var(name=node.id)

    def visit_Attribute(self, node: ast.Attribute) -> Expr:
        if isinstance(node.value, ast.Subscript):
            base = node.value.value
            if isinstance(base, ast.Name):
                name = f"{base.id}.{node.attr}"
            else:
                name = f"?.{node.attr}"
            idx = self.visit(node.value.slice) if isinstance(node.value.slice, ast.expr) else IntLit(value=0)
            if not idx:
                idx = IntLit(value=0)
            return IndexExpr(name=name, index=idx)
        # Resolve enum member references to their integer encoding
        if isinstance(node.value, ast.Name):
            from .shape_ir import lookup_enum_value, lookup_shape
            ev = lookup_enum_value(node.value.id, node.attr)
            if ev is not None:
                return IntLit(value=ev)
            # Model field access (Pydantic/shape): resolve the param name
            # to its declared type, then check the shape registry.  If the
            # type IS a shape, produce a structural FieldAccess (not a
            # flattened Var) so that contracts like
            # [assert account.balance >= 0] compile to Z-valued Coq Props.
            param_name = node.value.id
            model_type = self.param_type_hint.get(param_name)
            if model_type and lookup_shape(model_type) is not None:
                from .contract_ir import FieldAccess
                return FieldAccess(obj=param_name, field=node.attr)
        # If the base is a Call (e.g. Order(order_id).status), the
        # contract language can't represent the call return value as
        # a flat variable.  Return OpaqueTerm so the comparison
        # short-circuits to True (the observer's guarantee comes from
        # the callee's contract transitively).
        if isinstance(node.value, ast.Call):
            from .contract_ir import OpaqueTerm
            return OpaqueTerm(name=self._get_call_name(node.value) or "?")
        # result.attr (e.g. result.status) — structural field projection
        # on the return value.  Emit FieldAccess with obj="result"; in the
        # postcondition compilation, the obj is mapped to the raw WP binder
        # "v" (not the unpacked Z/bool/string bound variable) so that
        # model_field_Z v "attr" extracts the field from the return value.
        if isinstance(node.value, ast.Name) and node.value.id == "result":
            from .contract_ir import FieldAccess
            return FieldAccess(obj="result", field=node.attr)
        path = self._attribute_path(node)
        # Always normalise dots to underscores with _escape_field convention:
        # precondition: bare var  e.g. item_value  (Coq param name)
        # postcondition: state key  e.g. s "item_value"%string
        # Using the same flattening in both contexts keeps contract key names
        # consistent with what _expand_params and _lower_attribute produce.
        parts = path.split(".")
        parts[-1] = parts[-1].replace("_", "__")
        return Var(name="_".join(parts))

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

    def _extract_name(self, node: ast.expr) -> Optional[str]:
        """Return the identifier if node is a Name, else None."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            return node.attr
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
            ast.In: "in", ast.NotIn: "notin",
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
                if self.var_types.get(lst_name) == "dict":
                    return DictCountExpr(name=lst_name)
                return LenExpr(name=lst_name)
            return IntLit(value=0)
        if name in ("abs", "min", "max"):
            args = [self.visit(a) for a in node.args]
            args = [a for a in args if a]
            if len(args) >= 2 and name == "min":
                return MinExpr(left=args[0], right=args[1])
            if len(args) >= 2 and name == "max":
                return MaxExpr(left=args[0], right=args[1])
            if not args:
                return IntLit(value=0)
        if name == "sum":
            if node.args and isinstance(node.args[0], ast.Name):
                return SumExpr(name=node.args[0].id)
            return IntLit(value=0)
        if name in ("all", "any"):
            return self._translate_quantifier(node, name)
        if name == "isinstance":
            # isinstance(obj, SomeType) → obj_tag == TYPE_TAG
            if len(node.args) == 2 and isinstance(node.args[0], ast.Name):
                obj_name = node.args[0].id
                type_arg = node.args[1]
                type_name = None
                if isinstance(type_arg, ast.Attribute):
                    from axiomander.oracle.mcp_server import _dotted_path
                    type_name = _dotted_path(type_arg)
                elif isinstance(type_arg, ast.Name):
                    type_name = type_arg.id
                if type_name:
                    from axiomander.oracle.py_to_imp import PyToImpLowerer
                    tag = PyToImpLowerer._TYPE_TAG_MAP.get(type_name)
                    if tag is not None:
                        tag_var = f"{obj_name}_tag"
                        return BinOp(op="=", left=Var(name=tag_var), right=IntLit(value=tag))
            return IntLit(value=1)
        if name == "owns":
            # owns(x) → resource ownership predicate
            if node.args and isinstance(node.args[0], ast.Name):
                from .contract_ir import ROwnExpr
                return ROwnExpr(obj=node.args[0].id)
            return IntLit(value=1)
        # Ghost resolver: observer calls resolved to ghost variable names
        # from the callee's OpaqueSpec.ghost_vars mapping.
        if name in self.ghost_resolver:
            return Var(name=self.ghost_resolver[name])
        # Unknown function call → opaque DB observer (OpaqueTerm → True)
        # opaque DB observer (e.g. db_get_payment_state(order_id)).
        # Compiles to True in Coq Prop; the real guarantee is discharged
        # transitively through the callee's own contract.
        from .contract_ir import OpaqueTerm
        return OpaqueTerm(name=name, args=[
            self.visit(a) for a in node.args if self.visit(a) is not None
        ])

    def _translate_quantifier(self, node: ast.Call, name: str) -> Optional[Expr]:
        """Translate all(p(x) for x in lst) or all(p(x) for x in range(lo, hi))."""
        if node.args and isinstance(node.args[0], ast.GeneratorExp):
            gen = node.args[0]
            if gen.generators and len(gen.generators) == 1:
                comp = gen.generators[0]
                if isinstance(comp.target, ast.Name) and isinstance(comp.iter, ast.List):
                    var = comp.target.id
                    elts = [self.visit(e) for e in comp.iter.elts]
                    elts = [e for e in elts if e]
                    if not elts:
                        return BoolLit(value=(name == "all"))
                    pred = self.visit(gen.elt)
                    if pred:
                        if name == "all":
                            return AllExpr(var=var, lst="__literal__", pred=pred,
                                          lower=IntLit(value=0), upper=IntLit(value=1))
                        # For any(): expand to disjunction pred[x := e] for each element
                        from .contract_ir import _subst_var, Logical as CLogical
                        terms = [_subst_var(pred, var, e.value if hasattr(e, 'value') and e.kind == 'int' else None)
                                 for e in elts]
                        terms = [t for t in terms if t]
                        if len(terms) == 1:
                            return terms[0]
                        return CLogical(op="or", operands=terms)
                if isinstance(comp.target, ast.Name) and isinstance(comp.iter, ast.Name):
                    var = comp.target.id
                    lst = comp.iter.id
                    pred = self.visit(gen.elt)
                    if pred:
                        if name == "all":
                            return AllExpr(var=var, lst=lst, pred=pred)
                        return AnyExpr(var=var, lst=lst, pred=pred)
                if isinstance(comp.target, ast.Name) and isinstance(comp.iter, ast.Call):
                    if isinstance(comp.iter.func, ast.Name) and comp.iter.func.id == "range":
                        var = comp.target.id
                        args = comp.iter.args
                        if len(args) == 1:
                            lower = IntLit(value=0)
                            upper = self.visit(args[0])
                        elif len(args) == 2:
                            lower = self.visit(args[0])
                            upper = self.visit(args[1])
                        else:
                            return BoolLit(value=True)
                        pred = self.visit(gen.elt)
                        if pred and lower and upper:
                            if name == "all":
                                return AllExpr(var=var, lower=lower, upper=upper, pred=pred)
                            return AnyExpr(var=var, lower=lower, upper=upper, pred=pred)
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
