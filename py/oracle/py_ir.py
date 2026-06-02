"""
Faithful Python Core IR — explicit, operational models of Python semantics.

Every Python construct we handle gets an IR node here. The IR is faithful:
it does NOT assume types are known, does NOT silently resolve ambiguous
operations, and does NOT strip Python behavior.

Lowering to the Verification IR (IMP) is a separate, explicit pass.
"""

from __future__ import annotations
from typing import Literal, Union, Optional
from pydantic import BaseModel, Field


# ── Expressions ──────────────────────────────────────────────────

class PyExpr(BaseModel):
    """Base for Python expression nodes."""
    pass


class PyName(PyExpr):
    """A variable reference: x, y, result."""
    kind: Literal["name"] = "name"
    name: str


class PyConstant(PyExpr):
    """A literal constant."""
    kind: Literal["constant"] = "constant"
    value: int | str | bool | float | None
    py_type: str = "int"  # "int", "str", "bool", "float", "None"


class PyBinaryOp(PyExpr):
    """A binary operation: a + b, a - b, etc.
    
    The + operator is AMBIGUOUS — it could be int addition or str/list
    concatenation. The lowering pass resolves this based on contracts.
    """
    kind: Literal["binop"] = "binop"
    op: str  # '+', '-', '*', '/', '//', '%'
    left: PyExpr
    right: PyExpr


class PyCompare(PyExpr):
    """A comparison: a < b, a == b, a is None, etc."""
    kind: Literal["compare"] = "compare"
    op: str  # '<', '<=', '>', '>=', '==', '!=', 'is', 'is not', 'in', 'not in'
    left: PyExpr
    right: PyExpr


class PyBooleanOp(PyExpr):
    """Boolean logic: a and b, a or b, not a."""
    kind: Literal["boolop"] = "boolop"
    op: str  # 'and', 'or', 'not'
    operands: list[PyExpr] = Field(default_factory=list)


class PyUnaryOp(PyExpr):
    """Unary operations: -a, not a."""
    kind: Literal["unaryop"] = "unaryop"
    op: str  # '-', 'not'
    operand: PyExpr


class PyCall(PyExpr):
    """A function or method call: f(args), obj.method(args)."""
    kind: Literal["call"] = "call"
    func: str           # resolved function/method name
    args: list[PyExpr] = Field(default_factory=list)
    is_method: bool = False  # True if called as obj.method(...)


class PySubscript(PyExpr):
    """Container access: obj[key], lst[i]."""
    kind: Literal["subscript"] = "subscript"
    container: PyExpr
    key: PyExpr


class PyAttribute(PyExpr):
    """Attribute access: obj.field, obj.attr."""
    kind: Literal["attribute"] = "attribute"
    obj: PyExpr
    attr: str


class PyListLiteral(PyExpr):
    """List literal: [a, b, c]."""
    kind: Literal["list_literal"] = "list_literal"
    elements: list[PyExpr] = Field(default_factory=list)


class PyListComp(PyExpr):
    """List comprehension: [expr for var in iterable if cond]."""
    kind: Literal["list_comp"] = "list_comp"
    elt: PyExpr
    var: str
    iterable: PyExpr
    conds: list[PyExpr] = Field(default_factory=list)


class PyDictLiteral(PyExpr):
    """Dict literal: {k: v, ...}."""
    kind: Literal["dict_literal"] = "dict_literal"
    pairs: list[dict[str, PyExpr]] = Field(default_factory=list)  # [{"key": k, "value": v}]


class PySetLiteral(PyExpr):
    """Set literal: {a, b, c}."""
    kind: Literal["set_literal"] = "set_literal"
    elements: list[PyExpr] = Field(default_factory=list)


class PyTupleLiteral(PyExpr):
    """Tuple literal: (a, b, c)."""
    kind: Literal["tuple_literal"] = "tuple_literal"
    elements: list[PyExpr] = Field(default_factory=list)


class PyStringLiteral(PyExpr):
    """String literal: 'hello'."""
    kind: Literal["string_literal"] = "string_literal"
    value: str


class PyGeneratorExpr(PyExpr):
    """Generator expression: all(x>0 for x in lst), range(i)."""
    kind: Literal["generator"] = "generator"
    iterator: str     # variable name bound in iteration
    iterable: PyExpr  # the collection being iterated
    predicate: PyExpr  # the condition for each element
    quantifier: str = "all"  # "all", "any"


class PyLen(PyExpr):
    """len(x) — sequence/dict length."""
    kind: Literal["len"] = "len"
    obj: PyExpr


class PyIsInstance(PyExpr):
    """isinstance(x, int) — type check."""
    kind: Literal["isinstance"] = "isinstance"
    obj: PyExpr
    type_name: str  # "int", "str", "float", "bool", etc.


# ── Statements ───────────────────────────────────────────────────

class PyStmt(BaseModel):
    """Base for Python statement nodes."""
    pass


class PyAssign(PyStmt):
    """Variable assignment: x = expr."""
    kind: Literal["assign"] = "assign"
    target: str
    value: PyExpr


class PyAugAssign(PyStmt):
    """Augmented assignment: x += expr, x -= expr."""
    kind: Literal["augassign"] = "augassign"
    target: str
    op: str  # '+', '-', '*', '/'
    value: PyExpr


class PyStoreAttr(PyStmt):
    """Attribute store: obj.field = expr."""
    kind: Literal["store_attr"] = "store_attr"
    obj: str
    attr: str
    value: PyExpr


class PyStoreSubscript(PyStmt):
    """Container store: obj[key] = expr."""
    kind: Literal["store_subscript"] = "store_subscript"
    container: PyExpr
    key: PyExpr
    value: PyExpr


class PyIf(PyStmt):
    """Conditional: if cond: body else: orelse."""
    kind: Literal["if"] = "if"
    test: PyExpr
    body: list[PyStmt] = Field(default_factory=list)
    orelse: list[PyStmt] = Field(default_factory=list)


class PyWhile(PyStmt):
    """While loop: while cond: body. Invariants are contract IR nodes."""
    kind: Literal["while"] = "while"
    test: PyExpr
    body: list[PyStmt] = Field(default_factory=list)
    invariants: list = Field(default_factory=list)  # contract_ir.Expr nodes
    line_number: int = 0


class PyFor(PyStmt):
    """For loop: for var in iterable: body."""
    kind: Literal["for"] = "for"
    var: str
    iterable: PyExpr
    body: list[PyStmt] = Field(default_factory=list)
    invariants: list = Field(default_factory=list)  # contract_ir.Expr nodes


class PyReturn(PyStmt):
    """Return statement."""
    kind: Literal["return"] = "return"
    value: Optional[PyExpr] = None


class PyAssert(PyStmt):
    """Assert statement — contract or invariant."""
    kind: Literal["assert"] = "assert"
    test: PyExpr
    classification: str = "general"  # "precondition", "postcondition", "invariant"
    line_number: int = 0


class PyExprStmt(PyStmt):
    """Expression used as a statement (e.g., function call)."""
    kind: Literal["expr_stmt"] = "expr_stmt"
    expr: PyExpr


class PySliceSubscript(PyExpr):
    """Slice access: lst[start:end]."""
    kind: Literal["slice_subscript"] = "slice_subscript"
    obj: PyExpr
    start: Optional[PyExpr] = None
    end: Optional[PyExpr] = None


class PySliceStore(PyStmt):
    """Slice assignment: lst[start:end] = value."""
    kind: Literal["slice_store"] = "slice_store"
    obj: str
    start: Optional[PyExpr] = None
    end: Optional[PyExpr] = None
    value: PyExpr


class PyPass(PyStmt):
    """pass statement -- no-op."""
    kind: Literal["pass"] = "pass"


class PyRaise(PyStmt):
    """Raise statement: raise ExcType or raise ExcType(msg).

    exc_type: string name of the exception class (e.g. "ValueError").
    message:  optional expression for the exception argument.
    """
    kind: Literal["raise"] = "raise"
    exc_type: str
    message: Optional[PyExpr] = None


class PyExcHandler(BaseModel):
    """A single except clause: except ExcType [as var]: body."""
    exc_type: str        # exception class name, e.g. "ValueError"
    exc_var: Optional[str] = None   # 'as <var>' binding, or None
    body: list[PyStmt] = Field(default_factory=list)


class PyTry(PyStmt):
    """Try/except block.

    Only the body and except handlers are modelled -- finally/else
    clauses are dropped (they are not in scope for Hoare-logic contracts).
    """
    kind: Literal["try"] = "try"
    body: list[PyStmt] = Field(default_factory=list)
    handlers: list[PyExcHandler] = Field(default_factory=list)


# ── Function ─────────────────────────────────────────────────────

class PyFunction(BaseModel):
    """A Python function in the Core IR."""
    name: str
    params: list[str] = Field(default_factory=list)
    param_types: dict[str, str] = Field(default_factory=dict)  # name → "int"|"str"|etc.
    return_type: Optional[str] = None
    body: list[PyStmt] = Field(default_factory=list)
    class_name: Optional[str] = None  # if this is a method


# ── Helpers ──────────────────────────────────────────────────────

def is_pure_expr(expr: PyExpr) -> bool:
    """Check if an expression is observably pure (no calls, no mutation)."""
    if isinstance(expr, PyCall):
        return False
    if isinstance(expr, PyBinaryOp):
        return is_pure_expr(expr.left) and is_pure_expr(expr.right)
    if isinstance(expr, PyCompare):
        return is_pure_expr(expr.left) and is_pure_expr(expr.right)
    if isinstance(expr, PyBooleanOp):
        return all(is_pure_expr(o) for o in expr.operands)
    if isinstance(expr, PyUnaryOp):
        return is_pure_expr(expr.operand)
    if isinstance(expr, PySubscript):
        return is_pure_expr(expr.container) and is_pure_expr(expr.key)
    if isinstance(expr, PyAttribute):
        return is_pure_expr(expr.obj)
    if isinstance(expr, PyGeneratorExpr):
        return is_pure_expr(expr.predicate) and is_pure_expr(expr.iterable)
    return True  # names, constants, literals are pure
