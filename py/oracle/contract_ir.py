"""
Intermediate representation for contract expressions.

A typed expression AST that compiles to both Coq Prop and SMT-LIB.
Uses Pydantic discriminated unions for type-safe matching.
"""

from __future__ import annotations
from typing import Literal, Union, Optional
from pydantic import BaseModel, Field


class Var(BaseModel):
    kind: Literal["var"] = "var"
    name: str

    def to_coq(self, scoped: bool = False) -> str:
        if scoped:
            return f's "{self.name}"%string'
        return self.name

    def to_smt(self) -> str:
        return self.name


class IntLit(BaseModel):
    kind: Literal["int"] = "int"
    value: int

    def to_coq(self, scoped: bool = False) -> str:
        return str(self.value)

    def to_smt(self) -> str:
        return str(self.value)


class BoolLit(BaseModel):
    kind: Literal["bool"] = "bool"
    value: bool

    def to_coq(self, scoped: bool = False) -> str:
        return "True" if self.value else "False"

    def to_smt(self) -> str:
        return "true" if self.value else "false"


class BinOp(BaseModel):
    kind: Literal["binop"] = "binop"
    op: str  # +, -, *, /, mod, =, <=, >=, <, >
    left: Expr
    right: Expr

    def to_coq(self, scoped: bool = False) -> str:
        op_map = {"/": "/", "mod": "mod"}
        coq_op = op_map.get(self.op, self.op)
        left = self.left.to_coq(scoped)
        right = self.right.to_coq(scoped)
        is_str_cmp = scoped and self.op in ('=', '<>') and (
            hasattr(self.right, 'kind') and self.right.kind == 'strlit'
        )
        is_float_cmp = scoped and self.op in ('=', '<>') and (
            hasattr(self.right, 'kind') and self.right.kind == 'float'
        )
        is_tuple_cmp = scoped and self.op in ('=', '<>') and (
            hasattr(self.right, 'kind') and self.right.kind == 'tuple'
        )
        if scoped and self.op in ('+', '-', '*', '/', 'mod', '<', '<=', '>', '>=', '=', '<>'):
            if is_str_cmp:
                if left.startswith('s "'):
                    left = f'asString ({left})'
            elif is_float_cmp:
                if left.startswith('s "'):
                    left = f'asFloat ({left})'
            elif is_tuple_cmp:
                if left.startswith('s "'):
                    return f"(value_eqb ({left}) {right} = true)"
            else:
                if left.startswith('s "'):
                    left = f'asZ ({left})'
                if right.startswith('s "'):
                    right = f'asZ ({right})'
        return f"({left} {coq_op} {right})"

    def to_smt(self) -> str:
        op_map = {"mod": "mod", "/": "div"}
        smt_op = op_map.get(self.op, self.op)
        return f"({smt_op} {self.left.to_smt()} {self.right.to_smt()})"


class Logical(BaseModel):
    kind: Literal["logical"] = "logical"
    op: str  # and, or, not
    operands: list[Expr] = Field(default_factory=list)

    def to_coq(self, scoped: bool = False) -> str:
        if self.op == "not":
            inner = self.operands[0].to_coq(scoped)
            return f"~ ({inner})"
        sep = " /\\ " if self.op == "and" else " \\/ "
        return "(" + sep.join(o.to_coq(scoped) for o in self.operands) + ")"

    def to_smt(self) -> str:
        if self.op == "not":
            return f"(not {self.operands[0].to_smt()})"
        smt_op = "and" if self.op == "and" else "or"
        return f"({smt_op} {' '.join(o.to_smt() for o in self.operands)})"


class LenExpr(BaseModel):
    """len(lst) — array length lookup."""
    kind: Literal["len"] = "len"
    name: str

    def to_coq(self, scoped: bool = False) -> str:
        if scoped:
            return f's "{self.name}._len"%string'
        return f"{self.name}__len"

    def to_smt(self) -> str:
        return f"{self.name}__len"


class IndexExpr(BaseModel):
    """lst[i] — array index lookup."""
    kind: Literal["index"] = "index"
    name: str
    index: Expr

    def to_coq(self, scoped: bool = False) -> str:
        if scoped:
            return f's (parray_key "{self.name}"%string {self.index.to_coq(False)})%string'
        return f"{self.name}___{self.index.to_coq(False)}"

    def to_smt(self) -> str:
        return f"{self.name}___{self.index.to_smt()}"


class DictLenExpr(BaseModel):
    """len(dict[key]) — dict value list length."""
    kind: Literal["dict_len"] = "dict_len"
    name: str
    key: Expr

    def to_coq(self, scoped: bool = False) -> str:
        key_str = self.key.to_coq(False)
        if scoped:
            return f's (parray_len_key (dict_key "{self.name}"%string ({key_str})))%string'
        return f"{self.name}_v_{key_str}__len"

    def to_smt(self) -> str:
        return f"{self.name}_v_{self.key.to_smt()}__len"


class DictCountExpr(BaseModel):
    """len(dict) — number of keys in dict."""
    kind: Literal["dict_count"] = "dict_count"
    name: str

    def to_coq(self, scoped: bool = False) -> str:
        if scoped:
            return f's (dict_count_key "{self.name}"%string)%string'
        return f"{self.name}__count"

    def to_smt(self) -> str:
        return f"{self.name}__count"


class AllExpr(BaseModel):
    """all(p(x) for x in lst) or all(p(x) for x in range(lo, hi))."""
    kind: Literal["all"] = "all"
    var: str
    lst: str = ""
    pred: "Expr"
    lower: Optional["Expr"] = None
    upper: Optional["Expr"] = None

    def to_coq(self, scoped: bool = False) -> str:
        return "True"

    def to_smt(self) -> str:
        p = self.pred.to_smt()
        if self.lower is not None and self.upper is not None:
            lo = self.lower.to_smt()
            hi = self.upper.to_smt()
            return f"(forall (({self.var} Int)) (=> (and (<= {lo} {self.var}) (< {self.var} {hi})) {p}))"
        return f"(forall (({self.var} Int)) (=> (and (<= 0 {self.var}) (< {self.var} {self.lst}__len)) {p}))"


class AnyExpr(BaseModel):
    """any(p(x) for x in lst) or any(p(x) for x in range(lo, hi))."""
    kind: Literal["any"] = "any"
    var: str
    lst: str = ""
    pred: "Expr"
    lower: Optional["Expr"] = None
    upper: Optional["Expr"] = None

    def to_coq(self, scoped: bool = False) -> str:
        return "True"

    def to_smt(self) -> str:
        p = self.pred.to_smt()
        if self.lower is not None and self.upper is not None:
            lo = self.lower.to_smt()
            hi = self.upper.to_smt()
            return f"(exists (({self.var} Int)) (and (and (<= {lo} {self.var}) (< {self.var} {hi})) {p}))"
        return f"(exists (({self.var} Int)) (and (and (<= 0 {self.var}) (< {self.var} {self.lst}__len)) {p}))"


class SliceLenExpr(BaseModel):
    """len(lst[i:j]) — length of slice = j - i."""
    kind: Literal["slice_len"] = "slice_len"
    name: str
    start: Optional["Expr"] = None
    end: Optional["Expr"] = None

    def to_coq(self, scoped: bool = False) -> str:
        s = self.start.to_coq(False) if self.start else "0"
        e = self.end.to_coq(False) if self.end else f'asZ (s "{self.name}._len"%string)' if scoped else f"{self.name}__len"
        return f"({e} - {s})"

    def to_smt(self) -> str:
        s = self.start.to_smt() if self.start else "0"
        e = self.end.to_smt() if self.end else f"{self.name}__len"
        return f"(- {e} {s})"


class MinExpr(BaseModel):
    """min(a, b) — minimum of two values."""
    kind: Literal["min"] = "min"
    left: "Expr"
    right: "Expr"

    def to_coq(self, scoped: bool = False) -> str:
        left = self.left.to_coq(scoped)
        right = self.right.to_coq(scoped)
        if scoped:
            if left.startswith('s "'):
                left = f'asZ ({left})'
            if right.startswith('s "'):
                right = f'asZ ({right})'
        return f"(Z.min ({left}) ({right}))"

    def to_smt(self) -> str:
        return f"(ite (< {self.left.to_smt()} {self.right.to_smt()}) {self.left.to_smt()} {self.right.to_smt()})"


class MaxExpr(BaseModel):
    """max(a, b) — maximum of two values."""
    kind: Literal["max"] = "max"
    left: "Expr"
    right: "Expr"

    def to_coq(self, scoped: bool = False) -> str:
        left = self.left.to_coq(scoped)
        right = self.right.to_coq(scoped)
        if scoped:
            if left.startswith('s "'):
                left = f'asZ ({left})'
            if right.startswith('s "'):
                right = f'asZ ({right})'
        return f"(Z.max ({left}) ({right}))"

    def to_smt(self) -> str:
        return f"(ite (> {self.left.to_smt()} {self.right.to_smt()}) {self.left.to_smt()} {self.right.to_smt()})"


class SumExpr(BaseModel):
    """sum(lst) — sum of list elements."""
    kind: Literal["sum"] = "sum"
    name: str

    def to_coq(self, scoped: bool = False) -> str:
        return "0"

    def to_smt(self) -> str:
        return f"{self.name}__sum"


class FloatExpr(BaseModel):
    """Float literal for contracts: result == 3.14. Z-encoded (scaled * 100)."""
    kind: Literal["float"] = "float"
    value: int  # Z-encoded integer

    def to_coq(self, scoped: bool = False) -> str:
        return str(self.value)

    def to_smt(self) -> str:
        return str(self.value)


class StrLitExpr(BaseModel):
    """String literal for comparison: s == \"value\"."""
    kind: Literal["strlit"] = "strlit"
    value: str

    def to_coq(self, scoped: bool = False) -> str:
        escaped = self.value.replace('\\', '\\\\').replace('"', '\\"')
        return f'"{escaped}"%string'

    def to_smt(self) -> str:
        return f'"{self.value}"'


class TupleExpr(BaseModel):
    """Tuple literal for contracts: result == (1, 2)."""
    kind: Literal["tuple"] = "tuple"
    elements: list["Expr"] = Field(default_factory=list)

    def to_coq(self, scoped: bool = False) -> str:
        def wrap_val(e):
            s = e.to_coq(scoped)
            if hasattr(e, 'kind'):
                if e.kind == 'int':
                    return f"(VZ {s})"
                if e.kind == 'strlit':
                    return f"(VString {s})"
                if e.kind == 'float':
                    return f"(VFloat {s})"
            return s
        els = " :: ".join(wrap_val(e) for e in self.elements) if self.elements else ""
        return f"(VTuple ({els} :: nil))" if els else "(VTuple nil)"

    def to_smt(self) -> str:
        return "0"


Expr = Union[Var, IntLit, BoolLit, BinOp, Logical, LenExpr, IndexExpr, DictLenExpr, DictCountExpr, AllExpr, AnyExpr, SliceLenExpr, MinExpr, MaxExpr, SumExpr, StrLitExpr, FloatExpr, TupleExpr]
