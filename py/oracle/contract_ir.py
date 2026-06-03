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

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        if scoped and self.name not in unbound:
            return f's "{self.name}"%string'
        return self.name

    def to_smt(self) -> str:
        return self.name


class IntLit(BaseModel):
    kind: Literal["int"] = "int"
    value: int

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        return str(self.value)

    def to_smt(self) -> str:
        return str(self.value)


class BoolLit(BaseModel):
    kind: Literal["bool"] = "bool"
    value: bool

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        return "True" if self.value else "False"

    def to_smt(self) -> str:
        return "true" if self.value else "false"


class BinOp(BaseModel):
    kind: Literal["binop"] = "binop"
    op: str  # +, -, *, /, mod, =, <=, >=, <, >
    left: Expr
    right: Expr

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        op_map = {"/": "/", "mod": "mod"}
        coq_op = op_map.get(self.op, self.op)
        left = self.left.to_coq(scoped, unbound)
        right = self.right.to_coq(scoped, unbound)
        is_str_cmp = scoped and self.op in ('=', '<>') and (
            hasattr(self.right, 'kind') and self.right.kind == 'strlit'
        )
        is_float_cmp = scoped and self.op in ('=', '<>') and (
            hasattr(self.right, 'kind') and self.right.kind == 'float'
        )
        is_tuple_cmp = scoped and self.op in ('=', '<>') and (
            hasattr(self.right, 'kind') and self.right.kind == 'tuple'
        )
        is_dict_cmp = scoped and self.op in ('=', '<>') and (
            hasattr(self.right, 'kind') and self.right.kind == 'dict'
        )
        is_set_cmp = scoped and self.op in ('=', '<>') and (
            hasattr(self.right, 'kind') and self.right.kind == 'set'
        )
        if scoped and self.op in ('+', '-', '*', '/', 'mod', '<', '<=', '>', '>=', '=', '<>'):
            if is_str_cmp:
                if left.startswith('s '):
                    left = f'asString ({left})'
            elif is_float_cmp:
                if left.startswith('s '):
                    left = f'asFloat ({left})'
            elif is_tuple_cmp or is_dict_cmp or is_set_cmp:
                if left.startswith('s '):
                    return f"(value_eqb ({left}) {right} = true)"
            else:
                if left.startswith('s '):
                    left = f'asZ ({left})'
                if right.startswith('s '):
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

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        if self.op == "not":
            inner = self.operands[0].to_coq(scoped, unbound)
            return f"~ ({inner})"
        sep = " /\\ " if self.op == "and" else " \\/ "
        return "(" + sep.join(o.to_coq(scoped, unbound) for o in self.operands) + ")"

    def to_smt(self) -> str:
        if self.op == "not":
            return f"(not {self.operands[0].to_smt()})"
        smt_op = "and" if self.op == "and" else "or"
        return f"({smt_op} {' '.join(o.to_smt() for o in self.operands)})"


class LenExpr(BaseModel):
    """len(lst) — array length lookup."""
    kind: Literal["len"] = "len"
    name: str

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        if scoped:
            return f'asZ (hget s "{self.name}"%string len_f)'
        return f"{self.name}__len"

    def to_smt(self) -> str:
        return f"{self.name}__len"


class IndexExpr(BaseModel):
    """lst[i] — array index lookup."""
    kind: Literal["index"] = "index"
    name: str
    index: Expr

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        if scoped:
            idx_coq = self.index.to_coq(False, unbound)
            return f'asZ (hget s "{self.name}"%string (elem_f ({idx_coq})))'
        return f"{self.name}___{self.index.to_coq(False, unbound)}"

    def to_smt(self) -> str:
        return f"{self.name}___{self.index.to_smt()}"


class DictLenExpr(BaseModel):
    """len(dict[key]) — dict value list length."""
    kind: Literal["dict_len"] = "dict_len"
    name: str
    key: Expr

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        key_str = self.key.to_coq(False, unbound)
        if scoped:
            return f'asZ (hget s "{self.name}"%string (dlen_f ({key_str})))'
        return f"{self.name}_v_{key_str}__len"

    def to_smt(self) -> str:
        return f"{self.name}_v_{self.key.to_smt()}__len"


class DictCountExpr(BaseModel):
    """len(dict) — number of keys in dict."""
    kind: Literal["dict_count"] = "dict_count"
    name: str

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        if scoped:
            return f'asZ (hget s "{self.name}"%string count_f)'
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

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        unbound_vars = unbound | {self.var}
        p = self.pred.to_coq(scoped, unbound=unbound_vars)
        if self.lower is not None and self.upper is not None:
            lo = self.lower.to_coq(scoped, unbound_vars)
            hi = self.upper.to_coq(scoped, unbound_vars)
            if scoped:
                if lo.startswith('s '):
                    lo = f'asZ ({lo})'
                if hi.startswith('s '):
                    hi = f'asZ ({hi})'
            return f"(forall ({self.var} : Z), {lo} <= {self.var} < {hi} -> {p})"
        ln = f'asZ (hget s "{self.lst}"%string len_f)' if (scoped and self.lst) else (f"{self.lst}__len" if self.lst else "0")
        return f"(forall ({self.var} : Z), 0 <= {self.var} < {ln} -> {p})"

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

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
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

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        s = self.start.to_coq(False, unbound) if self.start else "0"
        e = self.end.to_coq(False, unbound) if self.end else f'asZ (s "{self.name}._len"%string)' if scoped else f"{self.name}__len"
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

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        left = self.left.to_coq(scoped, unbound)
        right = self.right.to_coq(scoped, unbound)
        if scoped:
            if left.startswith('s '):
                left = f'asZ ({left})'
            if right.startswith('s '):
                right = f'asZ ({right})'
        return f"(Z.min ({left}) ({right}))"

    def to_smt(self) -> str:
        return f"(ite (< {self.left.to_smt()} {self.right.to_smt()}) {self.left.to_smt()} {self.right.to_smt()})"


class MaxExpr(BaseModel):
    """max(a, b) — maximum of two values."""
    kind: Literal["max"] = "max"
    left: "Expr"
    right: "Expr"

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        left = self.left.to_coq(scoped, unbound)
        right = self.right.to_coq(scoped, unbound)
        if scoped:
            if left.startswith('s '):
                left = f'asZ ({left})'
            if right.startswith('s '):
                right = f'asZ ({right})'
        return f"(Z.max ({left}) ({right}))"

    def to_smt(self) -> str:
        return f"(ite (> {self.left.to_smt()} {self.right.to_smt()}) {self.left.to_smt()} {self.right.to_smt()})"


class SumExpr(BaseModel):
    """sum(lst) — sum of list elements."""
    kind: Literal["sum"] = "sum"
    name: str

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        return "0"

    def to_smt(self) -> str:
        return f"{self.name}__sum"


class FloatExpr(BaseModel):
    """Float literal for contracts: result == 3.14. Z-encoded (scaled * 100)."""
    kind: Literal["float"] = "float"
    value: int  # Z-encoded integer

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        return str(self.value)

    def to_smt(self) -> str:
        return str(self.value)


class StrLitExpr(BaseModel):
    """String literal for comparison: s == \"value\"."""
    kind: Literal["strlit"] = "strlit"
    value: str

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        escaped = self.value.replace('\\', '\\\\').replace('"', '\\"')
        return f'"{escaped}"%string'

    def to_smt(self) -> str:
        return f'"{self.value}"'


class TupleExpr(BaseModel):
    """Tuple literal for contracts: result == (1, 2)."""
    kind: Literal["tuple"] = "tuple"
    elements: list["Expr"] = Field(default_factory=list)

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        def wrap_val(e):
            s = e.to_coq(scoped, unbound)
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


class DictExpr(BaseModel):
    """Dict literal for contracts: result == {1: 2}. Z-encoded keys/values."""
    kind: Literal["dict"] = "dict"
    pairs: list[tuple["Expr", "Expr"]] = Field(default_factory=list)

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        pas = []
        for k, v in self.pairs:
            ks = k.to_coq(scoped, unbound)
            vs = v.to_coq(scoped, unbound)
            # Wrap Z values
            if hasattr(k, 'kind') and k.kind == 'int':
                ks = f"(VZ {ks})"
            if hasattr(v, 'kind') and v.kind == 'int':
                vs = f"(VZ {vs})"
            pas.append(f"({ks}, {vs})")
        ps = " :: ".join(pas) if pas else ""
        return f"(VDict ({ps} :: nil))" if ps else "(VDict nil)"

    def to_smt(self) -> str:
        return "0"


class SetExpr(BaseModel):
    """Set literal for contracts: result == {1, 2}."""
    kind: Literal["set"] = "set"
    elements: list["Expr"] = Field(default_factory=list)

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        def wrap_val(e):
            s = e.to_coq(scoped, unbound)
            if hasattr(e, 'kind') and e.kind == 'int':
                return f"(VZ {s})"
            return s
        els = " :: ".join(wrap_val(e) for e in self.elements) if self.elements else ""
        return f"(VSet ({els} :: nil))" if els else "(VSet nil)"

    def to_smt(self) -> str:
        return "0"


class ImpliesExpr(BaseModel):
    """Implication: A -> B for conditional guarantees."""
    kind: Literal["implies"] = "implies"
    left: Expr
    right: Expr

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        return f"({self.left.to_coq(scoped, unbound)} -> {self.right.to_coq(scoped, unbound)})"

    def to_smt(self) -> str:
        return f"(=> {self.left.to_smt()} {self.right.to_smt()})"


class RaisesExpr(BaseModel):
    """Exception postcondition: raises(ExcType, cond).

    Asserts that if the function raises an exception of type ExcType,
    the condition cond holds over the state at the raise point.

    In the outcome predicate, this becomes:
        | ORaise (VString "ExcType") s => cond_on_s
    """
    kind: Literal["raises"] = "raises"
    exc_type: str    # exception class name, e.g. "ValueError"
    cond: Expr       # condition that holds when this exception is raised

    def to_coq(self, scoped: bool = True, unbound: frozenset[str] = frozenset()) -> str:
        """Emit the Coq expression for the condition (always scoped -- raise state is s)."""
        return self.cond.to_coq(scoped=True, unbound=unbound)

    def to_coq_arm(self, unbound: frozenset[str] = frozenset()) -> str:
        """Emit a single match arm: | ORaise (VString \"ExcType\") s => cond."""
        cond_coq = self.cond.to_coq(scoped=True, unbound=unbound)
        return f'| ORaise (VString "{self.exc_type}"%string) s => {cond_coq}'

    def to_smt(self) -> str:
        return self.cond.to_smt()


class IsShape(BaseModel):
    """is_shape(obj, Type) — the object structurally matches the shape.

    Emits isVZ/isVString type guards for every field.  Auto-injected
    into preconditions from type annotations; also the caller obligation
    for every CCall with a typed parameter.
    """
    kind: Literal["is_shape"] = "is_shape"
    obj: str
    model_type: str

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        from .shape_ir import lookup_shape, is_shape_coq
        shape = lookup_shape(self.model_type)
        if shape:
            return is_shape_coq(self.obj, shape, scoped=scoped)
        return "True"

    def to_smt(self) -> str:
        return "true"


class IsValid(BaseModel):
    """is_valid(obj, Type) — the object satisfies all declared constraints.

    Expands to is_shape + Field(ge=0, le=100, ...) constraint conjunction.
    For validate_assignment=True models this is auto-tracked; for default
    mode the user writes it in contracts when constraint reasoning is needed.
    """
    kind: Literal["is_valid"] = "is_valid"
    obj: str
    model_type: str

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        from .shape_ir import lookup_shape, is_valid_coq
        shape = lookup_shape(self.model_type)
        if shape:
            return is_valid_coq(self.obj, shape, scoped=scoped)
        return "True"

    def to_smt(self) -> str:
        return "true"


class ReMatchExpr(BaseModel):
    """s.re_match("pattern") -- regex membership contract predicate.

    In scoped (postcondition) context compiles to:
      re_match (asString (s "subject"%string)) "pattern"

    In unscoped (precondition) context compiles to:
      re_match subject "pattern"

    The theory-SMT oracle recognises this form and dispatches to
    QF_SLIA via str.in_re + the sre_parse-based RegLan translator.
    """
    kind: Literal["re_match"] = "re_match"
    subject: str    # variable name, e.g. "phone"
    pattern: str    # Python regex pattern, e.g. "[0-9]{3}-[0-9]{3}-[0-9]{4}"

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        if scoped and self.subject not in unbound:
            subj = f'(asString (s "{self.subject}"%string))'
        else:
            subj = self.subject
        # Escape double-quotes inside the pattern for Coq string literals
        pat = self.pattern.replace('"', '\\"')
        # re_match is a Prop -- no = true needed
        return f're_match {subj} "{pat}"'

    def to_smt(self) -> str:
        return f"re_match_{self.subject}_{self.pattern}"


class ListEqExpr(BaseModel):
    """List literal equality: result == [a, b] or result != [].

    Currently compiles to length equality (len(result) == len(literal))
    since element-by-element comparison requires list-index support in
    the contract IR.  The node preserves the semantic intent so it can
    be upgraded to element-wise equality when that becomes available.
    """
    kind: Literal["list_eq"] = "list_eq"
    name: str          # left-hand list name, e.g. "result"
    op: str            # "=" or "<>"
    n_elements: int    # number of elements in the literal on the right

    def to_coq(self, scoped: bool = False, unbound: frozenset[str] = frozenset()) -> str:
        # Compiles to length comparison: (hget s "name"%string len_f) = n_elements
        key_ref = f's "{self.name}"%string' if scoped else self.name
        op_str = "=" if self.op == "=" else "<>"
        return f'(asZ (hget {key_ref} len_f) {op_str} {self.n_elements})'

    def to_smt(self) -> str:
        return f"({self.op} (len {self.name}) {self.n_elements})"


Expr = Union[Var, IntLit, BoolLit, BinOp, Logical, LenExpr, IndexExpr, DictLenExpr, DictCountExpr, AllExpr, AnyExpr, SliceLenExpr, MinExpr, MaxExpr, SumExpr, StrLitExpr, FloatExpr, TupleExpr, DictExpr, SetExpr, ImpliesExpr, RaisesExpr, IsShape, IsValid, ListEqExpr, ReMatchExpr]
