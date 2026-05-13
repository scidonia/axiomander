"""
Intermediate representation for contract expressions.

A small expression AST that compiles to both Coq Prop and SMT-LIB.
Replaces regex-based string parsing with structured code generation.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class Expr:
    """Base for IR expressions."""
    pass


@dataclass
class Var(Expr):
    name: str

    def to_coq(self, scoped: bool = False) -> str:
        if scoped:
            return f's "{self.name}"%string'
        return self.name

    def to_smt(self) -> str:
        return self.name


@dataclass
class IntLit(Expr):
    value: int

    def to_coq(self, scoped: bool = False) -> str:
        return str(self.value)

    def to_smt(self) -> str:
        return str(self.value)


@dataclass
class BoolLit(Expr):
    value: bool

    def to_coq(self, scoped: bool = False) -> str:
        return "True" if self.value else "False"

    def to_smt(self) -> str:
        return "true" if self.value else "false"


@dataclass
class BinOp(Expr):
    op: str  # +, -, *, /, mod, =, <=, >=, <, >
    left: Expr
    right: Expr

    def to_coq(self, scoped: bool = False) -> str:
        op_map = {"/": "/", "mod": "mod"}
        coq_op = op_map.get(self.op, self.op)
        return f"({self.left.to_coq(scoped)} {coq_op} {self.right.to_coq(scoped)})"

    def to_smt(self) -> str:
        op_map = {"mod": "mod", "/": "div"}
        smt_op = op_map.get(self.op, self.op)
        return f"({smt_op} {self.left.to_smt()} {self.right.to_smt()})"


@dataclass
class Logical(Expr):
    op: str  # and, or, not
    operands: list[Expr] = field(default_factory=list)

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


@dataclass
class LenExpr(Expr):
    """len(lst) — array length lookup."""
    name: str

    def to_coq(self, scoped: bool = False) -> str:
        if scoped:
            return f's "{self.name}._len"%string'
        return f"{self.name}__len"

    def to_smt(self) -> str:
        return f"{self.name}__len"


@dataclass
class IndexExpr(Expr):
    """lst[i] — array index lookup."""
    name: str
    index: Expr

    def to_coq(self, scoped: bool = False) -> str:
        if scoped:
            return f's (parray_key "{self.name}"%string {self.index.to_coq(False)})%string'
        return f"{self.name}___{self.index.to_coq(False)}"

    def to_smt(self) -> str:
        return f"{self.name}___{self.index.to_smt()}"


@dataclass
class DictLenExpr(Expr):
    """len(dict[key]) — dict value list length."""
    name: str
    key: Expr

    def to_coq(self, scoped: bool = False) -> str:
        key_str = self.key.to_coq(False)
        if scoped:
            return f's (parray_len_key (dict_key "{self.name}"%string ({key_str})))%string'
        return f"{self.name}_v_{key_str}__len"

    def to_smt(self) -> str:
        return f"{self.name}_v_{self.key.to_smt()}__len"


def formula_to_smt(invariant: Expr, exit_cond: Expr, postcondition: Expr, scaffold: Expr | None = None) -> str:
    """Generate an SMT-LIB file from the IR and return (source, variables)."""
    from .smt_export import _extract_vars

    # Collect vars from all sub-expressions
    inv_str = invariant.to_coq(scoped=False)
    exit_str = exit_cond.to_coq(scoped=False)
    post_str = postcondition.to_coq(scoped=False)
    scaff_str = scaffold.to_coq(scoped=False) if scaffold else ""

    vars_set = _extract_vars(inv_str, exit_str, post_str, scaff_str)

    lines = [
        "(set-logic QF_NIA)",
        "(set-option :produce-models true)",
    ]
    for v in sorted(vars_set):
        lines.append(f"(declare-fun {v} () Int)")

    lines.append(f"(assert {invariant.to_smt()})")
    lines.append(f"(assert {exit_cond.to_smt()})")
    if scaffold:
        lines.append(f"(assert {scaffold.to_smt()})")
    lines.append(f"(assert (not {postcondition.to_smt()}))")
    lines.append("(check-sat)")

    return "\n".join(lines)
