"""Iris Prop compilation for contract_ir nodes.

Compiles contract_ir.Expr nodes to pure Coq Prop strings suitable for
Iris WP pre/postconditions (bare Z variables, no state accessors).
Compiles to the same idioms as the existing to_coq(scoped=False) where
the semantics match, diverging only where the IMP state model (s "x",
asZ, hget) is inapplicable.

Phase-3 nodes (list/dict/set/index operations, exceptions,
Pydantic shapes) compile to "True" — they need SnakeletLang value-model
support that isn't wired yet.  String comparisons, regex membership,
Z quantifiers over ranges, recursors, and min/max compile correctly.

SMT escalation: nodes that emit "True" mechanically are invisible to
lia.  When a full contract (with list/set/string operations) needs to
be checked, the existing .to_smt() path through smt_export/theory_smt
still works — this module only handles the Coq Prop side.
"""

from __future__ import annotations

from typing import Optional
from oracle.contract_ir import (
    AllExpr, AnyExpr, BinOp, BoolLit, DictCountExpr, DictExpr,
    DictLenExpr, Expr, FloatExpr, ImpliesExpr, IndexExpr, IntLit,
    IsShape, IsValid, LenExpr, ListEqExpr, Logical, MaxExpr, MinExpr,
    RaisesExpr, ReMatchExpr, RecursorExpr, ROwnExpr, SetExpr,
    SliceLenExpr, StrLitExpr, StringContainsExpr, StringEqualsExpr,
    SumExpr, TupleExpr, Var,
)


def iris_prop(node: Expr, *,
              param_set: frozenset[str] = frozenset(),
              post_var: str = "") -> str:
    """Compile a contract_ir Expr to a pure Coq Prop for Iris.

    param_set: variable names that are NOT Iris context binders
               (quantifier-bound variables).
    post_var: if non-empty, rename this variable to 'z' in the output
              (used for postconditions where the return value is
              re-bound existentially).
    """
    kind = node.kind
    dispatch = {
        "var": _var, "int": _int_lit, "bool": _bool_lit,
        "binop": _binop, "logical": _logical,
        "len": _placeholder, "index": _placeholder,
        "dict_len": _placeholder, "dict_count": _placeholder,
        "all": _all, "any": _any, "slice_len": _slice_len,
        "min": _min, "max": _max, "sum": _placeholder,
        "float": _float, "strlit": _str_lit,
        "tuple": _placeholder, "dict": _placeholder, "set": _placeholder,
        "implies": _implies, "raises": _placeholder,
        "is_shape": _placeholder, "is_valid": _placeholder,
        "list_eq": _placeholder, "re_match": _re_match,
        "string_contains": _string_contains,
        "string_eq": _string_eq,
        "recursor": _recursor, "rown": _placeholder,
    }
    return dispatch[kind](node, param_set, post_var)


def _var(n, ps, pv):
    if n.name == pv:
        return "z"
    return n.name


def _int_lit(n, ps, pv):
    return str(n.value)


def _bool_lit(n, ps, pv):
    return "True" if n.value else "False"


def _binop(n, ps, pv):
    op_map = {"/": "/", "mod": "mod", "<>": "<>", "=": "="}
    coq_op = op_map.get(n.op, n.op)
    left = iris_prop(n.left, param_set=ps, post_var=pv)
    right = iris_prop(n.right, param_set=ps, post_var=pv)
    is_str = getattr(n.right, "kind", None) == "strlit"
    if is_str and n.op == "=":
        rlit = _str_lit(n.right, ps, pv)
        return f"(String.eqb {left} {rlit} = true)"
    if is_str and n.op == "<>":
        rlit = _str_lit(n.right, ps, pv)
        return f"(String.eqb {left} {rlit} <> true)" 
    return f"({left} {coq_op} {right})"


def _logical(n, ps, pv):
    if n.op == "not":
        return f"~ ({iris_prop(n.operands[0], param_set=ps, post_var=pv)})"
    sep = " /\\ " if n.op == "and" else " \\/ "
    return "(" + sep.join(iris_prop(o, param_set=ps, post_var=pv)
                          for o in n.operands) + ")"


def _all(n, ps, pv):
    inner_ps = ps | {n.var}
    p = iris_prop(n.pred, param_set=inner_ps, post_var=pv)
    if n.lower is not None and n.upper is not None:
        lo = iris_prop(n.lower, param_set=inner_ps, post_var=pv)
        hi = iris_prop(n.upper, param_set=inner_ps, post_var=pv)
        return f"(forall ({n.var} : Z), {lo} <= {n.var} < {hi} -> {p})"
    return "True"  # phase 3: forall over lists in Iris


def _any(n, ps, pv):
    inner_ps = ps | {n.var}
    p = iris_prop(n.pred, param_set=inner_ps, post_var=pv)
    if n.lower is not None and n.upper is not None:
        lo = iris_prop(n.lower, param_set=inner_ps, post_var=pv)
        hi = iris_prop(n.upper, param_set=inner_ps, post_var=pv)
        return f"(exists ({n.var} : Z), {lo} <= {n.var} < {hi} /\\ {p})"
    return "True"  # phase 3: exists over lists in Iris


def _slice_len(n, ps, pv):
    s = iris_prop(n.start, param_set=ps, post_var=pv) if n.start else "0"
    e = iris_prop(n.end, param_set=ps, post_var=pv) if n.end else "0"
    return f"({e} - {s})"


def _min(n, ps, pv):
    left = iris_prop(n.left, param_set=ps, post_var=pv)
    right = iris_prop(n.right, param_set=ps, post_var=pv)
    return f"(Z.min ({left}) ({right}))"


def _max(n, ps, pv):
    left = iris_prop(n.left, param_set=ps, post_var=pv)
    right = iris_prop(n.right, param_set=ps, post_var=pv)
    return f"(Z.max ({left}) ({right}))"


def _float(n, ps, pv):
    return str(n.value)


def _str_lit(n, ps, pv):
    escaped = n.value.replace("\\", "\\\\").replace('"', '\\"')
    return f'"{escaped}"%string'


def _implies(n, ps, pv):
    left = iris_prop(n.left, param_set=ps, post_var=pv)
    right = iris_prop(n.right, param_set=ps, post_var=pv)
    return f"({left} -> {right})"


def _re_match(n, ps, pv):
    subj = n.subject
    pat = n.pattern.replace("\\", "\\\\").replace('"', '\\"')
    return f're_match {subj} "{pat}"'


def _string_contains(n, ps, pv):
    op = "=" if n.negated else "<>"
    return f"(String.index 0 {n.needle} {n.haystack} {op} None)"


def _string_eq(n, ps, pv):
    op = "<>" if n.negated else "="
    return f'(String.eqb {n.var} "{n.literal}"%string {op} true)'


def _recursor(n, ps, pv):
    return f"({n.recursor} {n.predicate} {n.arg})"


def _placeholder(n, ps, pv):
    return "True"


# -- Convenience: compile contracts from the linter ---------------------------

def compile_postcondition(node: Expr, ret_var: str) -> str:
    r"""Compile a postcondition expression to an Iris WP post Prop.

    Produces the shape finish_pure expects:
        exists z : Z, v = LitInt z /\ P[ret_var := z]
    """
    prop = iris_prop(node, post_var=ret_var)
    return f"exists z : Z, v = LitInt z /\\ ({prop})"


def compile_precondition(node: Expr) -> str:
    """Compile a precondition expression to a bare Coq Prop."""
    return iris_prop(node)
