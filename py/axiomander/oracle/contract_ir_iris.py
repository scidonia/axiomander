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
from axiomander.oracle.contract_ir import (
    AllExpr, AnyExpr, BinOp, BoolLit, DictCountExpr, DictExpr,
    DictLenExpr, Expr, FieldAccess, FloatExpr, ImpliesExpr, IndexExpr,
    IntLit, IsShape, IsValid, LenExpr, ListEqExpr, Logical, MaxExpr,
    MinExpr, OpaqueTerm, RaisesExpr, ReMatchExpr, RecursorExpr, ROwnExpr,
    SetExpr, SliceLenExpr, StrLitExpr, StringContainsExpr,
    StringEqualsExpr, SumExpr, TupleExpr, Var,
)


"""Contract IR to Iris Coq Prop compiler."""

# Module-level thread for list_model (avoids threading through the
# recursive iris_prop call chain — _binop / _logical lose it).
_LIST_MODEL: dict[str, str] = {}

# Module-level thread for the post-variable rename target.  Postconditions
# rename [post_var] to this bound name; defaults to "z" (integer results),
# but string/bool results use "s"/"b" so the existential binder matches the
# LitString/LitBool constructor.
_POST_BOUND: str = "z"

# Module-level set of float parameter names — _var wraps them with z2float
# so contract comparisons like x >= 0.0 compile to
# z2float x >= 0.0%float instead of the type-error Z >= float.
_FLOAT_PARAMS: set[str] = set()


def iris_prop(node: Expr, *,
              param_set: frozenset[str] = frozenset(),
              post_var: str = "",
              list_model: dict[str, str] | None = None,
              post_bound: str | None = None,
              float_params: set[str] | None = None) -> str:
    """Compile a contract_ir Expr to a pure Coq Prop for Iris.

    param_set: variable names that are NOT Iris context binders.
    post_var: if non-empty, rename this variable to [post_bound]
              (postconditions).
    list_model: mapping from Python list-parameter names to their
                Coq model names (e.g. {'xs': 'M_xs'}) for len(xs).
    post_bound: the bound-variable name [post_var] renames to (default
                "z"; "s" for string results, "b" for bool).  None means
                "keep the current module-level setting" so recursive
                calls from _binop / _logical preserve the chosen binder.
    """
    global _LIST_MODEL, _POST_BOUND
    if list_model is not None:
        _LIST_MODEL = list_model
    if post_bound is not None:
        _POST_BOUND = post_bound
    lm = _LIST_MODEL
    kind = node.kind
    dispatch = {
        "var": _var, "int": _int_lit, "bool": _bool_lit,
        "binop": _binop, "logical": _logical,
        "len": lambda n, ps, pv: _list_len(n, ps, pv, lm),
        "index": _placeholder, "dict_len": _placeholder,
        "dict_count": _placeholder, "all": _all, "any": _any,
        "slice_len": _slice_len, "min": _min, "max": _max,
        "sum": _placeholder, "float": _float, "strlit": _str_lit,
        "tuple": _placeholder, "dict": _placeholder, "set": _placeholder,
        "implies": _implies, "raises": _placeholder,
        "is_shape": _is_shape, "is_valid": _is_valid,
        "list_eq": _placeholder, "re_match": _re_match,
        "string_contains": _string_contains,
        "string_eq": _string_eq,
        "hex_string": _hex_string,
        "recursor": _recursor, "rown": _placeholder,
        "opaque_term": _placeholder,
        "field_access": _field_access,
    }
    # The "len" dispatch captures lm via closure.  For "binop" and
    # "logical" which recurse into iris_prop, the inner call does NOT
    # pass list_model, but that's fine: "len" nodes appear as direct
    # operands of binops, and the dispatch at the top of iris_prop
    # handles them before the binop's recursion reaches them.
    return dispatch[kind](node, param_set, post_var)


_STRING_PARAMS: set[str] = set()

_BOOL_PARAMS: set[str] = set()


def _list_len(n, ps, pv, list_model):
    """len(x) for a list or string parameter."""
    if n.name in _FLOAT_PARAMS:
        return "0"
    if n.name in _STRING_PARAMS:
        return f"Z.of_nat (String.length (match {n.name} with LitString s => s | _ => \"\"%string end))"
    if n.name in _LIST_MODEL:
        return f"Z.of_nat (List.length {_LIST_MODEL[n.name]})"
    return f"Z.of_nat (List.length {n.name})"


def _var(n, ps, pv):
    if n.name == pv or n.name == "result":
        return _POST_BOUND
    if n.name in _FLOAT_PARAMS:
        return f"z2float {n.name}"
    if n.name in _BOOL_PARAMS:
        return f"({n.name} <> 0)"
    return n.name


def _int_lit(n, ps, pv):
    return str(n.value)


def _bool_lit(n, ps, pv):
    return "true" if n.value else "false"


def _opaque_p(n: Expr) -> bool:
    """Check if an Expr tree contains an OpaqueTerm."""
    if getattr(n, "kind", None) == "opaque_term":
        return True
    if getattr(n, "kind", None) == "binop":
        return _opaque_p(n.left) or _opaque_p(n.right)
    if getattr(n, "kind", None) == "logical":
        return any(_opaque_p(o) for o in n.operands)
    if getattr(n, "kind", None) == "implies":
        return _opaque_p(n.left) or _opaque_p(n.right)
    return False


def _float_p(n: Expr) -> bool:
    """Check if an Expr represents a float value (literal or float-typed var)."""
    if getattr(n, "kind", None) == "float":
        return True
    if getattr(n, "kind", None) == "var":
        return getattr(n, "name", "") in _FLOAT_PARAMS
    return False


def _binop(n, ps, pv):
    z_scope = bool(pv)
    # Short-circuit: if either operand is an opaque DB observer, the whole
    # comparison is unknowable from local state; compile to True (identity).
    if _opaque_p(n.left) or _opaque_p(n.right):
        return "True"
    # --- Float-aware comparison / arithmetic ---
    is_float = _float_p(n.left) or _float_p(n.right)
    if is_float:
        left = iris_prop(n.left, param_set=ps, post_var=pv)
        right = iris_prop(n.right, param_set=ps, post_var=pv)
        # Ensure both sides are float: wrap Z vars with z2float
        if not _float_p(n.left):
            left = f"z2float ({left})"
        if not _float_p(n.right):
            right = f"z2float ({right})"
        float_cmp = {
            "=": "PrimFloat.eqb", "<>": "(fun a b => negb (PrimFloat.eqb a b))",
            "<": "PrimFloat.ltb", "<=": "PrimFloat.leb",
            ">": "(fun a b => PrimFloat.ltb b a)",
            ">=": "(fun a b => PrimFloat.leb b a)",
        }
        float_arith = {
            "+": "PrimFloat.add", "-": "PrimFloat.sub",
            "*": "PrimFloat.mul", "/": "PrimFloat.div",
        }
        if n.op in float_cmp:
            if z_scope:
                return f"({float_cmp[n.op]} ({left}) ({right})) = true"
            return f"({float_cmp[n.op]} ({left}) ({right}))"
        if n.op in float_arith:
            return f"({float_arith[n.op]} ({left}) ({right}))"
        # Fall through for unsupported float ops
    # --- Integer comparison / arithmetic (original code) ---
    if z_scope:
        if n.op == ">":
            left = iris_prop(n.left, param_set=ps, post_var=pv)
            right = iris_prop(n.right, param_set=ps, post_var=pv)
            return f"({right} <? {left}) = true"
        if n.op == ">=":
            left = iris_prop(n.left, param_set=ps, post_var=pv)
            right = iris_prop(n.right, param_set=ps, post_var=pv)
            return f"({right} <=? {left}) = true"
        if n.op == "<":
            left = iris_prop(n.left, param_set=ps, post_var=pv)
            right = iris_prop(n.right, param_set=ps, post_var=pv)
            return f"({left} <? {right}) = true"
        if n.op == "<=":
            left = iris_prop(n.left, param_set=ps, post_var=pv)
            right = iris_prop(n.right, param_set=ps, post_var=pv)
            return f"({left} <=? {right}) = true"
    else:
        if n.op in (">", "<", ">=", "<="):
            left = iris_prop(n.left, param_set=ps, post_var=pv)
            right = iris_prop(n.right, param_set=ps, post_var=pv)
            coq_op = {">": ">", "<": "<", ">=": ">=", "<=": "<="}[n.op]
            return f"({left} {coq_op} {right})"
    op_map = {"/": "/", "mod": "mod"}
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
    z_scope = bool(pv)
    if n.op == "not":
        inner = iris_prop(n.operands[0], param_set=ps, post_var=pv)
        return f"~ ({inner})"
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
    if n.lst:
        # Resolve the container variable through the full iris pipeline
        lst_var = iris_prop(Var(n.lst), param_set=ps, post_var=pv)
        # Replace bound variable with local binder _v (word-boundary safe)
        import re
        p_subst = re.sub(rf'\b{n.var}\b', '_v', p)
        return (
            f"(forallb (fun (_v : sn_val) => "
            f"match _v with LitInt _z => {p_subst} | _ => false end) "
            f"{lst_var} = true)"
        )
    return "True"


def _any(n, ps, pv):
    inner_ps = ps | {n.var}
    if n.lower is not None and n.upper is not None:
        # For small integer ranges, expand to disjunction (nia can handle \/)
        from .contract_ir import _extract_int_lit, _subst_var
        lo_v = _extract_int_lit(n.lower)
        hi_v = _extract_int_lit(n.upper)
        if lo_v is not None and hi_v is not None and hi_v - lo_v <= 5:
            terms = []
            for i in range(lo_v, hi_v):
                subbed = _subst_var(n.pred, n.var, i)
                terms.append(f"({iris_prop(subbed, param_set=inner_ps, post_var=pv)})")
            return " \\/ ".join(terms) if terms else "True"
        lo = iris_prop(n.lower, param_set=inner_ps, post_var=pv)
        hi = iris_prop(n.upper, param_set=inner_ps, post_var=pv)
        p = iris_prop(n.pred, param_set=inner_ps, post_var=pv)
        return f"(exists ({n.var} : Z), {lo} <= {n.var} < {hi} /\\ {p})"
    if n.lst:
        import re
        p = iris_prop(n.pred, param_set=inner_ps, post_var=pv)
        lst_var = iris_prop(Var(n.lst), param_set=ps, post_var=pv)
        p_subst = re.sub(rf'\b{n.var}\b', '_v', p)
        return (
            f"(existsb (fun (_v : sn_val) => "
            f"match _v with LitInt _z => {p_subst} | _ => false end) "
            f"{lst_var} = true)"
        )
    return "True"


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
    # Float literal: Z-encoded (value * 100).  Convert to Coq float
    # without relying on float_scope (which would shadow Z literals).
    v = float(n.value) / 100
    return f"(z2float ({int(n.value // 100)}))" if n.value % 100 == 0 else \
           f"(PrimFloat.div (z2float ({n.value})) (z2float (100)))"


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
    op = "<>" if n.negated else "="
    needle_coq = f'"{n.needle}"%string'
    return f"(str_contains_val (LitString {needle_coq}) (str_to_lower_val {n.haystack}) {op} true)"


def _string_eq(n, ps, pv):
    op = "<>" if n.negated else "="
    var = _POST_BOUND if n.var == pv else n.var
    return f'(String.eqb {var} "{n.literal}"%string {op} true)'


def _hex_string(n, ps, pv):
    var = _POST_BOUND if n.name == pv or n.name == "result" else n.name
    return f"(str_all_hex (match {var} with LitString raw => raw | _ => \"\"%string end) = true)"


def _recursor(n, ps, pv):
    arg = _LIST_MODEL.get(n.arg, n.arg)
    return f"Z.of_nat ({n.recursor} {n.predicate} {arg})"


def _is_valid(n, ps, pv):
    """is_valid(obj, Type) — field constraint conjunction from shape registry."""
    from axiomander.oracle.shape_ir import lookup_shape, flat_fields
    shape = lookup_shape(n.model_type)
    if not shape:
        return "True"
    parts: list[str] = []
    for flat_key, f in flat_fields(shape, n.obj):
        key_scoped = f's "{flat_key}"%string'
        key_bare = flat_key
        for c in f.constraints:
            formatted = c.format(key_scoped=key_scoped, key_bare=key_bare)
            # Remove IMP asZ(...) wrapper → bare key
            unscoped = formatted.replace(f"asZ ({key_scoped})", key_bare)
            # Replace bare flat key with Iris model_field_Z projection
            unscoped = unscoped.replace(key_bare,
                                         f'model_field_Z {n.obj} "{f.name}"')
            parts.append(unscoped)
    return " /\\ ".join(f"({p})" for p in parts) if parts else "True"


def _is_shape(n, ps, pv):
    """is_shape(obj, Type) — structural check.  For Iris, models are
    always well-typed at the sn_val level; field existence is enforced
    by the type system.  Compile to True."""
    return "True"


def _placeholder(n, ps, pv):
    return "True"


def _field_access(n, ps, pv):
    """Structural field projection for Pydantic model fields.
    In postcondition context (pv non-empty), 'result' is renamed
    to the raw WP binder 'v' (not the unpacked Z/bool/string bound
    variable)."""
    obj = "v" if (pv and n.obj == "result") else n.obj
    return f'model_field_Z {obj} "{n.field}"'


# -- Convenience: compile contracts from the linter ---------------------------

def _result_value_kind(node: Expr, ret_var: str) -> str:
    """Infer the SnakeletLang value constructor for the return value.

    Walks the postcondition IR looking for the way [ret_var] is compared:
      - against a string literal (StringEqualsExpr on ret_var, or a
        BinOp '='/'<>' whose other side is a StrLitExpr) -> "string"
      - against a bool                                    -> "bool"
      - otherwise (arithmetic / Z comparison)             -> "int"

    Returns one of "int" | "bool" | "string".
    """
    found: dict[str, Optional[str]] = {"kind": None}

    def walk(n: Expr) -> None:
        if found["kind"] is not None:
            return
        k = getattr(n, "kind", None)
        if k == "string_eq" and getattr(n, "var", None) == ret_var:
            found["kind"] = "string"
            return
        if k == "binop":
            left = getattr(n, "left", None)
            right = getattr(n, "right", None)
            op = getattr(n, "op", None)
            l_is_ret = (getattr(left, "kind", None) == "var"
                        and getattr(left, "name", None) == ret_var)
            r_is_ret = (getattr(right, "kind", None) == "var"
                        and getattr(right, "name", None) == ret_var)
            if op in ("=", "<>"):
                if l_is_ret and getattr(right, "kind", None) == "strlit":
                    found["kind"] = "string"
                    return
                if r_is_ret and getattr(left, "kind", None) == "strlit":
                    found["kind"] = "string"
                    return
                if l_is_ret and getattr(right, "kind", None) == "bool":
                    found["kind"] = "bool"
                    return
                if r_is_ret and getattr(left, "kind", None) == "bool":
                    found["kind"] = "bool"
                    return
            if left is not None:
                walk(left)
            if right is not None:
                walk(right)
            return
        if k == "logical":
            for o in getattr(n, "operands", []):
                walk(o)
            return
        if k == "implies":
            walk(getattr(n, "left"))
            walk(getattr(n, "right"))
            return

    walk(node)
    return found["kind"] or "int"


def _collect_vars(node: Expr) -> set[str]:
    """Collect all Var-name references in an Expr subtree."""
    out: set[str] = set()
    k = getattr(node, "kind", None)
    if k == "var":
        out.add(node.name)
    elif k == "binop":
        out.update(_collect_vars(node.left))
        out.update(_collect_vars(node.right))
    elif k == "logical":
        for o in getattr(node, "operands", []):
            out.update(_collect_vars(o))
    elif k == "implies":
        out.update(_collect_vars(node.left))
        out.update(_collect_vars(node.right))
    return out


# Per-kind wrapper: (Coq binder type, value constructor, post_var rename target)
_RESULT_KIND_WRAPPER = {
    "int": ("Z", "LitInt", "z"),
    "bool": ("bool", "LitBool", "b"),
    "string": ("string", "LitString", "s"),
    "sn_val": ("sn_val", "id", "v"),  # model/dict return — use v directly
}


def compile_postcondition(node: Expr, ret_var: str,
                         list_model: dict[str, str] | None = None,
                         result_kind: str | None = None,
                         ghost_resolver: dict[str, str] | None = None) -> str:
    r"""Compile a postcondition expression to an Iris WP post Prop.

    Produces the shape finish_pure expects, dispatched on the return
    value's constructor:
        int    -> exists z : Z, v = LitInt z /\ P[ret_var := z]
        bool   -> exists b : bool, v = LitBool b /\ P[ret_var := b]
        string -> exists s : string, v = LitString s /\ P[ret_var := s]

    If [ghost_resolver] is provided, Var nodes whose names are ghost
    variable names are UNWRAPPED to the ghost var name for the proof
    context (the resume from [destruct Hr] in the proof script provides
    the ghost value).  Full observer verification requires the
    invariant/ownership model (next layer).
    """
    kind = result_kind or _result_value_kind(node, ret_var)
    # sn_val result kind: no unpacking, v is used directly
    if kind == "sn_val":
        gh = ghost_resolver or {}
        ghost_vars_used = sorted(_collect_vars(node).intersection(gh.values()))
        ghost_binders = "".join(
            f"(exists ({gv} : Z), " for gv in ghost_vars_used)
        ghost_closers = "".join(")" for _ in ghost_vars_used)
        prop = iris_prop(node, post_var=ret_var, list_model=list_model,
                         post_bound="v")
        return f"({ghost_binders} ({prop}){ghost_closers})"
    binder_ty, ctor, bound = _RESULT_KIND_WRAPPER.get(
        kind, _RESULT_KIND_WRAPPER["int"])
    # Ghost vars referenced in the postcondition — nested inside the
    # result existential so finish_pure handles the result and leaves
    # the ghost var residual for per-branch ghost_close.
    gh = ghost_resolver or {}
    ghost_vars_used = sorted(_collect_vars(node).intersection(gh.values()))
    ghost_binders = "".join(
        f"(exists ({gv} : Z), " for gv in ghost_vars_used)
    ghost_closers = "".join(")" for _ in ghost_vars_used)
    prop = iris_prop(node, post_var=ret_var, list_model=list_model,
                     post_bound=bound)
    return (f"exists {bound} : {binder_ty}, v = {ctor} {bound} /\\ "
            f"({ghost_binders} ({prop}){ghost_closers})")


def compile_precondition(node: Expr,
                         list_model: dict[str, str] | None = None) -> str:
    """Compile a precondition expression to a bare Coq Prop."""
    return iris_prop(node, list_model=list_model)
