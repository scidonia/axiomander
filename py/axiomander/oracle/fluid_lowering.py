"""Fluid predicate lowerer: lambda_A^tot -> CoqTerm.

The single, total, type-directed reflection R that compiles contract_ir.Expr
nodes to Coq Prop strings.  Design: docs/fluid-lowerer-design.md.
Theory: docs/fluid-contract-language-theory.md, sections 1, 2, 9, 10, 11.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Callable, Optional

from axiomander.oracle.contract_ir import (  # Expr node types used by the lowerer
    AllExpr, AnyExpr, BinOp as IRBinOp, BoolLit, DictExpr,
    FloatExpr, ImpliesExpr, IntLit, Logical, MaxExpr,
    MinExpr, RaisesExpr, SetExpr, SliceLenExpr, StrLitExpr,
    TupleExpr, Var, HexStringExpr, StringContainsExpr,
    StringEqualsExpr, ReMatchExpr, IsValid, IsShape,
    FieldAccess, RecursorExpr,
)

# Shorthand for the dispatch handler signature.
_Handler = Callable[..., "CoqTerm"]


# --------------------------------------------------------------------------
# Types of the pure fragment (the reified type codes).
# --------------------------------------------------------------------------

class Ty(Enum):
    """The pure value types of lambda_A^tot.

    INT/BOOL/STR/FLOAT are scalars.  LIST/TUPLE/DICT/SET are the immutable
    structural values (LitList / LitTuple / LitDict / LitSet in
    coq/SnakeletExnLang.v).  PROP is the type of a finished Coq proposition
    (output of a comparison / connective / quantifier) -- distinct from BOOL
    (a sn_val).  Carrying the type lets coercions be derived rather than guessed.
    """
    INT = "int"
    BOOL = "bool"
    STR = "str"
    FLOAT = "float"
    LIST = "list"
    TUPLE = "tuple"
    DICT = "dict"
    SET = "set"
    PROP = "prop"
    UNKNOWN = "unknown"


# Type for a list-element type (the homogeneous element type of a LIST / SET /
# DICT).  None means the list type is not known (list of UNKNOWN).
ListElemTy = Optional[Ty]


# --------------------------------------------------------------------------
# CoqTerm: a lowered term carrying its inferred fragment type.
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class CoqTerm:
    """A lowered Coq term plus its inferred fragment type.

    `text` is the Coq surface syntax string.  `ty` drives downstream
    coercions -- when a term of type BOOL needs to become a Prop, we
    append `= true`; when a term of type INT appears in a float context,
    we wrap with `z2float`.
    """
    text: str
    ty: Ty

    @property
    def is_prop(self) -> bool:
        return self.ty is Ty.PROP

    def as_prop(self) -> CoqTerm:
        """If this term is a bool value, embed it into Prop via `= true`.

        A term already of type PROP is returned unchanged.  This is the
        type-directed version of the legacy `z_scope` positional flag.
        """
        if self.ty is Ty.PROP:
            return self
        if self.ty is Ty.BOOL:
            return CoqTerm(f"{self.text} = true", Ty.PROP)
        return CoqTerm(f"{self.text} <> 0", Ty.PROP)


class FluidLowerError(Exception):
    """Raised when a node is outside lambda_A^tot.

    Carries a concrete diagnostic naming the offending construct.  The
    caller (contract_linter / iris_pipeline) maps this to a Violation
    so the predicate is rejected at the boundary, never silently
    reflected into a malformed term.
    """


@dataclass(frozen=True)
class FluidViolation:
    """A diagnostic about a construct outside lambda_A^tot.

    `kind` is the contract_ir node kind.
    `message` says what construct is rejected and why.
    `is_rejection` = True means this blocks lowering; False means the
    node is stubbed to "True" (degraded) but lowering continues.
    """
    kind: str
    message: str
    is_rejection: bool = False


# ---------------------------------------------------------------------------
# Registry: kinds that are deliberately stubbed (out of pure fragment).
# Each entry explains why and what to do instead.
# ---------------------------------------------------------------------------

_STUB_KINDS: dict[str, str] = {
    "raises": "exception postconditions are handled upstream by the "
              "proof generator, not by the pure fragment",
    "opaque_term": "external observer calls are discharged via callee "
                   "contracts, not lowered inline",
    "rown": "resource ownership is handled by Iris spatial context, "
            "not by the pure fragment",
}

# Kinds that are in the dispatch table but produce "True" stubs.
_STUBBED = frozenset(_STUB_KINDS.keys())


def collect_violations(node, ctx: LowerCtx | None = None) -> list[FluidViolation]:
    """Walk an Expr tree and collect all lowering diagnostics.

    Returns a list of FluidViolation — one per node that either:
      - is handled by a stub (degraded to "True"), or
      - is genuinely outside lambda_A^tot (no dispatch entry).

    Nodes handled by proper (non-stub) clauses produce no diagnostics.
    This is the totality judgment's diagnostic output surface: the
    caller maps violations to user-facing messages.
    """
    violations: list[FluidViolation] = []

    def walk(n):
        kind: str = getattr(n, "kind", "")
        if not kind:
            return
        if kind in _STUBBED:
            violations.append(FluidViolation(
                kind=kind,
                message=f"'{kind}': {_STUB_KINDS[kind]}",
                is_rejection=False,
            ))
        # Known node kinds: walk children.
        children: list = []
        if kind == "binop":
            children = [getattr(n, "left", None), getattr(n, "right", None)]
        elif kind == "logical":
            children = list(getattr(n, "operands", []))
        elif kind in ("implies", "min", "max"):
            children = [getattr(n, "left", None), getattr(n, "right", None)]
        elif kind == "slice_len":
            children = [getattr(n, "start", None), getattr(n, "end", None)]
        elif kind in ("all", "any"):
            children = [getattr(n, "pred", None)]
            if getattr(n, "lower", None):
                children.append(n.lower)
            if getattr(n, "upper", None):
                children.append(n.upper)
        elif kind == "raises":
            children = [getattr(n, "cond", None)]
        for c in children:
            if c is not None and hasattr(c, "kind"):
                walk(c)

    walk(node)
    return violations


# --------------------------------------------------------------------------
# LowerCtx: the typing/lowering environment (carrier of the totality judgment).
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class LowerCtx:
    """Immutable lowering context threaded through the recursion.

    gamma:       name -> Ty for every bound variable / parameter.
    post_var:    the postcondition result variable (renamed to post_bound).
    post_bound:  the Coq binder the result variable renames to ("z"/"s"/"b"/"v").
    list_model:  Python list-param name -> Coq model name (e.g. xs -> M_xs).
    """
    gamma: dict[str, Ty] = field(default_factory=dict)
    post_var: str = ""
    post_bound: str = "z"
    list_model: dict[str, str] = field(default_factory=dict)
    list_elem_types: dict[str, ListElemTy] = field(default_factory=dict)

    def typ(self, name: str) -> Ty:
        """Return the type of a variable, or UNKNOWN if untyped."""
        return self.gamma.get(name, Ty.UNKNOWN)

    def elem_typ(self, name: str) -> ListElemTy:
        """Return the element type of a list variable, or None."""
        return self.list_elem_types.get(name)

    def bind(self, name: str, ty: Ty) -> "LowerCtx":
        """Return a child context with `name : ty` added.

        Used for quantifier binders (forall/exists).  The original ctx is
        unchanged -- LowerCtx is immutable (frozen dataclass).
        """
        g = dict(self.gamma)
        g[name] = ty
        return LowerCtx(
            gamma=g,
            post_var=self.post_var,
            post_bound=self.post_bound,
            list_model=self.list_model,
        )

    @property
    def in_postcondition(self) -> bool:
        return bool(self.post_var)


# --------------------------------------------------------------------------
# lower: the single, total, type-directed lowering function.
# --------------------------------------------------------------------------

def lower(node, ctx: LowerCtx, *, bool_mode: bool = False) -> CoqTerm:
    """Compile a contract_ir Expr to a typed CoqTerm.

    Matches on node.kind and dispatches to the appropriate clause handler.
    Each handler is a pure function (node, ctx) -> CoqTerm; the ctx carries
    the gamma, post_var, post_bound, and list_model threading.

    bool_mode=True produces bare Coq bool terms (for recursor lambda bodies):
    comparisons use Z.ltb/Z.leb/Z.eqb instead of (... = true), and logical
    connectives use andb/orb/negb instead of (/\\ / \\/ ~).
    """
    kind: str = getattr(node, "kind", "")
    dispatch: dict[str, _Handler] = {
        "var": _lower_var,
        "int": _lower_int,
        "bool": _lower_bool,
        "strlit": _lower_strlit,
        "float": _lower_float,
        "binop": _lower_binop,
        "logical": _lower_logical,
        "implies": _lower_implies,
        "min": _lower_min,
        "max": _lower_max,
        "slice_len": _lower_slice_len,
        "len": _lower_len,
        "all": _lower_all,
        "any": _lower_any,
        "recursor": _lower_recursor,
        "hex_string": _lower_hex_string,
        "string_contains": _lower_string_contains,
        "string_eq": _lower_string_eq,
        "re_match": _lower_re_match,
        "is_valid": _lower_is_valid,
        "is_shape": _lower_is_shape,
        "field_access": _lower_field_access,
        # Value-model closures (WP-4) — no longer stubbed.
        "index": _lower_index,
        "sum": _lower_sum,
        "tuple": _lower_tuple,
        "dict": _lower_dict_node,
        "set": _lower_set,
        "list_eq": _lower_list_eq,
        "dict_len": _lower_dict_len,
        "dict_count": _lower_dict_count,
        # Deliberate out-of-fragment nodes — neutral identity.
        "opaque_term": _lower_opaque,
        "rown": _lower_opaque,
        "raises": _lower_opaque,
        "predicate_call": _lower_predicate_call,
    }
    handler = dispatch.get(kind)
    if handler is None:
        raise FluidLowerError(
            f"node kind '{kind}' is outside lambda_A^tot. "
            f"Recognised kinds: {sorted(dispatch.keys())}")
    return handler(node, ctx, bool_mode=bool_mode)


# --------------------------------------------------------------------------
# Clause handlers — scalar core (WP-1).
# --------------------------------------------------------------------------

def _lower_var(node: Var, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    name = node.name
    ty = ctx.typ(name)
    if name == ctx.post_var or name == "result":
        name = ctx.post_bound
    if ty is Ty.FLOAT:
        return CoqTerm(f"z2float {name}", Ty.FLOAT)
    if ty is Ty.BOOL:
        return CoqTerm(f"({name} <> 0)", Ty.PROP)
    if ty is Ty.STR:
        return CoqTerm(name, Ty.STR)
    if ty is Ty.INT:
        return CoqTerm(name, Ty.INT)
    return CoqTerm(name, Ty.UNKNOWN)


def _lower_int(node: IntLit, _ctx: LowerCtx, **_kw: object) -> CoqTerm:
    return CoqTerm(str(node.value), Ty.INT)


def _lower_bool(node: BoolLit, _ctx: LowerCtx, **_kw: object) -> CoqTerm:
    return CoqTerm("true" if node.value else "false", Ty.BOOL)


def _lower_strlit(node: StrLitExpr, _ctx: LowerCtx, **_kw: object) -> CoqTerm:
    escaped = node.value.replace("\\", "\\\\").replace('"', '\\"')
    return CoqTerm(f'"{escaped}"%string', Ty.STR)


def _lower_float(node: FloatExpr, _ctx: LowerCtx, **_kw: object) -> CoqTerm:
    if node.value % 100 == 0:
        return CoqTerm(f"(z2float ({int(node.value // 100)}))", Ty.FLOAT)
    return CoqTerm(
        f"(PrimFloat.div (z2float ({node.value})) (z2float (100)))", Ty.FLOAT)


def _lower_implies(node: ImpliesExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    left = lower(node.left, ctx)
    right = lower(node.right, ctx)
    return CoqTerm(f"({left.text} -> {right.text})", Ty.PROP)


def _lower_min(node: MinExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    left = lower(node.left, ctx)
    right = lower(node.right, ctx)
    return CoqTerm(f"(Z.min ({left.text}) ({right.text}))", Ty.INT)


def _lower_max(node: MaxExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    left = lower(node.left, ctx)
    right = lower(node.right, ctx)
    return CoqTerm(f"(Z.max ({left.text}) ({right.text}))", Ty.INT)


def _lower_slice_len(node: SliceLenExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    s = lower(node.start, ctx).text if node.start else "0"
    e = lower(node.end, ctx).text if node.end else "0"
    return CoqTerm(f"({e} - {s})", Ty.INT)


def _lower_opaque(_node, _ctx: LowerCtx, **_kw: object) -> CoqTerm:
    return CoqTerm("True", Ty.PROP)


def _lower_predicate_call(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    """Call to a user-defined recursive predicate → Fixpoint application.

    e.g. is_sorted(xs) → is_sorted M_xs  (type BOOL).
    The Fixpoint definition is emitted separately in the proof preamble.
    """
    arg_strs = []
    for a in node.args:
        t = lower(a, ctx)
        name = t.text
        if name in ctx.list_model:
            name = ctx.list_model[name]
        arg_strs.append(name)
    return CoqTerm(f"({node.name} {' '.join(arg_strs)})", Ty.BOOL)


# ---------------------------------------------------------------------------
# _lower_len  (list / string length)
# ---------------------------------------------------------------------------

def _lower_len(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    name: str = node.name
    ty = ctx.typ(name)
    if name == ctx.post_var or name == "result":
        name = ctx.post_bound
    if ty is Ty.STR:
        return CoqTerm(
            f'Z.of_nat (String.length (match {name} with '
            f'LitString s => s | _ => ""%string end))', Ty.INT)
    if name in ctx.list_model:
        return CoqTerm(f"Z.of_nat (List.length {ctx.list_model[name]})", Ty.INT)
    return CoqTerm(f"Z.of_nat (List.length {name})", Ty.INT)


# ---------------------------------------------------------------------------
# _lower_logical
# ---------------------------------------------------------------------------

def _lower_logical(node: Logical, ctx: LowerCtx, *,
                   bool_mode: bool = False) -> CoqTerm:
    if bool_mode:
        return _lower_logical_bool(node, ctx)
    if node.op == "not":
        inner = lower(node.operands[0], ctx)
        return CoqTerm(f"~ ({inner.text})", Ty.PROP)
    sep = " /\\ " if node.op == "and" else " \\/ "
    parts = [lower(o, ctx).text for o in node.operands]
    return CoqTerm("(" + sep.join(parts) + ")", Ty.PROP)


def _lower_logical_bool(node: Logical, ctx: LowerCtx) -> CoqTerm:
    """Bool-mode logical: andb / orb / negb (for recursor lambdas)."""
    if node.op == "not":
        inner = lower(node.operands[0], ctx, bool_mode=True)
        return CoqTerm(f"negb ({inner.text})", Ty.BOOL)
    sep = " && " if node.op == "and" else " || "
    parts = [lower(o, ctx, bool_mode=True).text for o in node.operands]
    return CoqTerm("(" + sep.join(parts) + ")", Ty.BOOL)


# ---------------------------------------------------------------------------
# _lower_binop — type-directed comparisons.
# ---------------------------------------------------------------------------

_Z_CMP_PROP: dict[str, str] = {
    "<": "<?", "<=": "<=?", ">": "<?", ">=": "<=?",
    "=": "=?", "<>": "=?",
}
_Z_CMP_BOOL: dict[str, str] = {
    "<": "ltb", "<=": "leb", ">": "ltb", ">=": "leb",
    "=": "eqb", "<>": "eqb",
}


def _lower_binop(node: IRBinOp, ctx: LowerCtx, *,
                 bool_mode: bool = False) -> CoqTerm:
    left = lower(node.left, ctx)
    right = lower(node.right, ctx)

    if left.text == "True" or right.text == "True":
        ty = Ty.BOOL if bool_mode else Ty.PROP
        return CoqTerm("True", ty)

    l_ty = left.ty
    r_ty = right.ty
    is_float = (l_ty is Ty.FLOAT or r_ty is Ty.FLOAT)
    is_str = (l_ty is Ty.STR or r_ty is Ty.STR)

    if is_float:
        return _float_op_bool(node.op, _ensure_float(left),
                              _ensure_float(right), bool_mode, left, right)

    if is_str and node.op in ("=", "<>"):
        eq_op = "<>" if node.op == "<>" else "="
        eqb = f"(String.eqb {left.text} {right.text} {eq_op} true)"
        if bool_mode:
            op = "negb" if node.op == "<>" else ""
            inner = f"(String.eqb {left.text} {right.text})"
            return CoqTerm(f"{op}({inner})" if op else inner, Ty.BOOL)
        return CoqTerm(eqb, Ty.PROP)

    # --- Structural comparison (tuple, dict, set, list) ---
    if _is_structural(l_ty) or _is_structural(r_ty):
        return _structural_cmp(node.op, left.text, right.text, bool_mode)

    return _integer_op_bool(node.op, left.text, right.text, bool_mode)


def _integer_op_bool(op: str, l: str, r: str, bool_mode: bool) -> CoqTerm:
    if bool_mode:
        if op in _Z_CMP_BOOL:
            fn = _Z_CMP_BOOL[op]
            flipped = op in (">", ">=")
            a, b = (r, l) if flipped else (l, r)
            eqb = op in ("=", "<>")
            neg = "negb " if op == "<>" else ""
            tok = f"Z.{fn} {a} {b}" if not eqb else f"Z.{fn} {a} {b}"
            return CoqTerm(f"{neg}({tok})", Ty.BOOL)
        coq_op = {"/": "/", "mod": "mod"}.get(op, op)
        return CoqTerm(f"({l} {coq_op} {r})", Ty.INT)

    cmp_map = {
        "<": f"({l} <? {r}) = true",
        "<=": f"({l} <=? {r}) = true",
        ">": f"({r} <? {l}) = true",
        ">=": f"({r} <=? {l}) = true",
        "=": f"({l} =? {r}) = true",
        "<>": f"({l} =? {r}) <> true",
    }
    if op in cmp_map:
        return CoqTerm(cmp_map[op], Ty.PROP)
    coq_op = {"/": "/", "mod": "mod"}.get(op, op)
    return CoqTerm(f"({l} {coq_op} {r})", Ty.INT)


def _float_op_bool(op: str, l: str, r: str, bool_mode: bool,
                   left_term: CoqTerm, right_term: CoqTerm) -> CoqTerm:
    if op in _FLOAT_CMP:
        fn = _FLOAT_CMP[op]
        if bool_mode:
            return CoqTerm(f"({fn} ({l}) ({r}))", Ty.BOOL)
        return CoqTerm(f"({fn} ({l}) ({r})) = true", Ty.PROP)
    if op in _FLOAT_ARITH:
        fn = _FLOAT_ARITH[op]
        return CoqTerm(f"({fn} ({l}) ({r}))", Ty.FLOAT)
    raise FluidLowerError(f"unsupported float operator '{op}'")


_STRUCTURAL_TYPES = frozenset({Ty.LIST, Ty.TUPLE, Ty.DICT, Ty.SET})


def _is_structural(ty: Ty) -> bool:
    return ty in _STRUCTURAL_TYPES


def _structural_cmp(op: str, l_text: str, r_text: str,
                    bool_mode: bool) -> CoqTerm:
    neg = "negb " if op == "<>" else ""
    inner = f"(sn_val_eqb_full {l_text} {r_text})"
    if bool_mode:
        return CoqTerm(f"{neg}{inner}" if neg else inner, Ty.BOOL)
    eq_op = "<>" if op == "<>" else "="
    return CoqTerm(f"({inner} {eq_op} true)", Ty.PROP)


def _ensure_float(t: CoqTerm) -> str:
    if t.ty is Ty.FLOAT:
        return t.text
    return f"z2float ({t.text})"


_FLOAT_CMP: dict[str, str] = {
    "=": "PrimFloat.eqb",
    "<>": "(fun a b => negb (PrimFloat.eqb a b))",
    "<": "PrimFloat.ltb", "<=": "PrimFloat.leb",
    ">": "(fun a b => PrimFloat.ltb b a)",
    ">=": "(fun a b => PrimFloat.leb b a)",
}

_FLOAT_ARITH: dict[str, str] = {
    "+": "PrimFloat.add", "-": "PrimFloat.sub",
    "*": "PrimFloat.mul", "/": "PrimFloat.div",
}


# ---------------------------------------------------------------------------
# _lower_all / _lower_any  — bounded quantifiers.
# ---------------------------------------------------------------------------

def _lower_all(node: AllExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    # Range quantifier: forall (v : Z), lo <= v < hi -> P
    if node.lower is not None and node.upper is not None:
        child_ctx = ctx.bind(node.var, Ty.INT)
        lo = lower(node.lower, child_ctx).text
        hi = lower(node.upper, child_ctx).text
        p = lower(node.pred, child_ctx).text
        return CoqTerm(
            f"(forall ({node.var} : Z), {lo} <= {node.var} < {hi} -> {p})",
            Ty.PROP)
    # List quantifier: forallb over sn_val list
    list_name = ctx.list_model.get(node.lst, node.lst)
    elem_ty = ctx.elem_typ(node.lst)
    if elem_ty is not None:
        # Known element type — extract via pattern matching
        child_ctx = ctx.bind(node.var, Ty.INT)
        body = lower(node.pred, child_ctx, bool_mode=True)
        unwrapped = body.text.replace(node.var, "n")
        if elem_ty is Ty.STR:
            extract = "LitString n"
        elif elem_ty is Ty.FLOAT:
            extract = "LitFloat n"
        elif elem_ty is Ty.BOOL:
            extract = "LitBool n"
        else:
            extract = "LitInt n"
        lam = (f"(fun (_v : sn_val) => match _v with "
               f"{extract} => {unwrapped} | _ => false end)")
    else:
        # Unknown element type — keep as sn_val, let predicate dispatch
        child_ctx = ctx.bind(node.var, Ty.UNKNOWN)
        body = lower(node.pred, child_ctx, bool_mode=True)
        unwrapped = body.text.replace(node.var, "_v")
        lam = f"(fun (_v : sn_val) => {unwrapped})"
    return CoqTerm(
        f"(forallb {lam} {list_name} = true)", Ty.PROP)


def _lower_any(node: AnyExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    child_ctx = ctx.bind(node.var, Ty.INT)
    if node.lower is not None and node.upper is not None:
        from .contract_ir import _extract_int_lit, _subst_var
        lo_v = _extract_int_lit(node.lower)
        hi_v = _extract_int_lit(node.upper)
        if lo_v is not None and hi_v is not None and hi_v - lo_v <= 5:
            terms = []
            for i in range(lo_v, hi_v):
                subbed = _subst_var(node.pred, node.var, i)
                terms.append(f"({lower(subbed, child_ctx).text})")
            return CoqTerm(" \\/ ".join(terms) or "True", Ty.PROP)
        lo = lower(node.lower, child_ctx).text
        hi = lower(node.upper, child_ctx).text
        p = lower(node.pred, child_ctx).text
        return CoqTerm(
            f"(exists ({node.var} : Z), {lo} <= {node.var} < {hi} /\\ {p})",
            Ty.PROP)
    # List quantifier: existsb over sn_val list
    list_name = ctx.list_model.get(node.lst, node.lst)
    elem_ty = ctx.elem_typ(node.lst)
    if elem_ty is not None:
        child_ctx = ctx.bind(node.var, Ty.INT)
        body = lower(node.pred, child_ctx, bool_mode=True)
        unwrapped = body.text.replace(node.var, "n")
        if elem_ty is Ty.STR:
            extract = "LitString n"
        elif elem_ty is Ty.FLOAT:
            extract = "LitFloat n"
        elif elem_ty is Ty.BOOL:
            extract = "LitBool n"
        else:
            extract = "LitInt n"
        lam = (f"(fun (_v : sn_val) => match _v with "
               f"{extract} => {unwrapped} | _ => false end)")
    else:
        child_ctx = ctx.bind(node.var, Ty.UNKNOWN)
        body = lower(node.pred, child_ctx, bool_mode=True)
        unwrapped = body.text.replace(node.var, "_v")
        lam = f"(fun (_v : sn_val) => {unwrapped})"
    return CoqTerm(
        f"(existsb {lam} {list_name} = true)", Ty.PROP)


# ---------------------------------------------------------------------------
# String / hex / regex / field / shape / recursor predicates.
# ---------------------------------------------------------------------------

def _lower_recursor(node: RecursorExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    arg = ctx.list_model.get(node.arg, node.arg)
    return CoqTerm(f"Z.of_nat ({node.recursor} {node.predicate} {arg})", Ty.INT)


def _lower_hex_string(node: HexStringExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    var = ctx.post_bound if (node.name == ctx.post_var
                              or node.name == "result") else node.name
    return CoqTerm(
        f'(str_all_hex (match {var} with LitString raw => raw '
        f'| _ => ""%string end) = true)', Ty.PROP)


def _lower_string_contains(node: StringContainsExpr, ctx: LowerCtx,
                           **_kw: object) -> CoqTerm:
    op = "<>" if node.negated else "="
    needle_coq = f'"{node.needle}"%string'
    return CoqTerm(
        f"(str_contains_val (LitString {needle_coq}) "
        f"(str_to_lower_val {node.haystack}) {op} true)", Ty.PROP)


def _lower_string_eq(node: StringEqualsExpr, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    op = "<>" if node.negated else "="
    var_name = ctx.post_bound if (node.var == ctx.post_var
                                   or node.var == "result") else node.var
    return CoqTerm(
        f'(String.eqb {var_name} "{node.literal}"%string {op} true)', Ty.PROP)


def _lower_re_match(node: ReMatchExpr, _ctx: LowerCtx, **_kw: object) -> CoqTerm:
    pat = node.pattern.replace("\\", "\\\\").replace('"', '\\"')
    return CoqTerm(f're_match {node.subject} "{pat}"', Ty.PROP)


def _lower_is_valid(node: IsValid, _ctx: LowerCtx, **_kw: object) -> CoqTerm:
    from axiomander.oracle.shape_ir import lookup_shape, flat_fields
    shape = lookup_shape(node.model_type)
    if not shape:
        return CoqTerm("True", Ty.PROP)
    parts: list[str] = []
    for flat_key, f in flat_fields(shape, node.obj):
        key_scoped = f's "{flat_key}"%string'
        key_bare = flat_key
        for c in f.constraints:
            formatted = c.format(key_scoped=key_scoped, key_bare=key_bare)
            unscoped = formatted.replace(f"asZ ({key_scoped})", key_bare)
            unscoped = unscoped.replace(
                key_bare, f'model_field_Z {node.obj} "{f.name}"')
            parts.append(unscoped)
    return CoqTerm(
        " /\\ ".join(f"({p})" for p in parts) or "True", Ty.PROP)


def _lower_is_shape(_node, _ctx: LowerCtx, **_kw: object) -> CoqTerm:
    return CoqTerm("True", Ty.PROP)


def _lower_field_access(node: FieldAccess, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    obj = "v" if (ctx.in_postcondition and node.obj == "result") else node.obj
    return CoqTerm(f'model_field_Z {obj} "{node.field}"', Ty.INT)


# ---------------------------------------------------------------------------
# Value-model closures (WP-4) — structural literal constructors, indexing,
# list equality, dict model operations.
# ---------------------------------------------------------------------------

def _wrap_sn_val(t: CoqTerm) -> str:
    """Wrap a lowered term as its SnakeletExnLang constructor for use
    as an element of a structural literal (LitTuple, LitDict, LitSet, LitList)."""
    if t.ty is Ty.INT:
        return f"LitInt {t.text}"
    if t.ty is Ty.STR:
        return t.text  # already has "%string
    if t.ty is Ty.BOOL:
        return f"LitBool {t.text}"
    if t.ty is Ty.FLOAT:
        return f"LitFloat {t.text}"
    return t.text


def _lower_index(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    """List indexing for named list models: xs[i]."""
    name: str = node.name
    model = ctx.list_model.get(name, name)
    idx = lower(node.index, ctx)
    return CoqTerm(
        f"Z.of_nat (List.nth (Z.to_nat ({idx.text})) {model} 0)",
        Ty.INT)


def _lower_sum(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    """Sum over a named list: sum(xs) or fold_left Z.add 0 model."""
    name: str = node.name
    model = ctx.list_model.get(name, name)
    return CoqTerm(
        f"(List.fold_left Z.add 0 {model})",
        Ty.INT)


def _lower_tuple(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    els = [_wrap_sn_val(lower(e, ctx)) for e in node.elements]
    inner = " :: ".join(els + ["nil"]) if els else "nil"
    return CoqTerm(f"(LitTuple ({inner}))", Ty.TUPLE)


def _lower_dict_node(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    pairs = []
    for k, v in node.pairs:
        kw = _wrap_sn_val(lower(k, ctx))
        vw = _wrap_sn_val(lower(v, ctx))
        pairs.append(f"({kw}, {vw})")
    inner = " :: ".join(pairs + ["nil"]) if pairs else "nil"
    return CoqTerm(f"(LitDict ({inner}))", Ty.DICT)


def _lower_set(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    els = [_wrap_sn_val(lower(e, ctx)) for e in node.elements]
    inner = " :: ".join(els + ["nil"]) if els else "nil"
    return CoqTerm(f"(LitSet ({inner}))", Ty.SET)


def _lower_list_eq(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    """List equality: len(result) == n_elements."""
    op_str = "<>" if node.op == "<>" else "="
    # Resolve the list variable: use list_model for postcondition result
    if node.name == ctx.post_var or node.name == "result":
        name = ctx.list_model.get("result", "v")
    else:
        name = node.name
    return CoqTerm(
        f"(Z.of_nat (List.length {name}) {op_str} {node.n_elements})", Ty.PROP)


def _lower_dict_len(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    name: str = node.name
    model = ctx.list_model.get(name, name)
    return CoqTerm(f"Z.of_nat (List.length {model})", Ty.INT)


def _lower_dict_count(node, ctx: LowerCtx, **_kw: object) -> CoqTerm:
    name: str = node.name
    model = ctx.list_model.get(name, name)
    return CoqTerm(f"Z.of_nat (List.length {model})", Ty.INT)


# ---------------------------------------------------------------------------
# Pre/postcondition wrappers (compile_precondition / compile_postcondition).
# ---------------------------------------------------------------------------

def extract_forall_predicate(node) -> str:
    """Extract an sn_val->Prop predicate from a forallb precondition.

    Walks a contract_ir Expr looking for a list-quantifier AllExpr whose
    lst matches a known list model.  Returns the Forall predicate string
    suitable for wp_for_list_forall, or '' if none found.

    Example: all(x > 0 for x in xs) with list model {"xs": "M_xs"}
             → "(fun v => match v with LitInt n => Z.ltb 0 n = true | _ => False end)"
    """
    kind = getattr(node, "kind", "")
    if kind == "all":
        lst = getattr(node, "lst", "")
        if not lst:
            return ""
        # Build a LowerCtx to lower the predicate.  No list model needed
        # here — the predicate is over Z elements.
        pred = getattr(node, "pred", None)
        if pred is None:
            return ""
        var = node.var
        child_ctx = LowerCtx(gamma={var: Ty.INT})
        body = lower(pred, child_ctx, bool_mode=True)
        # body.text references var (the Python loop variable, e.g. "x").
        # The match binder is "n" — substitute var → n.
        body_text = body.text.replace(var, "n")
        return (f"(fun (_v : sn_val) => match _v with "
                f"LitInt n => {body_text} = true | _ => False end)")
    if kind == "logical":
        for o in getattr(node, "operands", []):
            pred = extract_forall_predicate(o)
            if pred:
                return pred
    return ""

_RESULT_KIND_WRAPPER: dict[str, tuple[str, str]] = {
    "int": ("Z", "LitInt"),
    "bool": ("bool", "LitBool"),
    "string": ("string", "LitString"),
}


def compile_precondition_fluid(node, ctx: LowerCtx) -> str:
    """Compile a precondition IR node to a bare Coq Prop string.

    If the lowered term is not already a PROP (e.g. a bare BOOL or INT),
    it is coerced via as_prop().
    """
    t = lower(node, ctx)
    if not t.is_prop:
        t = t.as_prop()
    return t.text


def compile_postcondition_fluid(node, ctx: LowerCtx, *,
                                result_kind: str = "int") -> str:
    """Compile a postcondition IR node to an Iris WP post Prop.

    Produces the shape finish_pure expects:
        int    -> exists z : Z, v = LitInt z /\ P[ret_var := z]
        bool   -> exists b : bool, v = LitBool b /\ P[ret_var := b]
        string -> exists s : string, v = LitString s /\ P[ret_var := s]

    When result_kind is not in the wrapper map, v is used directly
    (sn_val / structural result).
    """
    wrapper = _RESULT_KIND_WRAPPER.get(result_kind)
    if wrapper is None:
        # Structural / sn_val result — no unpacking.
        t = lower(node, ctx)
        return f"({t.text})"
    binder_ty, ctor = wrapper
    t = lower(node, ctx)
    if not t.is_prop:
        t = t.as_prop()
    return f"exists {ctx.post_bound} : {binder_ty}, v = {ctor} {ctx.post_bound} /\\ ({t.text})"
