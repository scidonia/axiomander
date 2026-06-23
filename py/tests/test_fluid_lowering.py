"""Unit tests for fluid_lowering: types, LowerCtx, CoqTerm (WP-0)
and scalar core lowering clauses (WP-1).
"""

import pytest

from axiomander.oracle.contract_ir import (
    AllExpr,
    AnyExpr,
    BinOp,
    BoolLit,
    FieldAccess,
    FloatExpr,
    HexStringExpr,
    ImpliesExpr,
    IntLit,
    IsShape,
    IsValid,
    LenExpr,
    Logical,
    MaxExpr,
    MinExpr,
    OpaqueTerm,
    RecursorExpr,
    ReMatchExpr,
    SliceLenExpr,
    StringContainsExpr,
    StringEqualsExpr,
    StrLitExpr,
    Var,
)
from axiomander.oracle.fluid_lowering import (
    CoqTerm,
    FluidLowerError,
    FluidViolation,
    LowerCtx,
    Ty,
    collect_violations,
    compile_postcondition_fluid,
    compile_precondition_fluid,
    lower,
)


# ---------------------------------------------------------------------------
# Ty
# ---------------------------------------------------------------------------

def test_ty_enum_values():
    assert Ty.INT.value == "int"
    assert Ty.BOOL.value == "bool"
    assert Ty.STR.value == "str"
    assert Ty.FLOAT.value == "float"
    assert Ty.LIST.value == "list"
    assert Ty.TUPLE.value == "tuple"
    assert Ty.DICT.value == "dict"
    assert Ty.SET.value == "set"
    assert Ty.PROP.value == "prop"
    assert Ty.UNKNOWN.value == "unknown"


def test_ty_prop_distinct_from_bool():
    """PROP and BOOL are different types -- comparisons produce PROP, values are BOOL."""
    assert Ty.PROP is not Ty.BOOL
    assert Ty.PROP is not Ty.INT


# ---------------------------------------------------------------------------
# CoqTerm
# ---------------------------------------------------------------------------

def test_coqterm_is_prop():
    assert CoqTerm("(a <? b) = true", Ty.PROP).is_prop is True
    assert CoqTerm("a", Ty.INT).is_prop is False
    assert CoqTerm("true", Ty.BOOL).is_prop is False


def test_coqterm_as_prop_idempotent():
    """as_prop on an already-PROP term is identity."""
    t = CoqTerm("(a <? b) = true", Ty.PROP)
    assert t.as_prop() is t


def test_coqterm_bool_as_prop():
    """A BOOL value becomes `= true` when lifted to PROP."""
    t = CoqTerm("P", Ty.BOOL)
    assert t.as_prop() == CoqTerm("P = true", Ty.PROP)


def test_coqterm_int_as_prop():
    """An INT value becomes `<> 0` when lifted to PROP (non-zero truthiness)."""
    t = CoqTerm("x", Ty.INT)
    assert t.as_prop() == CoqTerm("x <> 0", Ty.PROP)


def test_coqterm_frozen():
    """CoqTerm is frozen -- cannot be mutated."""
    t = CoqTerm("x", Ty.INT)
    with pytest.raises(Exception):
        t.text = "y"
    with pytest.raises(Exception):
        t.ty = Ty.BOOL


# ---------------------------------------------------------------------------
# FluidLowerError
# ---------------------------------------------------------------------------

def test_fluiderror_is_exception():
    assert issubclass(FluidLowerError, Exception)


def test_fluiderror_carries_message():
    msg = "predicate 'f' recurses on g(xs) which is not a sub-structure of xs"
    e = FluidLowerError(msg)
    assert str(e) == msg


# ---------------------------------------------------------------------------
# LowerCtx -- construction, immutability, type lookup
# ---------------------------------------------------------------------------

def test_ctx_empty_defaults():
    ctx = LowerCtx()
    assert ctx.gamma == {}
    assert ctx.post_var == ""
    assert ctx.post_bound == "z"
    assert ctx.list_model == {}
    assert not ctx.in_postcondition


def test_ctx_with_gamma():
    ctx = LowerCtx(gamma={"x": Ty.INT, "xs": Ty.LIST})
    assert ctx.typ("x") == Ty.INT
    assert ctx.typ("xs") == Ty.LIST
    assert ctx.typ("nonexistent") == Ty.UNKNOWN


def test_ctx_with_postcondition():
    ctx = LowerCtx(post_var="result", post_bound="s")
    assert ctx.in_postcondition is True
    assert ctx.post_var == "result"
    assert ctx.post_bound == "s"


def test_ctx_with_list_model():
    ctx = LowerCtx(list_model={"xs": "M_xs", "ys": "M_ys"})
    assert ctx.list_model["xs"] == "M_xs"
    assert ctx.list_model.get("nonexistent") is None


# ---------------------------------------------------------------------------
# LowerCtx -- bind (immutability)
# ---------------------------------------------------------------------------

def test_ctx_bind_adds_binding():
    ctx = LowerCtx(gamma={"x": Ty.INT})
    child = ctx.bind("v", Ty.LIST)
    # Child has the new binding.
    assert child.typ("v") == Ty.LIST
    assert child.typ("x") == Ty.INT  # inherited
    # Parent is unchanged.
    assert ctx.typ("v") == Ty.UNKNOWN


def test_ctx_bind_shadows():
    ctx = LowerCtx(gamma={"x": Ty.INT})
    child = ctx.bind("x", Ty.STR)
    assert child.typ("x") == Ty.STR
    assert ctx.typ("x") == Ty.INT  # original unmodified


def test_ctx_bind_is_frozen():
    """LowerCtx fields cannot be reassigned (frozen dataclass).

    Note: the dict *values* of gamma/list_model can be mutated in-place
    (Python dicts are always mutable).  bind() returns a new ctx with
    a fresh dict rather than mutating in-place.
    """
    ctx = LowerCtx()
    with pytest.raises(Exception):
        ctx.gamma = {"x": Ty.INT}  # field reassignment is blocked
    with pytest.raises(Exception):
        ctx.post_var = "v"


def test_ctx_bind_preserves_post():
    ctx = LowerCtx(post_var="result", post_bound="b", list_model={"xs": "M_xs"})
    child = ctx.bind("v", Ty.LIST)
    assert child.post_var == "result"
    assert child.post_bound == "b"
    assert child.list_model == {"xs": "M_xs"}
    assert child.in_postcondition is True


def test_ctx_bind_returns_new_instance():
    ctx = LowerCtx()
    child = ctx.bind("x", Ty.INT)
    assert child is not ctx
    assert isinstance(child, LowerCtx)


# =========================================================================
# WP-1: Scalar core clause handlers
# =========================================================================

_SIMPLE_CTX = LowerCtx(gamma={"x": Ty.INT, "y": Ty.INT, "ok": Ty.BOOL, "name": Ty.STR})
_POST_CTX = LowerCtx(gamma={"x": Ty.INT, "ok": Ty.BOOL, "f": Ty.FLOAT,
                              "result": Ty.INT},
                     post_var="result", post_bound="z")


# ---------------------------------------------------------------------------
# _lower_var
# ---------------------------------------------------------------------------

def test_lower_var_int():
    t = lower(Var(kind="var", name="x"), _SIMPLE_CTX)
    assert t == CoqTerm("x", Ty.INT)


def test_lower_var_unknown():
    t = lower(Var(kind="var", name="unknown"), LowerCtx())
    assert t == CoqTerm("unknown", Ty.UNKNOWN)


def test_lower_var_result_renamed():
    """result is renamed to post_bound (z) in postcondition context."""
    t = lower(Var(kind="var", name="result"), _POST_CTX)
    assert t == CoqTerm("z", Ty.INT)  # result has type INT in gamma


def test_lower_var_bool():
    t = lower(Var(kind="var", name="ok"), _SIMPLE_CTX)
    assert t == CoqTerm("(ok <> 0)", Ty.PROP)


def test_lower_var_float():
    t = lower(Var(kind="var", name="f"), _POST_CTX)
    assert t == CoqTerm("z2float f", Ty.FLOAT)


def test_lower_var_str():
    t = lower(Var(kind="var", name="name"), _SIMPLE_CTX)
    assert t == CoqTerm("name", Ty.STR)


# ---------------------------------------------------------------------------
# literal nodes
# ---------------------------------------------------------------------------

def test_lower_int():
    t = lower(IntLit(kind="int", value=42), _SIMPLE_CTX)
    assert t == CoqTerm("42", Ty.INT)


def test_lower_int_negative():
    t = lower(IntLit(kind="int", value=-5), _SIMPLE_CTX)
    assert t == CoqTerm("-5", Ty.INT)


def test_lower_bool_true():
    t = lower(BoolLit(kind="bool", value=True), _SIMPLE_CTX)
    assert t == CoqTerm("true", Ty.BOOL)


def test_lower_bool_false():
    t = lower(BoolLit(kind="bool", value=False), _SIMPLE_CTX)
    assert t == CoqTerm("false", Ty.BOOL)


def test_lower_strlit():
    t = lower(StrLitExpr(kind="strlit", value='hello'), _SIMPLE_CTX)
    assert t == CoqTerm('"hello"%string', Ty.STR)


def test_lower_strlit_escaped():
    t = lower(StrLitExpr(kind="strlit", value='a"b'), _SIMPLE_CTX)
    assert t == CoqTerm('"a\\"b"%string', Ty.STR)


def test_lower_float_whole():
    t = lower(FloatExpr(kind="float", value=300), _SIMPLE_CTX)
    assert t == CoqTerm("(z2float (3))", Ty.FLOAT)


def test_lower_float_fractional():
    t = lower(FloatExpr(kind="float", value=31416), _SIMPLE_CTX)
    assert t == CoqTerm(
        "(PrimFloat.div (z2float (31416)) (z2float (100)))", Ty.FLOAT)


# ---------------------------------------------------------------------------
# _lower_implies
# ---------------------------------------------------------------------------

def test_lower_implies():
    left = Var(kind="var", name="x")
    right = Var(kind="var", name="y")
    node = ImpliesExpr(kind="implies", left=left, right=right)
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("(x -> y)", Ty.PROP)


# ---------------------------------------------------------------------------
# _lower_min / _lower_max
# ---------------------------------------------------------------------------

def test_lower_min():
    node = MinExpr(kind="min",
                   left=IntLit(kind="int", value=3),
                   right=IntLit(kind="int", value=7))
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("(Z.min (3) (7))", Ty.INT)


def test_lower_max():
    node = MaxExpr(kind="max",
                   left=IntLit(kind="int", value=3),
                   right=IntLit(kind="int", value=7))
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("(Z.max (3) (7))", Ty.INT)


# ---------------------------------------------------------------------------
# _lower_slice_len
# ---------------------------------------------------------------------------

def test_lower_slice_len_both():
    node = SliceLenExpr(kind="slice_len",
                        name="lst",
                        start=IntLit(kind="int", value=2),
                        end=IntLit(kind="int", value=10))
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("(10 - 2)", Ty.INT)


def test_lower_slice_len_start_only():
    node = SliceLenExpr(kind="slice_len",
                        name="lst",
                        start=IntLit(kind="int", value=2),
                        end=None)
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("(0 - 2)", Ty.INT)


# ---------------------------------------------------------------------------
# _lower_logical
# ---------------------------------------------------------------------------

def test_lower_logical_and():
    a = Var(kind="var", name="x")
    b = Var(kind="var", name="y")
    node = Logical(kind="logical", op="and", operands=[a, b])
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("(x /\\ y)", Ty.PROP)


def test_lower_logical_or():
    node = Logical(kind="logical", op="or",
                   operands=[Var(kind="var", name="x"),
                             Var(kind="var", name="y")])
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("(x \\/ y)", Ty.PROP)


def test_lower_logical_not():
    node = Logical(kind="logical", op="not",
                   operands=[Var(kind="var", name="x")])
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("~ (x)", Ty.PROP)


def test_lower_logical_ternary_and():
    nodes: list = [Var(kind="var", name="a"),  # type: ignore[assignment]
                   Var(kind="var", name="b"),
                   Var(kind="var", name="c")]
    node = Logical(kind="logical", op="and", operands=nodes)  # type: ignore[arg-type]
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("(a /\\ b /\\ c)", Ty.PROP)


# ---------------------------------------------------------------------------
# _lower_binop — type-directed comparisons
# ---------------------------------------------------------------------------

def _binop(op, left, right):
    return BinOp(kind="binop", op=op, left=left, right=right)


_INT = lambda v: IntLit(kind="int", value=v)
_VAR = lambda n: Var(kind="var", name=n)
_STR = lambda v: StrLitExpr(kind="strlit", value=v)


def test_binop_int_eq():
    t = lower(_binop("=", _VAR("x"), _INT(5)), _SIMPLE_CTX)
    assert t == CoqTerm("(x =? 5) = true", Ty.PROP)


def test_binop_int_lt():
    t = lower(_binop("<", _VAR("x"), _INT(10)), _SIMPLE_CTX)
    assert t == CoqTerm("(x <? 10) = true", Ty.PROP)


def test_binop_int_le():
    t = lower(_binop("<=", _INT(0), _VAR("x")), _SIMPLE_CTX)
    assert t == CoqTerm("(0 <=? x) = true", Ty.PROP)


def test_binop_int_gt():
    t = lower(_binop(">", _VAR("x"), _INT(0)), _SIMPLE_CTX)
    assert t == CoqTerm("(0 <? x) = true", Ty.PROP)


def test_binop_int_ge():
    t = lower(_binop(">=", _VAR("x"), _INT(0)), _SIMPLE_CTX)
    assert t == CoqTerm("(0 <=? x) = true", Ty.PROP)


def test_binop_int_neq():
    t = lower(_binop("<>", _VAR("x"), _INT(0)), _SIMPLE_CTX)
    assert t == CoqTerm("(x =? 0) <> true", Ty.PROP)


def test_binop_int_arith():
    t = lower(_binop("+", _VAR("x"), _INT(3)), _SIMPLE_CTX)
    assert t == CoqTerm("(x + 3)", Ty.INT)


def test_binop_int_div():
    t = lower(_binop("/", _VAR("x"), _INT(2)), _SIMPLE_CTX)
    assert t == CoqTerm("(x / 2)", Ty.INT)


def test_binop_int_mod():
    t = lower(_binop("mod", _VAR("x"), _INT(2)), _SIMPLE_CTX)
    assert t == CoqTerm("(x mod 2)", Ty.INT)


def test_binop_str_eq():
    t = lower(_binop("=", _STR("abc"), _STR("xyz")), LowerCtx())
    assert t == CoqTerm(
        '(String.eqb "abc"%string "xyz"%string = true)', Ty.PROP)


def test_binop_str_neq():
    t = lower(_binop("<>", _STR("abc"), _STR("xyz")), LowerCtx())
    assert t == CoqTerm(
        '(String.eqb "abc"%string "xyz"%string <> true)', Ty.PROP)


def test_binop_float_cmp():
    fctx = LowerCtx(gamma={"x": Ty.FLOAT, "y": Ty.FLOAT})
    t = lower(_binop("<", _VAR("x"), _VAR("y")), fctx)
    assert t == CoqTerm(
        "(PrimFloat.ltb (z2float x) (z2float y)) = true", Ty.PROP)


def test_binop_float_int_coercion():
    """INT operand in float context gets z2float wrapping."""
    fctx = LowerCtx(gamma={"x": Ty.FLOAT})
    t = lower(_binop("=", _VAR("x"), _INT(0)), fctx)
    assert t == CoqTerm(
        "(PrimFloat.eqb (z2float x) (z2float (0))) = true", Ty.PROP)


def test_binop_opaque_shortcircuit():
    """When either operand is the legacy 'True' stub, comparison short-circuits."""
    node = BinOp(kind="binop", op="=",
                 left=Var(kind="var", name="x"),
                 right=OpaqueTerm(kind="opaque_term", name="opq"))  # type: ignore[arg-type]
    t = lower(node, _SIMPLE_CTX)
    assert t == CoqTerm("True", Ty.PROP)


# ---------------------------------------------------------------------------
# Rejection of non-scalar nodes (totality gate stub — WP-3 extends this)
# ---------------------------------------------------------------------------

def test_lower_rejects_unknown_kind():
    class Bogus:
        kind = "whale"

    with pytest.raises(FluidLowerError) as exc:
        lower(Bogus(), LowerCtx())
    assert "whale" in str(exc.value)
    assert "outside lambda_A^tot" in str(exc.value)


# =========================================================================
# WP-2: Len, quantifiers, string/value predicates, field access.
# =========================================================================

_LIST_CTX = LowerCtx(list_model={"xs": "M_xs", "ys": "M_ys"})
_LIST_CTX_TYPED = LowerCtx(
    gamma={"xs": Ty.LIST, "name": Ty.STR},
    list_model={"xs": "M_xs"})


# ---------------------------------------------------------------------------
# _lower_len
# ---------------------------------------------------------------------------

def test_lower_len_list():
    t = lower(LenExpr(kind="len", name="xs"), _LIST_CTX)
    assert t == CoqTerm("Z.of_nat (List.length M_xs)", Ty.INT)


def test_lower_len_list_no_model():
    t = lower(LenExpr(kind="len", name="ys"), LowerCtx())
    assert t == CoqTerm("Z.of_nat (List.length ys)", Ty.INT)


def test_lower_len_string():
    ctx = LowerCtx(gamma={"name": Ty.STR})
    t = lower(LenExpr(kind="len", name="name"), ctx)
    assert "String.length" in t.text
    assert "LitString" in t.text
    assert t.ty is Ty.INT


# ---------------------------------------------------------------------------
# _lower_all — range + list
# ---------------------------------------------------------------------------

def test_lower_all_range():
    node = AllExpr(kind="all", var="v",
                   pred=BinOp(kind="binop", op=">",  # type: ignore[arg-type]
                              left=Var(kind="var", name="v"),
                              right=IntLit(kind="int", value=0)),
                   lower=IntLit(kind="int", value=0),
                   upper=Var(kind="var", name="n"))
    t = lower(node, LowerCtx(gamma={"n": Ty.INT}))
    assert "(forall (v : Z), 0 <= v < n -> " in t.text
    assert t.ty is Ty.PROP


def test_lower_all_list():
    """all(...) over a list model → forallb with LitInt unwrapping."""
    node = AllExpr(kind="all", var="x", lst="xs",  # type: ignore[arg-type]
                   pred=BinOp(kind="binop", op=">",
                              left=Var(kind="var", name="x"),
                              right=IntLit(kind="int", value=0)))
    t = lower(node, _LIST_CTX)
    assert t.text.startswith("(forallb (fun (_v : sn_val) => ")
    assert "match _v with" in t.text
    assert "LitInt n =>" in t.text
    assert "Z.ltb 0 n" in t.text
    assert t.text.endswith(") M_xs = true)")
    assert t.ty is Ty.PROP


def test_lower_all_list_complex():
    """all with a composite predicate body → unwrapped LitInt."""
    node = AllExpr(kind="all", var="i", lst="xs",  # type: ignore[arg-type]
                   pred=Logical(kind="logical", op="and",
                                operands=[
                                    BinOp(kind="binop", op=">=",
                                          left=Var(kind="var", name="i"),
                                          right=IntLit(kind="int", value=0)),
                                    BinOp(kind="binop", op="<",
                                          left=Var(kind="var", name="i"),
                                          right=IntLit(kind="int", value=100)),
                                ]))  # type: ignore[arg-type]
    t = lower(node, _LIST_CTX)
    assert "forallb" in t.text
    assert "match _v with" in t.text
    assert "LitInt n =>" in t.text
    assert "Z.leb 0 n" in t.text
    assert "Z.ltb n 100" in t.text


# ---------------------------------------------------------------------------
# _lower_any — range (including small-range expansion) + list
# ---------------------------------------------------------------------------

def test_lower_any_range():
    node = AnyExpr(kind="any", var="v",
                   pred=BinOp(kind="binop", op="=",  # type: ignore[arg-type]
                              left=Var(kind="var", name="v"),
                              right=IntLit(kind="int", value=0)),
                   lower=IntLit(kind="int", value=0),
                   upper=IntLit(kind="int", value=10))
    t = lower(node, LowerCtx())
    assert "(exists (v : Z), 0 <= v < 10 /\\ " in t.text
    assert t.ty is Ty.PROP


def test_lower_any_small_range():
    """Small ranges (≤5) expand to disjunction."""
    node = AnyExpr(kind="any", var="v",
                   pred=BinOp(kind="binop", op="=",  # type: ignore[arg-type]
                              left=Var(kind="var", name="v"),
                              right=IntLit(kind="int", value=0)),
                   lower=IntLit(kind="int", value=0),
                   upper=IntLit(kind="int", value=3))
    t = lower(node, LowerCtx())
    assert "\\/" in t.text  # disjunction form
    assert "forall" not in t.text
    assert "exists" not in t.text
    assert t.ty is Ty.PROP


def test_lower_any_list():
    """exists(...) over a list → existsb with LitInt unwrapping."""
    node = AnyExpr(kind="any", var="x", lst="xs",  # type: ignore[arg-type]
                   pred=BinOp(kind="binop", op="<=",
                              left=Var(kind="var", name="x"),
                              right=IntLit(kind="int", value=0)))
    t = lower(node, _LIST_CTX)
    assert t.text.startswith("(existsb (fun (_v : sn_val) => ")
    assert "match _v with" in t.text
    assert "LitInt n =>" in t.text
    assert "Z.leb n 0" in t.text
    assert t.text.endswith(") M_xs = true)")
    assert t.ty is Ty.PROP


# ---------------------------------------------------------------------------
# _lower_recursor
# ---------------------------------------------------------------------------

def test_lower_recursor_countb():
    node = RecursorExpr(kind="recursor", recursor="countb",
                        predicate="(fun (x : Z) => Z.ltb 0 x)",
                        arg="xs")
    t = lower(node, _LIST_CTX)
    assert t == CoqTerm(
        "Z.of_nat (countb (fun (x : Z) => Z.ltb 0 x) M_xs)", Ty.INT)


def test_lower_recursor_no_model():
    node = RecursorExpr(kind="recursor", recursor="forallb",
                        predicate="(fun (x : Z) => Z.leb 0 x)",
                        arg="xs")
    t = lower(node, LowerCtx())
    assert "xs" in t.text
    assert "forallb" in t.text


# ---------------------------------------------------------------------------
# _lower_hex_string
# ---------------------------------------------------------------------------

def test_lower_hex_string_bare():
    node = HexStringExpr(kind="hex_string", name="s")
    t = lower(node, LowerCtx())
    assert "str_all_hex" in t.text
    assert "LitString raw" in t.text
    assert t.ty is Ty.PROP


def test_lower_hex_string_postcondition():
    ctx = LowerCtx(post_var="result", post_bound="s",
                   gamma={"result": Ty.STR})
    node = HexStringExpr(kind="hex_string", name="result")
    t = lower(node, ctx)
    assert "str_all_hex (match s with" in t.text


# ---------------------------------------------------------------------------
# _lower_string_contains
# ---------------------------------------------------------------------------

def test_lower_string_contains():
    node = StringContainsExpr(kind="string_contains",
                              needle="err", haystack="msg", negated=False)
    t = lower(node, LowerCtx())
    assert "str_contains_val" in t.text
    assert "str_to_lower_val msg" in t.text
    assert 'LitString "err"%string' in t.text
    assert "= true" in t.text
    assert t.ty is Ty.PROP


def test_lower_string_contains_negated():
    node = StringContainsExpr(kind="string_contains",
                              needle="fatal", haystack="msg", negated=True)
    t = lower(node, LowerCtx())
    assert "<> true" in t.text


# ---------------------------------------------------------------------------
# _lower_string_eq
# ---------------------------------------------------------------------------

def test_lower_string_eq():
    node = StringEqualsExpr(kind="string_eq", var="name",
                            literal="hello", negated=False)
    t = lower(node, LowerCtx())
    assert t == CoqTerm(
        '(String.eqb name "hello"%string = true)', Ty.PROP)


def test_lower_string_eq_negated():
    node = StringEqualsExpr(kind="string_eq", var="name",
                            literal="hello", negated=True)
    t = lower(node, LowerCtx())
    assert t == CoqTerm(
        '(String.eqb name "hello"%string <> true)', Ty.PROP)


def test_lower_string_eq_postcondition():
    ctx = LowerCtx(post_var="result", post_bound="s")
    node = StringEqualsExpr(kind="string_eq", var="result",
                            literal="done", negated=False)
    t = lower(node, ctx)
    assert 'String.eqb s "done"%string' in t.text


# ---------------------------------------------------------------------------
# _lower_re_match
# ---------------------------------------------------------------------------

def test_lower_re_match():
    node = ReMatchExpr(kind="re_match", subject="s", pattern=r"\d+")
    t = lower(node, LowerCtx())
    assert t == CoqTerm(r're_match s "\\d+"', Ty.PROP)


# ---------------------------------------------------------------------------
# _lower_is_valid / _lower_is_shape / _lower_field_access
# ---------------------------------------------------------------------------

def test_lower_is_shape():
    t = lower(IsShape(kind="is_shape", obj="r", model_type="FakeType"),  # type: ignore[arg-type]
              LowerCtx())
    assert t == CoqTerm("True", Ty.PROP)


def test_lower_field_access_precondition():
    node = FieldAccess(kind="field_access", obj="r", field="status")  # type: ignore[arg-type]
    t = lower(node, LowerCtx())
    assert t == CoqTerm('model_field_Z r "status"', Ty.INT)


def test_lower_field_access_postcondition():
    ctx = LowerCtx(post_var="result")
    node = FieldAccess(kind="field_access", obj="result", field="level")  # type: ignore[arg-type]
    t = lower(node, ctx)
    assert t == CoqTerm('model_field_Z v "level"', Ty.INT)


# ---------------------------------------------------------------------------
# Bool-mode: recursor lambda bodies (comparisons produce bare Z.ltb etc.)
# ---------------------------------------------------------------------------

def test_bool_mode_binop_lt():
    node = BinOp(kind="binop", op="<",
                 left=Var(kind="var", name="x"),
                 right=IntLit(kind="int", value=10))
    t = lower(node, _SIMPLE_CTX, bool_mode=True)
    assert t == CoqTerm("(Z.ltb x 10)", Ty.BOOL)


def test_bool_mode_binop_ge():
    node = BinOp(kind="binop", op=">=",
                 left=Var(kind="var", name="x"),
                 right=IntLit(kind="int", value=0))
    t = lower(node, _SIMPLE_CTX, bool_mode=True)
    assert t == CoqTerm("(Z.leb 0 x)", Ty.BOOL)


def test_bool_mode_binop_eq():
    node = BinOp(kind="binop", op="=",
                 left=Var(kind="var", name="x"),
                 right=IntLit(kind="int", value=0))
    t = lower(node, _SIMPLE_CTX, bool_mode=True)
    assert t == CoqTerm("(Z.eqb x 0)", Ty.BOOL)


def test_bool_mode_binop_neq():
    node = BinOp(kind="binop", op="<>",
                 left=Var(kind="var", name="x"),
                 right=IntLit(kind="int", value=0))
    t = lower(node, _SIMPLE_CTX, bool_mode=True)
    assert t == CoqTerm("negb (Z.eqb x 0)", Ty.BOOL)


def test_bool_mode_logical_and():
    a = BinOp(kind="binop", op=">", left=Var(kind="var", name="x"), right=IntLit(kind="int", value=0))
    b = BinOp(kind="binop", op="<", left=Var(kind="var", name="x"), right=IntLit(kind="int", value=10))
    node = Logical(kind="logical", op="and", operands=[a, b])  # type: ignore[arg-type]
    t = lower(node, _SIMPLE_CTX, bool_mode=True)
    assert t == CoqTerm("((Z.ltb 0 x) && (Z.ltb x 10))", Ty.BOOL)


def test_bool_mode_logical_or():
    a = BinOp(kind="binop", op="<", left=Var(kind="var", name="x"), right=IntLit(kind="int", value=0))
    b = BinOp(kind="binop", op=">", left=Var(kind="var", name="x"), right=IntLit(kind="int", value=10))
    node = Logical(kind="logical", op="or", operands=[a, b])  # type: ignore[arg-type]
    t = lower(node, _SIMPLE_CTX, bool_mode=True)
    assert t == CoqTerm("((Z.ltb x 0) || (Z.ltb 10 x))", Ty.BOOL)


def test_bool_mode_logical_not():
    a = BinOp(kind="binop", op="=", left=Var(kind="var", name="x"), right=IntLit(kind="int", value=0))
    node = Logical(kind="logical", op="not", operands=[a])  # type: ignore[arg-type]
    t = lower(node, _SIMPLE_CTX, bool_mode=True)
    assert t == CoqTerm("negb ((Z.eqb x 0))", Ty.BOOL)


# =========================================================================
# WP-3: Totality gate + diagnostics.
# =========================================================================

def test_collect_violations_index():
    """Index is now handled by _lower_index — no longer a stub."""
    from axiomander.oracle.contract_ir import IndexExpr
    node = IndexExpr(kind="index", name="xs",  # type: ignore[arg-type]
                     index=IntLit(kind="int", value=0))
    vs = collect_violations(node)
    assert len(vs) == 0  # WP-4: promoted from stub to real handler


def test_collect_violations_tuple():
    """Tuple is now handled by _lower_tuple — no longer a stub."""
    from axiomander.oracle.contract_ir import TupleExpr
    node = TupleExpr(kind="tuple", elements=[])  # type: ignore[arg-type]
    vs = collect_violations(node)
    assert len(vs) == 0


def test_collect_violations_nested():
    """Nested handled nodes produce no violations."""
    from axiomander.oracle.contract_ir import IndexExpr
    node = BinOp(kind="binop", op="=",
                 left=IndexExpr(kind="index", name="xs",  # type: ignore[arg-type]
                                index=IntLit(kind="int", value=0)),
                 right=IntLit(kind="int", value=0))
    vs = collect_violations(node)
    assert len(vs) == 0


def test_collect_violations_opaque():
    node = OpaqueTerm(kind="opaque_term", name="f")
    vs = collect_violations(node)
    assert len(vs) == 1
    assert vs[0].kind == "opaque_term"


def test_collect_violations_rown():
    from axiomander.oracle.contract_ir import ROwnExpr
    node = ROwnExpr(kind="rown", obj="r")
    vs = collect_violations(node)
    assert len(vs) == 1
    assert vs[0].kind == "rown"


def test_collect_violations_opaque_in_binop():
    """A binop with an opaque_term on one side still reports the stub."""
    node = BinOp(kind="binop", op="=",
                 left=OpaqueTerm(kind="opaque_term", name="f"),
                 right=IntLit(kind="int", value=0))
    vs = collect_violations(node)
    assert len(vs) == 1
    assert vs[0].kind == "opaque_term"


def test_collect_violations_clean():
    """A purely scalar expression produces no violations."""
    node = BinOp(kind="binop", op="<",
                 left=Var(kind="var", name="x"),
                 right=IntLit(kind="int", value=10))
    vs = collect_violations(node)
    assert len(vs) == 0


def test_collect_violations_all():
    """all(...) with a range predicate is clean (no violations)."""
    node = AllExpr(kind="all", var="v",
                   pred=BinOp(kind="binop", op=">",  # type: ignore[arg-type]
                              left=Var(kind="var", name="v"),
                              right=IntLit(kind="int", value=0)),
                   lower=IntLit(kind="int", value=0),
                   upper=IntLit(kind="int", value=10))
    vs = collect_violations(node)
    assert len(vs) == 0


def test_collect_violations_stub_inside_logical():
    """logical containing a stub (opaque_term) reports the stub."""
    stub = OpaqueTerm(kind="opaque_term", name="f")
    node = Logical(kind="logical", op="and",
                   operands=[stub, Var(kind="var", name="x")])  # type: ignore[arg-type]
    vs = collect_violations(node)
    assert len(vs) == 1
    assert vs[0].kind == "opaque_term"


def test_lower_rejects_missing_kind():
    """A node with no kind at all raises a clear error."""
    class NoKind:
        pass

    with pytest.raises(FluidLowerError) as exc:
        lower(NoKind(), LowerCtx())
    assert "outside lambda_A^tot" in str(exc.value)


def test_fluid_violation_is_frozen():
    v = FluidViolation(kind="index", message="list indexing", is_rejection=False)
    with pytest.raises(Exception):
        v.kind = "other"


# =========================================================================
# WP-4: Value-model closure — index, sum, tuple, dict, set, list_eq, sizes.
# =========================================================================

from axiomander.oracle.contract_ir import DictExpr, IndexExpr, ListEqExpr, SetExpr, SumExpr, TupleExpr  # noqa: E402


def test_lower_index_list():
    node = IndexExpr(kind="index", name="xs",  # type: ignore[arg-type]
                     index=IntLit(kind="int", value=2))
    t = lower(node, _LIST_CTX)
    assert "Z.of_nat (List.nth (Z.to_nat (2)) M_xs 0)" == t.text
    assert t.ty is Ty.INT


def test_lower_index_var():
    node = IndexExpr(kind="index", name="xs",  # type: ignore[arg-type]
                     index=Var(kind="var", name="i"))
    t = lower(node, _LIST_CTX)
    assert "Z.to_nat (i)" in t.text
    assert t.ty is Ty.INT


def test_lower_sum():
    node = SumExpr(kind="sum", name="xs")  # type: ignore[arg-type]
    t = lower(node, _LIST_CTX)
    assert "Z.of_nat (List.fold_left Z.add M_xs 0)" == t.text
    assert t.ty is Ty.INT


def test_lower_tuple_empty():
    node = TupleExpr(kind="tuple", elements=[])  # type: ignore[arg-type]
    t = lower(node, LowerCtx())
    assert t.text == "(LitTuple (nil))"
    assert t.ty is Ty.TUPLE


def test_lower_tuple_elements():
    node = TupleExpr(kind="tuple", elements=[  # type: ignore[arg-type]
        IntLit(kind="int", value=1),
        Var(kind="var", name="x"),
    ])
    t = lower(node, _SIMPLE_CTX)
    assert "LitInt 1" in t.text
    assert "LitInt x" in t.text
    assert t.ty is Ty.TUPLE


def test_lower_set():
    node = SetExpr(kind="set", elements=[  # type: ignore[arg-type]
        IntLit(kind="int", value=1),
        IntLit(kind="int", value=2),
    ])
    t = lower(node, LowerCtx())
    assert t.text == "(LitSet (LitInt 1 :: LitInt 2 :: nil))"
    assert t.ty is Ty.SET


def test_lower_dict_literal():
    node = DictExpr(kind="dict", pairs=[  # type: ignore[arg-type]
        (IntLit(kind="int", value=1), IntLit(kind="int", value=100)),
    ])
    t = lower(node, LowerCtx())
    assert "LitDict" in t.text
    assert "(LitInt 1, LitInt 100)" in t.text
    assert t.ty is Ty.DICT


def test_lower_list_eq():
    node = ListEqExpr(kind="list_eq", name="result", op="=", n_elements=3)  # type: ignore[arg-type]
    t = lower(node, LowerCtx(post_var="result", post_bound="v"))
    assert "Z.of_nat (List.length v)" in t.text
    assert "= 3" in t.text
    assert t.ty is Ty.PROP


def test_lower_list_eq_neq():
    node = ListEqExpr(kind="list_eq", name="result", op="<>", n_elements=0)  # type: ignore[arg-type]
    t = lower(node, LowerCtx(post_var="result", post_bound="v"))
    assert "<> 0" in t.text


def test_lower_dict_len():
    from axiomander.oracle.contract_ir import DictLenExpr
    node = DictLenExpr(kind="dict_len", name="d", key=IntLit(kind="int", value=0))
    t = lower(node, _LIST_CTX_TYPED)
    assert "Z.of_nat (List.length d)" in t.text
    assert t.ty is Ty.INT


def test_lower_dict_count():
    from axiomander.oracle.contract_ir import DictCountExpr
    node = DictCountExpr(kind="dict_count", name="d")  # type: ignore[arg-type]
    t = lower(node, _LIST_CTX_TYPED)
    assert "Z.of_nat (List.length d)" in t.text
    assert t.ty is Ty.INT


def test_binop_structural_eq():
    """result == (1, 2) uses sn_val_eqb for structural comparison."""
    tup = TupleExpr(kind="tuple", elements=[  # type: ignore[arg-type]
        IntLit(kind="int", value=1), IntLit(kind="int", value=2)])
    node = BinOp(kind="binop", op="=",
                 left=Var(kind="var", name="v"),
                 right=tup)  # type: ignore[arg-type]
    t = lower(node, LowerCtx())
    assert "sn_val_eqb v" in t.text
    assert t.ty is Ty.PROP


def test_binop_structural_neq():
    """result != (1, 2) uses sn_val_eqb with <>."""
    tup = TupleExpr(kind="tuple", elements=[  # type: ignore[arg-type]
        IntLit(kind="int", value=1)])
    node = BinOp(kind="binop", op="<>",
                 left=Var(kind="var", name="v"),
                 right=tup)  # type: ignore[arg-type]
    t = lower(node, LowerCtx())
    assert "(sn_val_eqb v" in t.text
    assert "<> true" in t.text


# =========================================================================
# WP-5: Pre/postcondition wrappers.
# =========================================================================

def test_compile_precondition_int_prop():
    """A comparison (already PROP) is used directly."""
    node = BinOp(kind="binop", op="<",
                 left=Var(kind="var", name="x"),
                 right=IntLit(kind="int", value=10))
    ctx = LowerCtx(gamma={"x": Ty.INT})
    result = compile_precondition_fluid(node, ctx)
    assert "(x <? 10) = true" in result


def test_compile_precondition_bool_coerced():
    """A bare bool value (not PROP) gets as_prop() coercion."""
    node = BoolLit(kind="bool", value=True)
    result = compile_precondition_fluid(node, LowerCtx())
    assert result == "true = true"


def test_compile_postcondition_int():
    r"""Int result wraps as exists z : Z, v = LitInt z /\ P."""
    node = BinOp(kind="binop", op=">=",
                 left=Var(kind="var", name="result"),
                 right=IntLit(kind="int", value=0))
    ctx = LowerCtx(gamma={"result": Ty.INT},
                   post_var="result", post_bound="z")
    result = compile_postcondition_fluid(node, ctx, result_kind="int")
    assert result.startswith("exists z : Z, v = LitInt z /\\ (")
    # 'result' renamed to 'z' in P; >= flips operands
    assert "(0 <=? z) = true" in result


def test_compile_postcondition_string():
    r"""String result wraps as exists s : string, v = LitString s /\ P."""
    ctx = LowerCtx(post_var="result", post_bound="s")
    node = StringEqualsExpr(kind="string_eq", var="result",
                            literal="done", negated=False)
    result = compile_postcondition_fluid(node, ctx, result_kind="string")
    assert result.startswith("exists s : string, v = LitString s /\\ (")
    assert "String.eqb s" in result


def test_compile_postcondition_bool():
    r"""Bool result wraps as exists b : bool, v = LitBool b /\ P."""
    ctx = LowerCtx(post_var="result", post_bound="b",
                   gamma={"result": Ty.BOOL})
    node = Var(kind="var", name="result")
    result = compile_postcondition_fluid(node, ctx, result_kind="bool")
    assert result.startswith("exists b : bool, v = LitBool b /\\ (")
    # Bool var -> (b <> 0) in Prop
    assert "(b <> 0)" in result


def test_compile_postcondition_structural():
    """sn_val result gets bare proposition (no unpacking)."""
    node = BinOp(kind="binop", op="=",
                 left=Var(kind="var", name="v"),
                 right=IntLit(kind="int", value=42))
    ctx = LowerCtx(gamma={"v": Ty.INT})
    result = compile_postcondition_fluid(node, ctx, result_kind="sn_val")
    assert result == "((v =? 42) = true)"
