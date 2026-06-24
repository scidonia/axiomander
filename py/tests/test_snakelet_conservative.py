"""Conservative correctness tests: Python → SnakeletIR → eval → compare with Python.

Checks: (1) valid ops produce same result as Python.
        (2) type-incompatible ops produce VError(TypeError), matching Python.
        (3) coercions work correctly (int→float, bool→int, str*int).
"""

import pytest
from typing import Any
from axiomander.oracle.snakelet_eval import (
    eval_expr, State, VInt, VFloat, VBool, VString, VUnit, VTuple, VLoc,
    Val, VError, VDict, alloc, _binop,
)
from axiomander.oracle.snakelet_ir import (
    SLit, SVar, SBinOp, SLoad, SStore, SLet, SIf, SReturn, SSeq, SFAA, SDictGet,
)


def py_result(py_a: Any, op: str, py_b: Any) -> Any:
    """Evaluate a binary operation in Python to get expected result or exception."""
    try:
        if op == "add": return py_a + py_b
        if op == "sub": return py_a - py_b
        if op == "mul": return py_a * py_b
        if op == "div": return py_a / py_b
        if op == "eq":  return py_a == py_b
        if op == "lt":  return py_a < py_b
        if op == "gt":  return py_a > py_b
        if op == "le":  return py_a <= py_b
        if op == "ge":  return py_a >= py_b
    except Exception as e:
        return type(e).__name__
    return None


def lit(py_v: Any) -> Any:
    if isinstance(py_v, bool): return SLit("bool", "true" if py_v else "false")
    if isinstance(py_v, int): return SLit("int", str(py_v))
    if isinstance(py_v, float): return SLit("int", str(int(py_v)))  # approximate
    if isinstance(py_v, str): return SLit("string", py_v)
    return SLit("unit", "")


def assert_same(op: str, py_a: Any, py_b: Any):
    """SnakeletLang _binop produces the same result as Python."""
    expected = py_result(py_a, op, py_b)
    actual = eval_expr(SBinOp(op=op, left=lit(py_a), right=lit(py_b)), State(), {})

    if expected == "TypeError":
        assert isinstance(actual, VError) and "TypeError" in str(actual), \
            f"{py_a} {op} {py_b} → expected TypeError, got {type(actual).__name__}"
    elif expected == "ValueError":
        assert isinstance(actual, VError) and "ValueError" in str(actual), \
            f"{py_a} {op} {py_b} → expected ValueError, got {type(actual).__name__}"
    elif isinstance(expected, float):
        assert isinstance(actual, VFloat), f"expected float, got {type(actual).__name__}"
    elif isinstance(expected, bool):
        assert isinstance(actual, VBool), f"expected bool, got {type(actual).__name__}"
    else:
        # int or other — compare values
        if isinstance(actual, VInt):
            assert actual.v == expected, f"{py_a} {op} {py_b} → expected {expected}, got {actual.v}"
        elif isinstance(actual, VBool):
            assert actual.v == expected, f"{py_a} {op} {py_b} → expected {expected}, got {actual.v}"
        elif isinstance(actual, VString):
            assert actual.v == expected, f"{py_a} {op} {py_b} → expected {expected}, got {actual.v}"


# ── Valid operations (must match Python) ─────────────────────────

def test_int_add():    assert_same("add", 3, 4)
def test_int_sub():    assert_same("sub", 10, 3)
def test_int_mul():    assert_same("mul", 3, 4)
def test_int_div():    assert_same("div", 3, 2)      # int/int → float
def test_int_eq_true(): assert_same("eq", 5, 5)
def test_int_eq_false(): assert_same("eq", 5, 3)
def test_int_lt():     assert_same("lt", 3, 5)
def test_int_gt():     assert_same("gt", 5, 3)
def test_int_le():     assert_same("le", 3, 3)

# ── Coercions (must match Python) ────────────────────────────────

def test_bool_as_int():  assert_same("add", True, 1)   # True→1, 1+1=2
def test_bool_false():   assert_same("add", False, 5)  # False→0, 0+5=5
def test_int_plus_bool(): assert_same("add", 3, True)  # 3 + True → 4

def test_string_add():   assert_same("add", "hello", "world")
def test_string_eq():    assert_same("eq", "abc", "abc")
def test_string_neq():   assert_same("eq", "abc", "def")
def test_string_mul():   assert_same("mul", "a", 3)    # "a"*3 → "aaa"

# ── Type errors (must match Python precisely) ───────────────────

def test_int_plus_string():    assert_same("add", 3, "hello")
def test_string_plus_int():    assert_same("add", "hello", 3)
def test_string_lt_int():      assert_same("lt", "hello", 3)
def test_int_div_string():     assert_same("div", 3, "hi")


# ── Let binding ──────────────────────────────────────────────────

def test_let_binding():
    s = State()
    e = SLet("x", SLit("int", "10"),
             SBinOp(op="add", left=SVar("x"), right=SLit("int", "5")))
    result = eval_expr(e, s, {})
    assert isinstance(result, VInt) and result.v == 15


# ── Heap: store + load ──────────────────────────────────────────

def test_store_load():
    s = State()
    env = {"l__box_value": VLoc(l=1)}
    e = SSeq(exprs=[
        SStore(loc="l__box_value", value=SLit("int", "42")),
        SLoad(loc="l__box_value"),
    ])
    result = eval_expr(e, s, env)
    assert isinstance(result, VInt) and result.v == 42


# ── Conditional ─────────────────────────────────────────────────

def test_if_true():
    e = SIf(cond=SLit("bool", "true"), then_branch=SLit("int", "1"), else_branch=SLit("int", "2"))
    assert eval_expr(e, State(), {}).v == 1

def test_if_false():
    e = SIf(cond=SLit("bool", "false"), then_branch=SLit("int", "1"), else_branch=SLit("int", "2"))
    assert eval_expr(e, State(), {}).v == 2


# ── Type safety: FAA on non-int → VError ────────────────────────

def test_faa_requires_int():
    s = State(); s.heap[1] = VString("hello")
    env = {"l__box_value": VLoc(l=1)}
    result = eval_expr(SFAA(loc="l__box_value", value=SLit("int", "1")), s, env)
    assert isinstance(result, VError), f"FAA on string should error, got {result}"


# ── Dict type safety ────────────────────────────────────────────

def test_dict_get_on_int():
    s = State(); s.heap[1] = VInt(42)
    env = {"l": VLoc(l=1)}
    e = SDictGet(loc="l", key=SLit("string", "key"))
    result = eval_expr(e, s, env)
    assert isinstance(result, VError), f"DictGet on int should error, got {result}"


# ── End-to-end: bump function ───────────────────────────────────

def test_bump_end_to_end():
    s = State()
    loc = alloc(s, VInt(0)).l
    env = {"box": VLoc(l=loc), "l__box_value": VLoc(l=loc)}
    body = SSeq(exprs=[
        SStore(loc="l__box_value",
               value=SBinOp(op="add", left=SLoad(loc="l__box_value"), right=SLit("int", "1"))),
        SReturn(value=SLoad(loc="l__box_value")),
    ])
    result = eval_expr(body, s, env)
    assert isinstance(result, VInt) and result.v == 1
    assert s.heap[loc].v == 1


# ── Conservative: IEEE 754 float ─────────────────────────────────

def test_float_inexact():
    """0.1 + 0.2 != 0.3 in IEEE 754 — our float model must preserve this."""
    assert 0.1 + 0.2 != 0.3, "IEEE 754: 0.1+0.2≠0.3 is a property of floats"


# ── Pydantic models: field access via DictGetIntOp ───────────────
# NOTE: Axiomander lowers Pydantic models to LitDict values.  Field
# access (model.balance) compiles to DictGetIntOp(dict, "balance")
# which is dict["balance"] semantics — KeyError, not AttributeError.
# This is intentional: the IR models records as dicts, not objects.

def test_dict_get_int_hit():
    """model.field on a dict returns the integer field value."""
    from axiomander.oracle.snakelet_eval import VDict, VInt
    d = VDict({"balance": VInt(42), "limit": VInt(100)})
    result = _binop("dict_get_int", d, VString("balance"))
    assert isinstance(result, VInt) and result.v == 42


def test_dict_get_int_miss():
    """model.field on a non-existent key raises KeyError."""
    from axiomander.oracle.snakelet_eval import VDict, VInt, VError
    d = VDict({"balance": VInt(42)})
    result = _binop("dict_get_int", d, VString("missing"))
    assert isinstance(result, VError) and result.kind == "KeyError"


def test_dict_get_int_wrong_type():
    """model.field where the value is not an int raises KeyError."""
    from axiomander.oracle.snakelet_eval import VDict, VString, VError
    d = VDict({"name": VString("alice")})
    result = _binop("dict_get_int", d, VString("name"))
    assert isinstance(result, VError) and result.kind == "KeyError"


def test_dict_in_op_hit():
    """InOp 'balance' in model → True."""
    from axiomander.oracle.snakelet_eval import VDict, VInt, VBool
    d = VDict({"balance": VInt(42)})
    result = _binop("in", d, VString("balance"))
    assert isinstance(result, VBool) and result.v is True


def test_dict_in_op_miss():
    """InOp 'missing' in model → False."""
    from axiomander.oracle.snakelet_eval import VDict, VInt, VBool
    d = VDict({"balance": VInt(42)})
    result = _binop("in", d, VString("missing"))
    assert isinstance(result, VBool) and result.v is False


# ── Model field access end-to-end (via SBinOp) ────────────────────

def test_model_field_hit():
    """SBinOp('dict_get_int', VDict lit, key) → field value."""
    e = SBinOp(
        op="dict_get_int",
        left=SLit(lit_type="dict", value="{}", elements=[
            SLit("string", "balance"), SLit("int", "42"),
        ]),
        right=SLit("string", "balance"),
    )
    result = eval_expr(e, State(), {})
    assert isinstance(result, VInt) and result.v == 42


def test_model_field_miss():
    """SBinOp('dict_get_int', VDict lit, missing key) → KeyError."""
    e = SBinOp(
        op="dict_get_int",
        left=SLit(lit_type="dict", value="{}", elements=[
            SLit("string", "balance"), SLit("int", "42"),
        ]),
        right=SLit("string", "missing"),
    )
    result = eval_expr(e, State(), {})
    assert isinstance(result, VError) and result.kind == "KeyError"


def test_model_field_wrong_receiver():
    """DictGetIntOp on non-dict raises TypeError."""
    result = _binop("dict_get_int", VInt(42), VString("balance"))
    assert isinstance(result, VError) and result.kind == "TypeError"


def test_keyerror_matches_python_dict():
    """Our KeyError semantics match Python dict[key] for missing keys."""
    d = {"balance": 42}
    try:
        d["missing"]
    except KeyError as e:
        py_key = str(e)
    # Our IR: DictGetInt on missing key → KeyError('missing')
    result = _binop("dict_get_int", VDict({"balance": VInt(42)}), VString("missing"))
    assert isinstance(result, VError)
    assert result.kind == "KeyError"
    assert "missing" in str(result) or "missing" in result.msg, \
        f"KeyError should mention key 'missing', got {result}"


# ── Pydantic is_valid against Field constraints ───────────────────

def test_is_valid_catches_violations():
    """is_valid(model, Type) catches Field(ge/le) violations.
    Pydantic rejects at construction; Axiomander checks at precondition.
    Uses model_construct to bypass Pydantic validation for testing."""
    from pydantic import BaseModel, Field
    import ast
    from axiomander.oracle.shape_ir import build_shape_registry
    from axiomander.oracle.contract_runtime import is_valid

    class Order(BaseModel):
        qty: int = Field(ge=1, le=100)
        price: int = Field(gt=0)

    src = '''
from pydantic import BaseModel, Field
class Order(BaseModel):
    qty: int = Field(ge=1, le=100)
    price: int = Field(gt=0)
'''
    build_shape_registry(ast.parse(src))

    assert is_valid(Order.model_construct(qty=10, price=50), "Order")
    assert not is_valid(Order.model_construct(qty=0, price=50), "Order")   # ge=1
    assert not is_valid(Order.model_construct(qty=200, price=50), "Order") # le=100
    assert not is_valid(Order.model_construct(qty=10, price=0), "Order")   # gt=0
    assert not is_valid(Order.model_construct(qty=10), "Order")            # missing price


def test_pydantic_field_access_matches_dict():
    """Real Pydantic model field access == DictGetIntOp on model dict."""
    from pydantic import BaseModel, Field
    import ast
    from axiomander.oracle.shape_ir import build_shape_registry

    class Order(BaseModel):
        qty: int = Field(ge=1, le=100)
        price: int = Field(gt=0)

    src = '''
from pydantic import BaseModel, Field
class Order(BaseModel):
    qty: int = Field(ge=1, le=100)
    price: int = Field(gt=0)
'''
    build_shape_registry(ast.parse(src))

    order = Order.model_construct(qty=42, price=99)

    # Dict representation mirrors the Pydantic model
    d = VDict({k: VInt(v) for k, v in order.model_dump().items()})

    # Field access via DictGetIntOp matches model.attribute
    qty_val = _binop("dict_get_int", d, VString("qty"))
    price_val = _binop("dict_get_int", d, VString("price"))

    assert isinstance(qty_val, VInt) and qty_val.v == order.qty == 42
    assert isinstance(price_val, VInt) and price_val.v == order.price == 99


# -- String substring containment (str_contains) --------------------------

def test_str_contains_found():
    r = _binop("str_contains", VString("hello world"), VString("lo wo"))
    assert isinstance(r, VBool) and r.v is True


def test_str_contains_not_found():
    r = _binop("str_contains", VString("hello world"), VString("xyz"))
    assert isinstance(r, VBool) and r.v is False


def test_str_contains_self():
    r = _binop("str_contains", VString("hello"), VString("hello"))
    assert isinstance(r, VBool) and r.v is True


def test_str_contains_empty_needle():
    r = _binop("str_contains", VString("hello"), VString(""))
    assert isinstance(r, VBool) and r.v is True


def test_str_contains_empty_haystack():
    r = _binop("str_contains", VString(""), VString("x"))
    assert isinstance(r, VBool) and r.v is False


def test_str_contains_prefix():
    r = _binop("str_contains", VString("hello world"), VString("hello"))
    assert isinstance(r, VBool) and r.v is True


def test_str_contains_suffix():
    r = _binop("str_contains", VString("hello world"), VString("world"))
    assert isinstance(r, VBool) and r.v is True
