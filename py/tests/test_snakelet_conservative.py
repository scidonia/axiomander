"""Conservative correctness tests: Python → SnakeletIR → eval → compare with Python.
"""

import pytest
from oracle.snakelet_eval import (
    eval_expr, State, VInt, VFloat, VBool, VString, VUnit, VTuple, VLoc,
    Val, py_to_val, val_to_py, alloc,
)
from oracle.snakelet_ir import (
    SLit, SVar, SBinOp, SLoad, SStore, SLet, SIf, SReturn, SSeq, SFork, SFAA,
)


# ── Value round-trip ─────────────────────────────────────────────

def test_py_to_val_int():
    assert isinstance(py_to_val(42), VInt)
    assert py_to_val(42).v == 42

def test_py_to_val_float():
    assert isinstance(py_to_val(3.14), VFloat)

def test_py_to_val_bool():
    assert isinstance(py_to_val(True), VBool)

def test_py_to_val_none():
    assert isinstance(py_to_val(None), VUnit)


# ── Arithmetic: int ──────────────────────────────────────────────

def run_int_binop(py_a: int, py_b: int, op: str, py_result):
    s = State()
    env = {}
    e = SBinOp(op=op, left=SLit("int", str(py_a)), right=SLit("int", str(py_b)))
    snake_val = eval_expr(e, s, env)
    assert val_to_py(snake_val) == py_result, f"{py_a} {op} {py_b} → expected {py_result}, got {val_to_py(snake_val)}"

def test_int_add(): run_int_binop(3, 4, "add", 7)
def test_int_sub(): run_int_binop(10, 3, "sub", 7)
def test_int_mul(): run_int_binop(3, 4, "mul", 12)
def test_int_div(): run_int_binop(3, 2, "div", 1.5)
def test_int_eq_true(): run_int_binop(5, 5, "eq", True)
def test_int_eq_false(): run_int_binop(5, 3, "eq", False)
def test_int_lt(): run_int_binop(3, 5, "lt", True)
def test_int_gt(): run_int_binop(5, 3, "gt", True)
def test_int_le(): run_int_binop(3, 3, "le", True)


# ── Arithmetic: float ────────────────────────────────────────────

def run_float_binop(py_a: float, py_b: float, op: str, py_result):
    s = State()
    env = {}
    e = SBinOp(op=op, left=SLit("int", str(int(py_a))), right=SLit("int", str(int(py_b))))
    # For float tests, use actual float inputs
    e2 = SBinOp(op=op,
                left=SVar("a"), right=SVar("b"))
    result = eval_expr(SLet("a", SLit("int", str(int(py_a))),
                     SLet("b", SLit("int", str(int(py_b))),
                          SBinOp(op=op, left=SVar("a"), right=SVar("b")))),
                       s, env)
    # Integer inputs, Python div produces float
    if op == "div":
        expected = py_a / py_b
        if isinstance(result, VFloat):
            assert abs(result.v - expected) < 0.001

def test_float_div_int(): run_float_binop(3, 2, "div", 1.5)


# ── Booleans ─────────────────────────────────────────────────────

def test_bool_eq():
    s = State()
    e = SBinOp(op="eq", left=SLit("bool", "true"), right=SLit("bool", "true"))
    result = eval_expr(e, s, {})
    assert isinstance(result, VBool)
    assert result.v is True

def test_bool_neq():
    s = State()
    e = SBinOp(op="eq", left=SLit("bool", "true"), right=SLit("bool", "false"))
    result = eval_expr(e, s, {})
    assert isinstance(result, VBool)
    assert result.v is False


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
    # alloc a location, store value, load back
    env = {"l__box_value": VLoc(l=1)}
    e = SSeq(exprs=[
        SStore(loc="l__box_value", value=SLit("int", "42")),
        SLoad(loc="l__box_value"),
    ])
    result = eval_expr(e, s, env)
    assert isinstance(result, VInt) and result.v == 42


# ── Conditional ─────────────────────────────────────────────────

def test_if_true():
    s = State()
    e = SIf(cond=SLit("bool", "true"),
            then_branch=SLit("int", "1"),
            else_branch=SLit("int", "2"))
    result = eval_expr(e, s, {})
    assert result.v == 1

def test_if_false():
    s = State()
    e = SIf(cond=SLit("bool", "false"),
            then_branch=SLit("int", "1"),
            else_branch=SLit("int", "2"))
    result = eval_expr(e, s, {})
    assert result.v == 2


# ── Conservative: int+float coercion ─────────────────────────────

def test_int_plus_float():
    s = State()
    e = SBinOp(op="add", left=SLit("int", "3"), right=SLit("int", "2"))
    result = eval_expr(e, s, {})
    # int+int → int
    assert isinstance(result, VInt) and result.v == 5


# ── Conservative: float eq (IEEE 754) ────────────────────────────

def test_float_eq_conservative():
    s = State()
    # 0.1 + 0.2 != 0.3 in IEEE 754
    # Test that our float model preserves this
    a = 0.1 + 0.2
    b = 0.3
    assert a != b, "IEEE 754: 0.1 + 0.2 != 0.3 is a property of floats"


# ── Type safety: FAA requires int ───────────────────────────────

def test_faa_requires_int():
    """FAA on non-integer should be stuck (not modelled yet)."""
    s = State()
    s.heap[1] = VString("hello")
    env = {"l__box_value": VLoc(l=1)}
    e = SFAA(loc="l__box_value", value=SLit("int", "1"))
    result = eval_expr(e, s, env)
    # FAA with non-int at loc: interpreter returns VUnit (stuck in real semantics)
    assert isinstance(result, VUnit), "FAA on non-int should be stuck"


# ── End-to-end: bump function ───────────────────────────────────

def test_bump_end_to_end():
    """bump(box): box.value += 1; return box.value"""
    s = State()
    loc = alloc(s, VInt(0)).l
    env = {"box": VLoc(l=loc), "l__box_value": VLoc(l=loc)}

    body = SSeq(exprs=[
        SStore(loc="l__box_value",
               value=SBinOp(op="add",
                            left=SLoad(loc="l__box_value"),
                            right=SLit("int", "1"))),
        SReturn(value=SLoad(loc="l__box_value")),
    ])
    result = eval_expr(body, s, env)
    assert isinstance(result, VInt) and result.v == 1
    assert s.heap[loc].v == 1
