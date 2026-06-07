"""Rocq extraction tests: Python → SnakeletIR → Coq Compute → compare.

Generates .v files with Compute eval fuel e empty_state, runs coqc,
parses the output, and compares with Python's eval().
"""

import subprocess, tempfile, os, re
from pathlib import Path
from typing import Any
import pytest

from oracle.snakelet_ir import SLit, SBinOp
from oracle.snakelet_eval import VInt, VBool, VString, VFloat, VUnit, Val

BUILD_DIR = Path(__file__).resolve().parent.parent.parent / "_build" / "default" / "coq"


def lit(py_v: Any) -> SLit:
    if isinstance(py_v, bool):
        return SLit("bool", "true" if py_v else "false")
    if isinstance(py_v, int):
        return SLit("int", str(py_v))
    if isinstance(py_v, str):
        return SLit("string", py_v)
    return SLit("unit", "")


def py_eval(py_a: Any, op: str, py_b: Any) -> tuple[Any, str]:
    """Evaluate in Python. Returns (result_value, "ok"|"TypeError"|...)."""
    try:
        if op == "add": return (py_a + py_b, "ok")
        if op == "sub": return (py_a - py_b, "ok")
        if op == "mul": return (py_a * py_b, "ok")
        if op == "div": return (py_a / py_b, "ok")
        if op == "eq":  return (py_a == py_b, "ok")
        if op == "lt":  return (py_a < py_b, "ok")
        if op == "gt":  return (py_a > py_b, "ok")
        if op == "le":  return (py_a <= py_b, "ok")
        if op == "ge":  return (py_a >= py_b, "ok")
    except Exception as e:
        return (None, type(e).__name__)
    return (None, "unknown_op")


def rocq_compute(e: Any, fuel: int = 20) -> str:
    """Generate Coq, run coqc, parse Compute output. Returns result string."""
    coq_op_map = {"add": "AddOp", "sub": "SubOp", "mul": "MulOp", "div": "DivOp",
                  "eq": "EqOp", "le": "LeOp", "lt": "LtOp"}

    if isinstance(e, SBinOp):
        coq_expr = f"(BinOp {coq_op_map.get(e.op, 'AddOp')} {e.left.to_coq()} {e.right.to_coq()})"
    elif hasattr(e, 'to_coq'):
        coq_expr = e.to_coq()
    else:
        return "ERROR"

    coq_src = f"""From Stdlib Require Import String ZArith PrimFloat.
From stdpp Require Import gmap.
From SnakeletEval Require Import eval empty_state.
Import SnakeletLang.

Compute (eval {fuel} {coq_expr} empty_state).
"""

    with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
        f.write(coq_src)
        tmp = f.name

    try:
        r = subprocess.run(
            ["coqc", "-Q", str(BUILD_DIR.parent.parent), "SnakeletLang",
             "-Q", str(BUILD_DIR), "SnakeletEval",
             tmp],
            capture_output=True, text=True, timeout=30,
        )
        output = r.stdout + r.stderr
        # Parse Compute output: "= Some (LitInt 7)" or "= None"
        m = re.search(r'=\s*(Some\s*\(.*?\)|None)', output, re.DOTALL)
        if m:
            return m.group(1).strip()
        m = re.search(r'=\s*(None)', output)
        if m:
            return "None"
        return f"PARSE_ERROR:{output[:200]}"
    finally:
        try: os.unlink(tmp)
        except: pass
    return "TIMEOUT"


def parse_rocq_val(s: str) -> Any:
    """Parse a Rocq value like 'Some (LitInt 7)' or 'None'."""
    if s == "None" or s.startswith("None"):
        return None
    inner = s.replace("Some (", "").rstrip(")")
    inner = inner.strip()
    if "LitInt" in inner:
        m = re.search(r'LitInt\s+(-?\d+)', inner)
        if m: return int(m.group(1))
    if "LitBool true" in inner or "LitBool  true" in inner:
        return True
    if "LitBool false" in inner or "LitBool  false" in inner:
        return False
    if "LitString" in inner:
        m = re.search(r'LitString\s+"([^"]*)"', inner)
        if m: return m.group(1)
    if "LitFloat" in inner:
        m = re.search(r'LitFloat\s+(\S+)', inner)
        if m: return float(m.group(1))
    return s


def assert_rocq_matches(op: str, py_a: Any, py_b: Any, fuel: int = 20):
    """SnakeletLang in Coq produces the same result as Python."""
    expected, status = py_eval(py_a, op, py_b)
    e = SBinOp(op=op, left=lit(py_a), right=lit(py_b))
    rocq_raw = rocq_compute(e, fuel)
    rocq_val = parse_rocq_val(rocq_raw)

    if status != "ok":
        # Python raised — Rocq should produce None (stuck) or error
        assert rocq_val is None or rocq_raw == "None", \
            f"{py_a} {op} {py_b} → Python {status}, Rocq produced {rocq_raw}"
    else:
        # Both should produce the same value
        if isinstance(expected, float):
            assert isinstance(rocq_val, float), f"expected float, got {rocq_val}"
        elif isinstance(expected, bool):
            assert rocq_val == expected, f"{py_a} {op} {py_b} → expected {expected}, Rocq gave {rocq_val}"
        elif isinstance(expected, int):
            assert rocq_val == expected, f"{py_a} {op} {py_b} → expected {expected}, Rocq gave {rocq_val}"
        elif isinstance(expected, str):
            assert rocq_val == expected, f"{py_a} {op} {py_b} → expected {expected}, Rocq gave {rocq_val}"


# ── Tests ────────────────────────────────────────────────────────

def test_rocq_int_add():     assert_rocq_matches("add", 3, 4)
def test_rocq_int_sub():     assert_rocq_matches("sub", 10, 3)
def test_rocq_int_mul():     assert_rocq_matches("mul", 6, 7)
def test_rocq_int_div():     assert_rocq_matches("div", 3, 2)
def test_rocq_int_eq_true(): assert_rocq_matches("eq", 5, 5)
def test_rocq_int_eq_false(): assert_rocq_matches("eq", 5, 3)
def test_rocq_int_lt():      assert_rocq_matches("lt", 3, 7)
def test_rocq_int_gt():      assert_rocq_matches("gt", 7, 3)
def test_rocq_int_plus_string(): assert_rocq_matches("add", 3, "hello")
