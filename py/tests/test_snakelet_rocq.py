"""Rocq extraction tests: Python → SnakeletIR → Coq Compute → compare.

Generates .v files with Compute eval fuel e empty_state, runs coqc,
parses the output, and compares with Python's eval().
"""

import subprocess, tempfile, os, re
from pathlib import Path
from typing import Any
import pytest

from oracle.snakelet_ir import SLit, SBinOp

BUILD_DIR = None  # not used for Snakelet — use -R coq SnakeletLang directly


def lit(py_v: Any) -> SLit:
    if isinstance(py_v, bool):
        return SLit("bool", "true" if py_v else "false")
    if isinstance(py_v, int):
        return SLit("int", str(py_v))
    if isinstance(py_v, float):
        return SLit("float", repr(py_v))
    if isinstance(py_v, str):
        return SLit("string", py_v)
    if isinstance(py_v, tuple):
        elems = [lit(x) for x in py_v]
        return SLit("tuple", str(py_v), elements=elems)
    if isinstance(py_v, list):
        elems = [lit(x) for x in py_v]
        return SLit("list", str(py_v), elements=elems)
    if isinstance(py_v, type(None)):
        return SLit("unit", "")
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
        if op == "len": return (len(py_a), "ok")
        if op == "in":  return (py_b in py_a, "ok")   # Note: arg order swapped
        if op == "union": return (py_a | py_b, "ok")
        if op == "inter": return (py_a & py_b, "ok")
    except Exception as e:
        return (None, type(e).__name__)
    return (None, "unknown_op")


def rocq_compute(e: Any, fuel: int = 20) -> str:
    """Lower SExpr to Coq, Compute eval_pure, return result."""
    if hasattr(e, 'to_coq'):
        coq_expr = e.to_coq()
    else:
        return "ERROR: no to_coq"

    coq_src = f"""From Stdlib Require Import Uint63Axioms Floats.PrimFloat.
Require Import SnakeletLang SnakeletEval.
Import SnakeletEval.
Open Scope Z_scope.

Compute (eval_pure {fuel} ({coq_expr})).
"""

    with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
        f.write(coq_src)
        tmp = f.name

    try:
        coq_root = Path(__file__).resolve().parent.parent.parent
        r = subprocess.run(
            ["coqc", "-R", str(coq_root / "coq"), "", tmp],
            capture_output=True, text=True, timeout=30,
        )
        output = r.stdout + r.stderr
        # Parse: "= Some (Val (LitInt 7))"
        #       or "= None"
        m = re.search(r'=\s+(Some\s*\(.*?\)|None)', output, re.DOTALL)
        if m:
            return m.group(1).strip()
        return f"PARSE_ERROR:{output[:200]}"
    finally:
        try: os.unlink(tmp)
        except: pass
    return "TIMEOUT"


def parse_rocq_val(s: str) -> Any:
    """Parse eval_pure output: 'Some (Val (LitInt 7))' or 'None'."""
    if s is None or s == "None":
        return None
    s = s.strip()
    if s.startswith("Some "):
        s = s[5:].strip()
        if s.startswith("(") and s.endswith(")"):
            s = s[1:-1]
    if s.startswith("Val "):
        s = s[len("Val "):].strip()
        if s.startswith("(") and s.endswith(")"):
            s = s[1:-1]
    s = s.strip()
    if "LitTuple" in s or "LitList" in s:
        return _parse_list_val(s)
    if "LitDict" in s:
        return _parse_dict_val(s)
    if "LitUnit" in s:
        return "LitUnit"
    if "LitInt" in s:
        m = re.search(r'LitInt\s+(-?\d+)', s)
        if m: return int(m.group(1))
    if "LitBool" in s:
        if "true" in s: return True
        if "false" in s: return False
    if "LitFloat" in s:
        m = re.search(r'LitFloat\s+(\S+)', s)
        if m: return float(m.group(1))
    if "LitString" in s:
        m = re.search(r'LitString\s+"([^"]*)"', s)
        if m: return m.group(1)
    return s


def _parse_list_val(s: str) -> list:
    """Parse 'LitTuple [LitInt 1; LitInt 2]' -> [1, 2]."""
    s = s.strip()
    if "LitTuple" in s:
        s = s[s.index("LitTuple") + len("LitTuple"):]
    elif "LitList" in s:
        s = s[s.index("LitList") + len("LitList"):]
    elif "LitSet" in s:
        s = s[s.index("LitSet") + len("LitSet"):]
    else:
        return []
    s = s.strip()
    # Handle [x; y; z] bracket notation
    if s.startswith("["):
        # Find matching ]
        depth = 0
        end = -1
        for i, c in enumerate(s):
            if c == "[": depth += 1
            elif c == "]":
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end >= 0:
            inner = s[1:end]
            parts = _split_bracket_elems(inner)
            result = []
            for p in parts:
                v = _parse_scalar_val(p.strip())
                if v is not None:
                    result.append(v)
            return result
    # Handle :: nil notation (from custom-generated .v)
    s = s.replace(")%list", ")")
    if s.startswith("("): s = s[1:]
    if s.rstrip().endswith(")"):
        parts = _split_nil_cons(s)
        result = []
        for p in parts:
            v = _parse_scalar_val(p.strip())
            if v is not None:
                result.append(v)
        return result
    if "nil" in s:
        return []
    return []


def _split_bracket_elems(inner: str) -> list[str]:
    """Split '[ ... ; ... ; ...]' inner content respecting nesting."""
    parts = []
    depth = 0
    current = ""
    for c in inner:
        if c == "(" or c == "[":
            depth += 1
            current += c
        elif c == ")" or c == "]":
            depth -= 1
            current += c
        elif c == ";" and depth == 0:
            parts.append(current.strip())
            current = ""
        else:
            current += c
    if current.strip():
        parts.append(current.strip())
    return parts


def _parse_scalar_val(s: str) -> Any:
    """Parse a single scalar val, e.g. 'LitInt 3' -> 3."""
    s = s.strip().replace("\n", " ").replace("  ", " ")
    # Strip SnakeletLang. prefix
    if s.startswith("SnakeletLang."):
        s = s[len("SnakeletLang."):]
    # Remove trailing ) if present
    if s.endswith(")"):
        s = s[:-1].strip()
    if s.startswith("LitInt "):
        return int(s.split(" ", 1)[1].rstrip(")"))
    if s.startswith("LitBool "):
        return "true" in s
    if s.startswith("LitString "):
        m = re.search(r'"([^"]*)"', s)
        if m: return m.group(1)
    if s.startswith("LitFloat "):
        return float(s.split(" ", 1)[1].rstrip(")"))
    return s


def _split_nil_cons(s: str) -> list[str]:
    """Split 'LitInt 1 :: LitInt 2 :: nil' into ['LitInt 1', 'LitInt 2']."""
    # Remove nil at the end
    s = s.replace(" :: nil", "").strip()
    if not s:
        return []
    # Split by " :: " respecting parenthesized groups
    parts = []
    depth = 0
    current = ""
    i = 0
    while i < len(s):
        c = s[i]
        if c == "(":
            depth += 1
            current += c
        elif c == ")":
            depth -= 1
            current += c
        elif s[i:i+4] == " :: " and depth == 0:
            parts.append(current.strip())
            current = ""
            i += 3
        else:
            current += c
        i += 1
    if current.strip():
        parts.append(current.strip())
    return parts


def _parse_dict_val(s: str) -> dict:
    """Parse 'LitDict ((LitInt 1, LitString "a") :: nil)%list'."""
    return {}  # Simplified — dict value parsing deferred



def assert_rocq_matches(op: str, py_a: Any, py_b: Any, fuel: int = 20):
    """SnakeletIR lowereing + Coq eval_pure produces the same result as Python eval."""
    expected, status = py_eval(py_a, op, py_b)
    e = SBinOp(op=op, left=lit(py_a), right=lit(py_b))
    rocq_raw = rocq_compute(e, fuel)
    rocq_val = parse_rocq_val(rocq_raw)

    if status != "ok":
        # Python raised — Rocq should produce None or LitUnit (type-error sentinel)
        assert rocq_val is None or rocq_val == "VError" or rocq_val == "LitUnit", \
            f"{py_a} {op} {py_b} -> Python {status}, Rocq produced {rocq_raw}"
    else:
        if isinstance(expected, float):
            # Float comparison with tolerance — Coq uses IEEE 754
            assert isinstance(rocq_val, float), \
                f"{py_a} {op} {py_b} -> expected float {expected}, Rocq gave {rocq_val}"
            assert abs(rocq_val - expected) < 1e-10 * max(1.0, abs(expected)), \
                f"{py_a} {op} {py_b} -> expected {expected}, Rocq gave {rocq_val}"
        elif isinstance(expected, bool):
            assert isinstance(rocq_val, bool) and rocq_val == expected, \
                f"{py_a} {op} {py_b} -> expected {expected}, Rocq gave {rocq_val}"
        elif isinstance(expected, int):
            assert isinstance(rocq_val, int) and rocq_val == expected, \
                f"{py_a} {op} {py_b} -> expected {expected}, Rocq gave {rocq_val}"
        elif isinstance(expected, str):
            assert isinstance(rocq_val, str) and rocq_val == expected, \
                f"{py_a} {op} {py_b} -> expected {expected}, Rocq gave {rocq_val}"
        elif isinstance(expected, (tuple, list)):
            assert isinstance(rocq_val, (tuple, list)), \
                f"{py_a} {op} {py_b} -> expected tuple/list, got {type(rocq_val)}"
            assert list(rocq_val) == list(expected), \
                f"{py_a} {op} {py_b} -> expected {expected}, Rocq gave {rocq_val}"
        elif expected is None:
            assert rocq_val is None or rocq_val == "LitUnit", \
                f"{py_a} {op} {py_b} -> expected None/VError, Rocq gave {rocq_val}"


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

def test_rocq_str_concat():  assert_rocq_matches("add", "hello", "world")
def test_rocq_str_eq_true(): assert_rocq_matches("eq", "abc", "abc")
def test_rocq_str_eq_false(): assert_rocq_matches("eq", "abc", "def")
def test_rocq_str_len():     assert_rocq_matches("len", "hello", "ignored")

def test_rocq_tuple_concat(): assert_rocq_matches("add", (1, 2), (3, 4))
def test_rocq_tuple_eq():     assert_rocq_matches("eq", (1, 2), (1, 2))
def test_rocq_tuple_neq():    assert_rocq_matches("eq", (1, 2), (3, 4))
def test_rocq_tuple_len():    assert_rocq_matches("len", (1, 2, 3), "ignored")
def test_rocq_tuple_in():     assert_rocq_matches("in", (1, 2, 3), 2)
def test_rocq_tuple_notin():  assert_rocq_matches("in", (1, 2, 3), 99)

def test_rocq_list_concat():  assert_rocq_matches("add", [1, 2], [3, 4])
def test_rocq_list_len():     assert_rocq_matches("len", [1, 2, 3], "ignored")
def test_rocq_list_in():      assert_rocq_matches("in", [1, 2, 3], 2)

def test_rocq_mixed_tuple():  assert_rocq_matches("eq", (1, "hi"), (1, "hi"))
def test_rocq_mixed_neq():    assert_rocq_matches("eq", (1, "hi"), (2, "hi"))
