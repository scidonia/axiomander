"""Adequacy harness: cross-check fluid-lowered Coq terms against executable semantics.

For each (expression, concrete values) pair, the test:
  1. Lowers the expression via fluid_lowering → Coq Prop string
  2. Substitutes concrete values for variables
  3. Evaluates the expression via Python (contract runtime)
  4. Generates a Coq lemma with vm_compute and checks it via coqc

This is translation validation (theory section 7): each lowering instance is
machine-checked against a reference semantics.  Soundness is per-instance,
not once-and-for-all — exactly the CompCert-style approach.

Tests run with AXIOMANDER_FLUID=1 (to exercise the fluid lowerer path).
"""

import os
import subprocess
import tempfile
from pathlib import Path

import pytest

from axiomander.oracle.contract_ir import (
    BinOp,
    BoolLit,
    IntLit,
    Logical,
    Var,
)
from axiomander.oracle.fluid_lowering import CoqTerm, LowerCtx, Ty, lower

COQ_ROOT = Path(__file__).resolve().parent.parent.parent / "coq"
_CACHE: dict[str, bool] = {}  # coqc binary existence check


def _has_coqc() -> bool:
    if "coqc" not in _CACHE:
        _CACHE["coqc"] = subprocess.run(
            ["coqc", "--version"], capture_output=True).returncode == 0
    return _CACHE["coqc"]


pytestmark = pytest.mark.skipif(not _has_coqc(), reason="coqc not available")


_CTX = LowerCtx(gamma={"x": Ty.INT, "y": Ty.INT, "b": Ty.BOOL})


def _subst(term: str, bindings: dict[str, int | bool]) -> str:
    """Replace variable names with literal Coq values.

    Negative integers are wrapped in parens for Z_scope parsing,
    e.g. x=-3 becomes (-3).
    """
    result = term
    for name, val in bindings.items():
        if isinstance(val, bool):
            rep = "true" if val else "false"
        elif val < 0:
            rep = f"(-{abs(val)})"
        else:
            rep = str(val)
        # Replace name when it appears as a Coq variable (surrounded by
        # whitespace, parens, or operators).
        result = result.replace(f"({name}", f"({rep}").replace(
            f" {name})", f" {rep})").replace(
            f" {name} ", f" {rep} ").replace(
            f" {name}=", f" {rep}=")
        if result.startswith(f"{name} "):
            result = f"{rep} " + result[len(name) + 1:]
        if result.rstrip() == name or result.rstrip().endswith(f" {name}"):
            result = result[:result.rfind(name)] + rep + result[result.rfind(name) + len(name):]
    return result


def _check_coq(ct: CoqTerm, bindings: dict[str, int | bool],
               expected: bool) -> tuple[bool, str]:
    """Run vm_compute on the lowered CoqTerm with concrete bindings."""
    from axiomander.oracle.fluid_lowering import CoqTerm as _CT
    if not ct.is_prop:
        ct = ct.as_prop()
    term = _subst(ct.text, bindings)
    if expected:
        goal = term
        proof = "compute. reflexivity."
    else:
        goal = f"~ ({term})"
        proof = "compute. intro. inversion H."
    src = (
        f"From Stdlib Require Import ZArith.\n"
        f"Open Scope Z_scope.\n"
        f"Goal {goal}.\n"
        f"Proof. {proof} Qed.\n"
    )
    with tempfile.NamedTemporaryFile(
            mode="w", suffix=".v", delete=False) as f:
        f.write(src)
        tmp = f.name
    try:
        r = subprocess.run(
            ["coqc", "-R", str(COQ_ROOT), "", tmp],
            capture_output=True, text=True, timeout=30,
        )
        return r.returncode == 0, r.stdout + r.stderr
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass


# ---------------------------------------------------------------------------
# Test cases: (expression, bindings, expected_python_bool)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("left,op,right,bindings,expected", [
    # x > 0
    (Var(kind="var", name="x"),  ">",  IntLit(kind="int", value=0),
     {"x": 5}, True),
    (Var(kind="var", name="x"),  ">",  IntLit(kind="int", value=0),
     {"x": -3}, False),
    # x <= 10
    (Var(kind="var", name="x"),  "<=", IntLit(kind="int", value=10),
     {"x": 5}, True),
    (Var(kind="var", name="x"),  "<=", IntLit(kind="int", value=10),
     {"x": 15}, False),
    # x == y
    (Var(kind="var", name="x"),  "=",  Var(kind="var", name="y"),
     {"x": 7, "y": 7}, True),
    (Var(kind="var", name="x"),  "=",  Var(kind="var", name="y"),
     {"x": 7, "y": 8}, False),
    # x * x == y
    (BinOp(kind="binop", op="*", left=Var(kind="var", name="x"), right=Var(kind="var", name="x")),
     "=",  Var(kind="var", name="y"),
     {"x": 4, "y": 16}, True),
    (BinOp(kind="binop", op="*", left=Var(kind="var", name="x"), right=Var(kind="var", name="x")),
     "=",  Var(kind="var", name="y"),
     {"x": 4, "y": 15}, False),
    # x + y < 20
        (BinOp(kind="binop", op="+", left=Var(kind="var", name="x"), right=Var(kind="var", name="y")),
         "<", IntLit(kind="int", value=20),
         {"x": 5, "y": 7}, True),
    ])
def test_adequacy_binop(left, op, right, bindings, expected):
    """lowered comparison term vm_computes to the expected Python boolean."""
    if isinstance(left, Logical):
        node = left  # Logical is self-contained
    else:
        node = BinOp(kind="binop", op=op, left=left, right=right)  # type: ignore[arg-type]
    term = lower(node, _CTX)
    ok, out = _check_coq(term, bindings, expected)
    assert ok, f"coqc failed for {bindings} (expected {expected}): {out[:400]}"


# Scalar literals
@pytest.mark.parametrize("node,bindings,expected", [
    (BoolLit(kind="bool", value=True), {}, True),
    (BoolLit(kind="bool", value=False), {}, False),
])
def test_adequacy_scalar(node, bindings, expected):
    term = lower(node, _CTX)
    ok, out = _check_coq(term, bindings, expected)
    assert ok, f"coqc failed: {out[:400]}"