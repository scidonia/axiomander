"""End-to-end: Python source with assert contracts -> staged Iris proof.

Each test takes real Python source, extracts positional assert
contracts, lowers through PyIR -> SnakeletIR -> ANF -> staged proof
script, and compiles the result with coqc against the SnakeletLang
Iris stack.  Positive tests must PROVE the contract; negative tests
must FAIL (wrong post, missing pre).
"""

import os
import subprocess
import tempfile
from pathlib import Path

import pytest

from oracle.iris_pipeline import IrisGenError, python_to_iris_proof
from oracle.iris_proof_gen import OpaqueSpec, TransparentDef
from oracle.snakelet_ir import SBinOp, SVar

COQ_ROOT = Path(__file__).resolve().parent.parent.parent / "coq"


def run_coqc(src: str) -> tuple[bool, str]:
    with tempfile.NamedTemporaryFile(
            mode="w", suffix=".v", delete=False) as f:
        f.write(src)
        tmp = f.name
    try:
        r = subprocess.run(
            ["coqc", "-R", str(COQ_ROOT), "", tmp],
            capture_output=True, text=True, timeout=180,
        )
        return r.returncode == 0, r.stdout + r.stderr
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass


TABLE = {
    "square": OpaqueSpec(args=["x"], side=None, result="x * x"),
    "decr": OpaqueSpec(args=["x"], side="1 <= x", result="x - 1"),
    "twice": TransparentDef(
        params=["x"], body=SBinOp("add", SVar("x"), SVar("x"))),
}


def verify(source: str, table=TABLE, **kw) -> tuple[bool, str]:
    proof = python_to_iris_proof(source, table, **kw)
    return run_coqc(proof.emit())


# -- Positive: pure arithmetic ----------------------------------------------

def test_linear_arithmetic():
    ok, out = verify('''
def linear(x):
    assert x >= 1
    a = x + x
    b = a - 1
    assert b == 2 * x - 1
    return b
''')
    assert ok, out


def test_nested_expression_anf():
    """(x + 1) * (x + 2): both operands non-values -- without ANF the
    SnakeletLang ectx leaves this stuck.  The pipeline hoists both."""
    ok, out = verify('''
def nested(x):
    assert x >= 0
    c = (x + 1) * (x + 2)
    assert c >= 2
    return c
''')
    assert ok, out


def test_augmented_assignment():
    ok, out = verify('''
def augment(x):
    a = x
    a += 1
    a *= 2
    assert a == 2 * x + 2
    return a
''')
    assert ok, out


# -- Positive: conditionals --------------------------------------------------

def test_conditional_abs():
    ok, out = verify('''
def myabs(x):
    if x < 0:
        r = 0 - x
    else:
        r = x
    assert r >= 0
    return r
''')
    assert ok, out


def test_conditional_max():
    ok, out = verify('''
def mymax(a, b):
    if a < b:
        m = b
    else:
        m = a
    assert m >= a
    return m
''')
    assert ok, out


# -- Positive: contracted calls ---------------------------------------------

def test_opaque_call_chain():
    """square then decr; decr's precondition 1 <= x*x is nonlinear but
    follows from the function precondition x >= 1 via lia's
    hypothesis-product handling."""
    ok, out = verify('''
def chain(x):
    assert x >= 1
    a = square(x)
    b = decr(a)
    assert b == x * x - 1
    return b
''')
    assert ok, out


def test_transparent_helper_call():
    ok, out = verify('''
def use_twice(x):
    a = twice(x)
    b = a + 1
    assert b == x + x + 1
    return b
''')
    assert ok, out


def test_call_in_expression_anf():
    """A call nested in an arithmetic expression is hoisted by ANF into
    a let-bound call stage."""
    ok, out = verify('''
def call_in_expr(x):
    assert x >= 1
    b = square(x) + 1
    assert b == x * x + 1
    return b
''')
    assert ok, out


def test_call_in_branch():
    ok, out = verify('''
def guarded(x):
    if x < 1:
        r = square(1)
    else:
        r = square(x)
    assert r >= 1
    return r
''')
    assert ok, out


# -- Negative: the verifier rejects wrong contracts ---------------------------

def test_wrong_postcondition_rejected():
    ok, out = verify('''
def bad(x):
    a = x + x
    assert a == 3 * x
    return a
''')
    assert not ok


def test_missing_precondition_rejected():
    """decr requires 1 <= arg; without a function precondition the call
    is potentially stuck and the proof must fail."""
    ok, out = verify('''
def unguarded(x):
    b = decr(x)
    assert b == x - 1
    return b
''')
    assert not ok


def test_branch_specific_bug_rejected():
    """Wrong only in the else branch: r == x fails the post r >= 1 when
    x can be 0."""
    ok, out = verify('''
def offbyone(x):
    if x < 1:
        r = 1
    else:
        r = x - 1
    assert r >= 1
    return r
''')
    assert not ok


def test_unknown_callee_rejected():
    with pytest.raises(IrisGenError, match="unknown function"):
        python_to_iris_proof('''
def calls_unknown(x):
    a = mystery(x)
    return a
''', TABLE)


def test_unsupported_op_rejected():
    with pytest.raises(IrisGenError, match="not in the supported"):
        python_to_iris_proof('''
def uses_mod(x):
    a = x % 2
    return a
''', TABLE)


# -- SMT escalation slot -------------------------------------------------------

def test_smt_axiom_via_python():
    """A callee precondition lia cannot prove (1 <= n*n + 1 for
    unconstrained n), discharged through the SMT axiom slot."""
    table = dict(TABLE)
    table["nldecr"] = OpaqueSpec(
        args=["x"], side="1 <= x * x + 1", result="x")
    src = '''
def needs_smt(n):
    a = nldecr(n)
    assert a == n
    return a
'''
    # Without the axiom: mechanically unprovable.
    ok, _ = verify(src, table=table)
    assert not ok
    # With the SMT-discharged axiom: proves.
    ok, out = verify(
        src, table=table,
        axioms=["forall x : Z, 1 <= x * x + 1"],
        pre_overrides={
            "nldecr": "eexists; split; [done | exact (smt_ax_0 n)]"},
    )
    assert ok, out
