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


def verify_exn(source: str, table=TABLE, **kw) -> tuple[bool, str]:
    """Verify via the exception-aware backend (Result-postcondition WP)."""
    proof = python_to_iris_proof(source, table, **kw)
    return run_coqc(proof.emit_exn())


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


# -- Strong-contract vocabulary (ContractLinter + contract_ir_iris) -----------

def test_forall_contract():
    """forall over a range compiles to a Coq forall Prop."""
    ok, out = verify('''
def ranged_constraint(x):
    assert x >= 0
    assert x < 10
    a = x + 1
    assert a >= 1
    return a
''', table=dict(TABLE))
    assert ok, out


def test_min_max_contract():
    """Z.min/Z.max in a contract compiled through ContractLinter."""
    ok, out = verify('''
def contract_min(a, b):
    x = a
    assert min(a, b) <= x
    return x
''', table=dict(TABLE))
    assert ok, out


def test_implies_contract():
    """implies(A, B) compiled to Coq A -> B."""
    ok, out = verify('''
def guard_result(x):
    assert implies(x >= 1, True)
    r = x
    assert implies(x >= 1, r >= 1)
    return r
''', table=dict(TABLE))
    assert ok, out


def test_compound_contract():
    """Multiple precondition asserts + compound postcondition."""
    ok, out = verify('''
def compound(x, y):
    assert x >= 0
    assert y >= 0
    z = x + y
    assert z >= 0 and z == x + y
    return z
''', table=dict(TABLE))
    assert ok, out


# -- Heap + while loops (Phase 1+2 through the pipeline) ----------------------

def test_heap_roundtrip_from_python():
    """ref/store/load heap builtins lower to SnakeletLang heap ops."""
    ok, out = verify('''
def cell_roundtrip():
    c = ref(5)
    store(c, 9)
    r = load(c)
    assert r == 9
    return r
''')
    assert ok, out


def test_while_count_from_python():
    """A concrete counting loop: the generator emits a bounded repeat
    of the iteration block plus the explicit exit iteration."""
    ok, out = verify('''
def count_to_two():
    c = ref(0)
    while load(c) < 2:
        store(c, load(c) + 1)
    r = load(c)
    assert r == 2
    return r
''')
    assert ok, out


def test_heap_loop_call_combined():
    """The crowning integration: opaque call + heap cell + while loop
    + arithmetic + contracts, all in one Python function."""
    ok, out = verify('''
def mixed(x):
    assert x >= 1
    a = square(x)
    c = ref(0)
    while load(c) < 3:
        store(c, load(c) + 1)
    b = load(c)
    r = a + b
    assert r == x * x + 3
    return r
''')
    assert ok, out


def test_while_wrong_post_rejected():
    """Loop runs to 2; claiming 3 must fail."""
    ok, out = verify('''
def count_wrong():
    c = ref(0)
    while load(c) < 2:
        store(c, load(c) + 1)
    r = load(c)
    assert r == 3
    return r
''')
    assert not ok


def test_while_symbolic_bound_rejected():
    """Symbolic loop bounds need the invariant path (not yet wired):
    the repeat block exits immediately and the proof fails at the
    exit stages -- gracefully, not by divergence."""
    ok, out = verify('''
def count_to_n(n):
    c = ref(0)
    while load(c) < n:
        store(c, load(c) + 1)
    r = load(c)
    assert r == n
    return r
''')
    assert not ok


# -- Loop invariants via assert (step 1) -----------------------------------

def test_while_with_inline_invariant():
    """Symbolic while with invariants: verified via per-loop lemma."""
    ok, out = verify('''
def while_inv(n):
    assert n >= 0
    c = ref(0)
    while load(c) < n:
        assert load(c) <= n
        store(c, load(c) + 1)
    r = load(c)
    assert r == n
    return r
''')
    # Symbolic n: verified with per-loop lemma + inferred Phi
    assert ok, out


def test_while_concrete_with_invariant():
    """Concrete bound with inline invariant: unrolls correctly. """
    ok, out = verify('''
def while_inv_concrete():
    c = ref(0)
    while load(c) < 3:
        assert load(c) <= 3
        store(c, load(c) + 1)
    r = load(c)
    assert r == 3
    return r
''')
    assert ok, out


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


# -- Exceptions ----------------------------------------------------------

def test_raise_proved():
    """A guarded raise is verified via the exception backend: the RExn arm
    is discharged by the matching raises() contract, the normal path by the
    postcondition."""
    ok, out = verify_exn('''
def check_pos(n):
    if n < 0:
        raise ValueError
    r = n
    assert r >= 0
    assert raises(ValueError, n < 0)
    return r
''')
    assert ok, out


def test_try_except_proved():
    """A try/except where the body doesn't raise is verified via wp_try_val."""
    ok, out = verify_exn('''
def try_simple(x):
    try:
        a = x + 1
    except Exception:
        a = 0
    assert x + 1 == x + 1
    return x + 1
''')
    assert ok, out


# -- Negative: exception tests -------------------------------------------

def test_raise_wrong_post_rejected():
    """A guarded raise whose raises() condition does not match the branch
    guard must fail: the RExn arm cannot be discharged."""
    ok, out = verify_exn('''
def bad_raise(n):
    if n < 0:
        raise ValueError
    r = n
    assert r >= 0
    assert raises(ValueError, n > 100)
    return r
''')
    assert not ok


def test_try_wrong_post_rejected():
    """Try body returns x+1, claiming x+2 must fail."""
    ok, out = verify_exn('''
def try_wrong(x):
    try:
        a = x + 1
    except Exception:
        a = 0
    assert a == x + 2
    return a
''')
    assert not ok


# -- Loops: exception backend --------------------------------------------

def test_for_loop_proved_exn():
    """A for-loop over a list parameter is verified via wp_for_list' on the
    Result WP.  Trivial (no-accumulator) invariant; the loop result unit
    feeds the trailing continuation, then the postcondition closes."""
    ok, out = verify_exn('''
def sum_pass(xs):
    for x in xs:
        y = x
    return 0
''')
    assert ok, out


def test_for_loop_accumulating_proved_exn():
    """A for-loop with a per-element invariant over a LITERAL list is
    verified via wp_for_list_forall: the full-list Forall is discharged
    structurally, each step preserves Forall on the tail."""
    ok, out = verify_exn('''
def all_pos():
    for x in [1, 2, 3]:
        assert x > 0
    return 0
''')
    assert ok, out


def test_for_loop_accumulating_param_rejected_exn():
    """The same loop over an OPAQUE list parameter must NOT prove: there is
    no source for Forall (x > 0) over an arbitrary list."""
    ok, out = verify_exn('''
def all_pos(xs):
    for x in xs:
        assert x > 0
    return 0
''')
    assert not ok
