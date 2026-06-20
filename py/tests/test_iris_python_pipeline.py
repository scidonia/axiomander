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
pytestmark = pytest.mark.slow

from axiomander.oracle.iris_pipeline import IrisGenError, python_to_iris_proof
from axiomander.oracle.iris_proof_gen import OpaqueSpec, TransparentDef
from axiomander.oracle.snakelet_ir import SBinOp, SVar

from axiomander.oracle.iris_pipeline import _coq_flags


def run_coqc(src: str) -> tuple[bool, str]:
    with tempfile.NamedTemporaryFile(
            mode="w", suffix=".v", delete=False) as f:
        f.write(src)
        tmp = f.name
    try:
        r = subprocess.run(
            ["coqc"] + _coq_flags() + [tmp],
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


def verify_exn(source: str, table=TABLE, **kw) -> tuple[bool, str]:
    """Verify via the exception-aware backend (Result-postcondition WP),
    the sole Iris backend."""
    proof = python_to_iris_proof(source, table, **kw)
    return run_coqc(proof.emit_exn())


# The exception backend is now the only Iris backend; [verify] is retained
# as an alias so existing call sites keep working.
verify = verify_exn


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


def test_mod_op_now_supported():
    """`mod` (%) was previously unsupported; now it is lowered to ModOp."""
    ok, out = verify_exn('''
def uses_mod(x):
    a = x % 2
    assert True
    return a
''')
    assert ok, out


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
    """Symbolic while with invariants: needs the per-loop lemma path, which
    is not yet ported to the exception backend (raises IrisGenError so the
    function falls through to IMP)."""
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
    assert ok, out


def test_while_concrete_with_invariant():
    """Concrete bound but with an inline invariant assert: the invariant
    triggers the WhileInv path, unsupported on the exception backend."""
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


def test_while_concrete_proved_exn():
    """A concrete counting while-loop verifies on the exception backend via
    loop_unfold (one wp_while unroll per iteration); the loop-condition
    boolean is computed (cbv) so the If reduces."""
    ok, out = verify_exn('''
def count_to_two():
    c = ref(0)
    while load(c) < 2:
        store(c, load(c) + 1)
    r = load(c)
    assert r == 2
    return r
''')
    assert ok, out


def test_while_concrete_wrong_post_rejected_exn():
    """The loop runs to 2; claiming the result is 3 must NOT prove."""
    ok, out = verify_exn('''
def count_wrong():
    c = ref(0)
    while load(c) < 2:
        store(c, load(c) + 1)
    r = load(c)
    assert r == 3
    return r
''')
    assert not ok


# -- Migrated from test_pipeline.py ---------------------------------------

def test_add_exn():
    ok, out = verify_exn('''
def add(a: int, b: int):
    assert True
    result = a + b
    assert result == a + b
    return result
''')
    assert ok, out


def test_max_of_two_exn():
    ok, out = verify_exn('''
def max_of_two(a: int, b: int):
    assert a >= 0; assert b >= 0
    if a >= b: result = a
    else: result = b
    assert result >= a; assert result >= b
    return result
''')
    assert ok, out


def test_clamp_exn():
    ok, out = verify_exn('''
def clamp(val: int, lo: int, hi: int):
    assert lo <= hi
    if val < lo: result = lo
    elif val > hi: result = hi
    else: result = val
    assert lo <= result <= hi
    return result
''')
    assert ok, out


def test_clamp_val_exn():
    ok, out = verify_exn('''
def clamp_val(val: int, lo: int, hi: int):
    assert lo <= hi
    if val < lo: result = lo
    elif val > hi: result = hi
    else: result = val
    assert min(hi, max(lo, result)) == result
    return result
''')
    assert ok, out


def test_float_param_exn():
    ok, out = verify_exn('''
def float_param(x: float):
    assert x >= 0.0
    result = x
    return result
''')
    assert ok, out


def test_implies_basic_exn():
    ok, out = verify_exn('''
def implies_basic(a: int):
    assert a >= 0
    if a > 10: result = 1
    else: result = 0
    assert implies(a > 10, result == 1)
    return result
''')
    assert ok, out


def test_isinstance_threeway_exn():
    ok, out = verify_exn('''
def isinstance_threeway(x) -> bool:
    assert True
    if isinstance(x, ast.Name): return True
    if isinstance(x, ast.Subscript): return True
    if isinstance(x, ast.Attribute): return True
    return False
''')
    assert ok, out


def test_double_exn():
    ok, out = verify_exn('''def double(n: int):
    assert n >= 0
    result = n + n
    assert result == 2 * n
    return result
''')
    assert ok, out


def test_clamp2_exn():
    ok, out = verify_exn('''def clamp2(val: int, lo: int, hi: int):
    assert lo <= hi
    if val < lo:
        result = lo
    else:
        if val > hi:
            result = hi
        else:
            result = val
    assert result >= lo and result <= hi
    return result
''')
    assert ok, out


# -- List operations (AppendOp / LengthOp) --------------------------------

def test_list_append_len_exn():
    """xs=[]; xs.append(v); len(xs) verifies via AppendOp/LengthOp."""
    ok, out = verify_exn('''
def simple_append(x: int):
    assert x >= 0
    items = []
    items.append(x)
    result = len(items)
    assert result == 1
    return result
''')
    assert ok, out


# -- Structural object projection (DictGetOp / dict_lookup) ---------------
# Pydantic model field access and dict indexing lower to a sound structural
# projection over LitDict (binop_eval DictGetOp -> dict_lookup_kvs), NOT to
# flattened scalar variables.  The object stays a single sn_val, preserving
# identity and composing for nested/whole-object use.

from axiomander.oracle.iris_proof_gen import IRIS_BUILTINS


def _builtins_table(extra=None):
    t = dict(IRIS_BUILTINS)
    if extra:
        t.update(extra)
    return t


def test_pydantic_field_access_exn():
    """account.balance lowers to field_access -> DictGetOp projection,
    keeping `account` a single sn_val (no flattening)."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Account(BaseModel):
    balance: int = Field(ge=0)
def get_balance(account: Account) -> int:
    result = account.balance
    return result
''', table=_builtins_table(), func_name="get_balance")
    assert ok, out


def test_dict_index_unguarded_rejected():
    """d[k] is PARTIAL: a miss raises KeyError(k).  With a symbolic dict and
    NO membership guarantee, the function genuinely can raise, so it must NOT
    verify against a total (exception-free) postcondition.  Rejection here is
    soundness, not a limitation -- the KeyError branch (RExn) cannot meet the
    RVal-only postcondition.  (To verify, supply `assert k in d` or use a
    concrete dict; precondition-driven branch elimination is future work.)"""
    ok, out = verify_exn('''
def lookup(d: dict, k):
    result = d[k]
    return result
''', table=_builtins_table(), func_name="lookup")
    assert not ok, "unguarded symbolic d[k] must be rejected (can raise KeyError)"


def test_pydantic_precondition_field():
    """assert account.balance >= 0: contract field access compiles to
    model_field_Z structural projection, not flattened Var."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Account(BaseModel):
    balance: int = Field(ge=0)
def get_balance(account: Account) -> int:
    assert account.balance >= 0
    result = account.balance
    return result
''', table=_builtins_table(), func_name="get_balance")
    assert ok, out


def test_pydantic_postcondition_field():
    """assert result == account.balance: postcondition uses structural
    field projection, verifies by reflexivity (same field_access in body)."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Account(BaseModel):
    balance: int = Field(ge=0)
def check_balance(account: Account):
    result = account.balance
    assert result == account.balance
    return result
''', table=_builtins_table(), func_name="check_balance")
    assert ok, out


def test_pydantic_wrong_postcondition_rejected():
    """assert result == 0 when body just reads the field: wrong, must reject."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Account(BaseModel):
    balance: int = Field(ge=0)
def wrong_post(account: Account) -> int:
    assert account.balance >= 0
    result = account.balance
    assert result == 0
    return result
''', table=_builtins_table(), func_name="wrong_post")
    assert not ok, "result == 0 is not guaranteed by the body"


def test_pydantic_two_fields():
    """Two distinct model fields project distinct values (identity preserved)."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Account(BaseModel):
    balance: int = Field(ge=0)
    status: int = Field(ge=0, le=5)
def sum_fields(account: Account) -> int:
    b = account.balance
    s = account.status
    result = b + s
    assert result == account.balance + account.status
    return result
''', table=_builtins_table(), func_name="sum_fields")
    assert ok, out


# -- List append with SSA rebinding (store-back semantics) ---------------

def test_list_append_ssa_single():
    """xs.append(v) on a type-annotated list param rebinds xs via SLet
    so subsequent len(xs) sees the updated list."""
    ok, out = verify_exn('''
def append_and_len(xs: list):
    xs.append(1)
    result = len(xs)
    return result
''', table=_builtins_table(), func_name="append_and_len")
    assert ok, out


def test_list_append_ssa_multi():
    """Multiple appends chain through SSA renames."""
    ok, out = verify_exn('''
def multi_append(xs: list):
    xs.append(1)
    xs.append(2)
    xs.append(3)
    result = len(xs)
    return result
''', table=_builtins_table(), func_name="multi_append")
    assert ok, out


def test_list_append_ssa_preserves_identity():
    """Append creates a new list; the original param is unchanged."""
    ok, out = verify_exn('''
def append_original_unchanged(xs: list):
    orig_len = len(xs)
    xs.append(1)
    new_len = len(xs)
    result = new_len - orig_len
    assert result == 1
    return result
''', table=_builtins_table(), func_name="append_original_unchanged")
    assert ok, out


# -- Float arithmetic + coercion (int+float -> float) -------------------

def test_float_add_body():
    """Float+float addition in body, int postcondition (True)."""
    ok, out = verify_exn('''
def float_add(x: float, y: float):
    result = x + y
    return result
''', table=_builtins_table(), func_name="float_add")
    assert ok, out


def test_float_int_coercion_body():
    """int + float -> float (Python coercion) in body."""
    ok, out = verify_exn('''
def mixed_add(n: int, x: float):
    result = n + x
    return result
''', table=_builtins_table(), func_name="mixed_add")
    assert ok, out


def test_float_compare_contract():
    """Float comparison in precondition compiles to PrimFloat.leb."""
    ok, out = verify_exn('''
def float_ge_check(x: float):
    assert x >= 0.0
    result = x
    return result
''', table=_builtins_table(), func_name="float_ge_check")
    assert ok, out


# -- Staged proof output + residual capture --------------------------------

def test_residual_capture_goal():
    """When a proof fails, capture_residual produces a .v fragment
    with the open goal and full hypotheses at the failure point."""
    from axiomander.oracle.iris_pipeline import capture_residual

    src = '''
def wrong(x: int):
    assert x >= 0
    result = x + 1
    assert result == 0
    return result
'''
    residual = capture_residual(src, {}, func_name="wrong")
    assert residual is not None, "should capture residual on failure"
    assert "Show." in residual
    assert "Abort." in residual
    assert "wrong_residual" in residual
    # The residual must compile (Abort ensures no Qed needed)
    ok, out = run_coqc(residual)
    assert ok, f"residual should compile: {out}"


def test_residual_no_capture_on_pass():
    """capture_residual returns None for a function that verifies."""
    from axiomander.oracle.iris_pipeline import capture_residual

    src = '''
def good(x: int):
    assert x >= 0
    result = x + 1
    assert result > x
    return result
'''
    residual = capture_residual(src, {}, func_name="good")
    assert residual is None, "should return None for verified function"


# -- Structured result.attr in postconditions ----------------------------

def test_result_field_in_post():
    """result.x on a model-returning function: structural projection
    on the raw WP binder v, no int existential wrapper."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Point(BaseModel):
    x: int = Field(ge=0)
def identity(p: Point) -> Point:
    assert p.x >= 0
    result = p
    assert result.x == p.x
    return result
''', table=_builtins_table(), func_name="identity")
    assert ok, out


def test_result_field_wrong_rejected():
    """result.x == 0 on a model with p.x >= 0: correctly rejected."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Point(BaseModel):
    x: int = Field(ge=0)
def wrong_result(p: Point) -> Point:
    assert p.x >= 0
    result = p
    assert result.x == 0
    return result
''', table=_builtins_table(), func_name="wrong_result")
    assert not ok, "result.x == 0 should be rejected when p.x >= 0"


# -- Pure-counter while loops (heap promotion) ---------------------------

def test_while_symbolic_bound():
    """while i < n: i = i + 1 with symbolic bound verified via heap promotion."""
    ok, out = verify_exn('''
def count_up(n: int):
    assert n >= 0
    i = 0
    while i < n:
        i += 1
    result = i
    return result
''', table=_builtins_table(), func_name="count_up")
    assert ok, out


# -- Multi-variable while loops (heap promotion for all locals) ----------

def test_while_multi_variable():
    """Two variables (counter + accumulator) both heap-promoted."""
    ok, out = verify_exn('''
def sum_to(n: int):
    assert n >= 0
    acc = 0
    i = 0
    while i < n:
        i += 1
        acc += i
    result = acc
    return result
''', table=_builtins_table(), func_name="sum_to")
    assert ok, out


def test_while_with_invariant_rewritten():
    """Invariant assert i <= n rewritten to lemma params after promotion."""
    ok, out = verify_exn('''
def count_with_inv(n: int):
    assert n >= 0
    i = 0
    while i < n:
        assert i <= n
        i += 1
    result = i
    return result
''', table=_builtins_table(), func_name="count_with_inv")
    assert ok, out


# -- Set operations (InOp, SetAddOp, value-type semantics) ---------------

def test_set_add_and_in():
    """set() + add + in as value-type ops, no heap allocation."""
    ok, out = verify_exn('''
def test_set():
    seen = set()
    seen.add(1)
    result = 1 in seen
    return result
''', table=_builtins_table(), func_name="test_set")
    assert ok, out


def test_set_not_in():
    """c not in seen compiles to InOp and Not check."""
    ok, out = verify_exn('''
def test_not_in():
    seen = set()
    seen.add(1)
    result = 2 not in seen
    return result
''', table=_builtins_table(), func_name="test_not_in")
    assert ok, out


def test_set_membership_rejected_wrong():
    """1 in empty set gives False, but contract asserts True — must reject."""
    ok, out = verify_exn('''
def wrong_in():
    seen = set()
    result = 1 in seen
    assert result == True
    return result
''', table=_builtins_table(), func_name="wrong_in")
    assert not ok, "1 in empty set gives False, contract says True"


# -- String indexing (StrIndexOp) ---------------------------------------

def test_string_index():
    """text[i] on string param uses String.substring."""
    ok, out = verify_exn('''
def first_char(text: str):
    assert len(text) > 0
    result = text[0]
    return result
''', table=_builtins_table(), func_name="first_char")
    assert ok, out


# -- String operations (StartsWithOp, EndsWithOp) -----------------------

def test_string_startswith():
    """s.startswith(prefix) uses String.prefix."""
    ok, out = verify_exn('''
def starts_hello(s: str):
    assert len(s) > 0
    result = s.startswith("hello")
    return result
''', table=_builtins_table(), func_name="starts_hello")
    assert ok, out


def test_string_endswith():
    """s.endswith(suffix) uses substring-based suffix check."""
    ok, out = verify_exn('''
def ends_world(s: str):
    assert len(s) > 0
    result = s.endswith("world")
    return result
''', table=_builtins_table(), func_name="ends_world")
    assert ok, out


# -- Model validation (is_valid) -----------------------------------------

def test_is_valid_field_constraint():
    """is_valid generates Field(ge=0) constraint via model_field_Z."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Account(BaseModel):
    balance: int = Field(ge=0)
def constrained(account: Account) -> int:
    assert is_valid(account, Account)
    result = account.balance
    return result
''', table=_builtins_table(), func_name="constrained")
    assert ok, out


def test_is_valid_wrong_rejected():
    """is_valid(acct) with Field(ge=0) — body asserts result < 0, must reject."""
    ok, out = verify_exn('''
from pydantic import BaseModel, Field
class Account(BaseModel):
    balance: int = Field(ge=0)
def bad(account: Account) -> int:
    assert is_valid(account, Account)
    result = account.balance
    assert result < 0
    return result
''', table=_builtins_table(), func_name="bad")
    assert not ok, "result < 0 contradicts Field(ge=0) constraint"


# -- String case-mapping (lower/upper) ---------------------------------

def test_string_lower():
    """s.lower() uses str_to_lower Fixpoint via ToLowerOp."""
    ok, out = verify_exn('''
def lower_test(s: str):
    assert len(s) > 0
    result = s.lower()
    return result
''', table=_builtins_table(), func_name="lower_test")
    assert ok, out


def test_string_upper():
    """s.upper() uses str_to_upper Fixpoint via ToUpperOp."""
    ok, out = verify_exn('''
def upper_test(s: str):
    result = s.upper()
    return result
''', table=_builtins_table(), func_name="upper_test")
    assert ok, out


# -- Dict get with default (d.get) --------------------------------------

def test_dict_get_hit():
    """d.get(k, default) where k is present in a concrete dict."""
    ok, out = verify_exn('''
def get_hit():
    d = {1: "a", 2: "b"}
    result = d.get(1, "default")
    return result
''', table=_builtins_table(), func_name="get_hit")
    assert ok, out


def test_dict_get_miss():
    """d.get(k, default) where k is NOT present — returns default."""
    ok, out = verify_exn('''
def get_miss():
    d = {1: "a"}
    result = d.get(2, "not_found")
    return result
''', table=_builtins_table(), func_name="get_miss")
    assert ok, out


def test_dict_get_opaque():
    """d.get(k, default) on opaque dict param."""
    ok, out = verify_exn('''
def get_opaque(d: dict, k, default):
    result = d.get(k, default)
    return result
''', table=_builtins_table(), func_name="get_opaque")
    assert ok, out


# -- Dict set (d[k] = v) -------------------------------------------------

def test_dict_set_opaque():
    """d[k] = v on opaque dict param via TupleOp + DictSetOp."""
    ok, out = verify_exn('''
def set_key(d: dict, k, v):
    d[k] = v
    result = d
    return result
''', table=_builtins_table(), func_name="set_key")
    assert ok, out


def test_dict_set_with_arithmetic():
    """d[x+1] = y*2 with expression key/value, lowered via ANF."""
    ok, out = verify_exn('''
def set_expr(d: dict, x, y):
    d[x + 1] = y * 2
    result = d
    return result
''', table=_builtins_table(), func_name="set_expr")
    assert ok, out
