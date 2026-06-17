"""Test fixture for the fulfil_order contract through the Iris pipeline.

Tests the Phase 3 heap-cell subset.  The full docstring contract in
contract.py is the target — these tests drive the incremental build-out.

Each test is named after the contract element it exercises.
Tests that are expected to fail (infrastructure not yet built) carry
@pytest.mark.xfail with a link to the implementation plan section.
"""

import os
import sys
import subprocess
import tempfile
from pathlib import Path

import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "py"))

COQ_ROOT = Path(__file__).resolve().parent.parent.parent / "coq"


def run_coqc(src: str) -> tuple[bool, str]:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".v", delete=False) as f:
        f.write(src)
        tmp = f.name
    try:
        r = subprocess.run(
            ["coqc", "-R", str(COQ_ROOT), "", tmp],
            capture_output=True, text=True, timeout=180,
        )
        return r.returncode == 0, r.stdout + r.stderr
    finally:
        for ext in ("", "o", "ok", "os", "vo", "glob", "vok"):
            try:
                os.unlink(tmp + ext if ext else tmp)
            except OSError:
                pass


from oracle.iris_pipeline import python_to_iris_proof, IrisGenError


def _verify(src: str, func_name: str) -> tuple[bool, str]:
    """Run the Iris verification pipeline on a source string."""
    proof = python_to_iris_proof(src, {}, func_name=func_name)
    return run_coqc(proof.emit_exn())


def _source(filename: str) -> str:
    path = os.path.join(os.path.dirname(__file__), filename)
    with open(path) as f:
        return f.read()


# -- Phase 3: heap-cell subset ---------------------------------------------


def test_phase3_generates():
    """Phase 3 contract generates a Coq proof without IrisGenError."""
    src = _source("phase3_assert.py")
    try:
        proof = python_to_iris_proof(src, {}, func_name="fulfil_order_phase3")
        assert proof.stages is not None
    except IrisGenError as e:
        pytest.fail(f"IrisGenError: {e}")


@pytest.mark.xfail(
    reason="string comparison in while condition (EqOp for LitString) "
           "not yet supported",
    strict=True,
)
def test_phase3_compiles():
    """Phase 3 contract compiles through coqc.

    XFAIL: The while condition [load(c_status) == "ready"] uses EqOp on
    LitString values.  binop_eval currently only handles LitInt/LitBool.
    Needs: extend binop_eval to handle EqOp/NeOp on LitString."""
    ok, out = _verify(_source("phase3_assert.py"), "fulfil_order_phase3")
    assert ok, f"Compilation failed:\n{out}"


# -- Phase 4: postcondition subsets ---------------------------------------


def test_set_membership_postcondition():
    """Postcondition [result in {"fulfilled", "failed"}].

    Set-membership over string literals expands to a disjunction of
    String.eqb equalities (ContractLinter._expand_set_membership) and the
    string return value is wrapped as [exists s : string, v = LitString s]
    (contract_ir_iris.compile_postcondition)."""
    src = """def in_set(x: int) -> str:
    assert x >= 0
    result = "fulfilled"
    assert result in {"fulfilled", "failed"}
    return result
"""
    ok, out = _verify(src, "in_set")
    assert ok, f"Compilation failed:\n{out}"


def test_string_postcondition():
    """Postcondition [result == "fulfilled"] with string return value.

    The return value is wrapped as [exists s : string, v = LitString s]
    rather than the integer [exists z : Z, v = LitInt z] shape, dispatched
    on the inferred result kind (contract_ir_iris.compile_postcondition)."""
    src = """def str_result(x: int) -> str:
    assert x >= 0
    result = "fulfilled"
    assert result == "fulfilled"
    return result
"""
    ok, out = _verify(src, "str_result")
    assert ok, f"Compilation failed:\n{out}"


# -- Phase 4b: string-guard while loop (single cell) ----------------------


def test_string_guard_while_single_cell():
    """A string-guard loop that terminates by FALSIFYING the guard.

        c = ref("ready")
        while load(c) == "ready":
            store(c, "done")     # falsifies the guard
        result = load(c)         # "done"

    Verified via the wp_while_str Hoare rule (no counter, no coinduction).
    The generator emits a NAMED body-obligation lemma
    [one_cell_body_spec_0] proving {l ↦ "ready" * Inv "ready"} body
    {∃ s', l ↦ s' * Inv s' * guard-false}, then applies wp_while_str and
    discharges the body with [iApply one_cell_body_spec_0].  The path-
    dependent invariant [Inv s := s = "ready" \\/ s = "done"] plus the
    guard-false exit yields [result == "done"]."""
    src = """def one_cell(x: int) -> str:
    assert x > 0
    c = ref("ready")
    while load(c) == "ready":
        store(c, "done")
    result = load(c)
    assert result == "done"
    return result
"""
    ok, out = _verify(src, "one_cell")
    assert ok, f"Compilation failed:\n{out}"


# -- Phase 5: multi-cell while loop ---------------------------------------


@pytest.mark.xfail(
    reason="multi-cell while-invariant (wp_while_inv_gen admitted)",
    strict=True,
)
def test_multicell_while_loop():
    """While loop tracking TWO heap cells (status + payment)."""
    src = """def two_cell_while(limit: int) -> str:
    assert limit > 0
    s = ref("ready")
    p = ref("pending")
    i = 0
    while i < limit:
        store(s, "done")
        store(p, "captured")
        i = i + 1
    r = load(s)
    assert r == "done"
    return r
"""
    ok, out = _verify(src, "two_cell_while")
    assert ok, f"Compilation failed:\n{out}"


# -- Phase 6: top-level composition ---------------------------------------


def test_fulfil_order_composition():
    """fulfil_order calling all 3 subcontracts against the DB theory.

    This is THE capstone test: the full specification graph composes.
    Each subcontract carries its own axiomander: contract (docstring);
    the DB theory ops are in the callee table with predicate posts.

    The implementation flow:
      reserve_inventory -> if fail: bail
      capture_payment    -> idempotent
      commit_order       -> CAS READY->DONE + queue + emit (conditionally)

    Verified compositionally: each callee's postcondition feeds the next.
    """
    from oracle.iris_proof_gen import OpaqueSpec
    from oracle.iris_pipeline import python_to_iris_proof

    src = """
class OrderStatus(IntEnum): READY = 0; DONE = 2
class PaymentState(IntEnum): AUTHORIZED = 0; CAPTURED = 2
class QueueState(IntEnum): READY = 0; DONE = 2

def reserve_inventory(order_id: int) -> int: result = 1; return result
def capture_payment(order_id: int) -> int: result = 2; return result
def cas_order_status(order_id: int, e: int, n: int) -> int: result = 1; return result
def db_set_queue_state(order_id: int, ns: int) -> int: result = 2; return result
def emit_fulfilled_event(order_id: int, worker_id: int) -> int: result = 1; return result

def do_reserve_inventory(order_id: int) -> int:
    \"\"\"
    axiomander:
        requires: order_id > 0
        ensures: result >= 0; result <= 1
    \"\"\"
    r = reserve_inventory(order_id); result = r; return result

def do_capture_payment(order_id: int) -> int:
    \"\"\"
    axiomander:
        requires: order_id > 0
        ensures: result == PaymentState.CAPTURED
    \"\"\"
    p = capture_payment(order_id); result = p; return result

def do_commit_order(order_id: int, worker_id: int) -> int:
    \"\"\"
    axiomander:
        requires: order_id > 0; worker_id > 0
        ensures: result >= 0; result <= 1
    \"\"\"
    won = cas_order_status(order_id, OrderStatus.READY, OrderStatus.DONE)
    if won == 1:
        q = db_set_queue_state(order_id, QueueState.DONE)
        e = emit_fulfilled_event(order_id, worker_id)
        result = 1; return result
    result = 0; return result

def fulfil_order(order_id: int, worker_id: int) -> int:
    \"\"\"
    axiomander:
        requires:
            order_id > 0
            worker_id > 0
        ensures:
            result >= 0
            result <= 1
    \"\"\"
    reserved = do_reserve_inventory(order_id)
    if reserved == 0:
        result = 0
        return result
    captured = do_capture_payment(order_id)
    committed = do_commit_order(order_id, worker_id)
    result = committed
    return result
"""
    table = {
        "reserve_inventory": OpaqueSpec(
            args=["order_id"], side="order_id > 0", result="0",
            post_pred="0 <= r_z /\\ r_z <= 1", post_witness="1"),
        "capture_payment": OpaqueSpec(
            args=["order_id"], side="order_id > 0", result="0",
            post_pred="r_z = 2", post_witness="2"),
        "cas_order_status": OpaqueSpec(
            args=["order_id", "e", "n"], side="order_id > 0", result="0",
            post_pred="r_z = 0 \\/ r_z = 1", post_witness="1"),
        "db_set_queue_state": OpaqueSpec(
            args=["order_id", "ns"], side="order_id > 0", result="0",
            post_pred="r_z = 2", post_witness="2"),
        "emit_fulfilled_event": OpaqueSpec(
            args=["order_id", "worker_id"],
            side="order_id > 0 /\\ worker_id > 0", result="0",
            post_pred="r_z = 1", post_witness="1"),
        "do_reserve_inventory": OpaqueSpec(
            args=["order_id"], side="order_id > 0", result="0",
            post_pred="0 <= r_z /\\ r_z <= 1", post_witness="1"),
        "do_capture_payment": OpaqueSpec(
            args=["order_id"], side="order_id > 0", result="0",
            post_pred="r_z = 2", post_witness="2"),
        "do_commit_order": OpaqueSpec(
            args=["order_id", "worker_id"],
            side="order_id > 0 /\\ worker_id > 0", result="0",
            post_pred="0 <= r_z /\\ r_z <= 1", post_witness="1"),
    }
    proof = python_to_iris_proof(src, table, func_name="fulfil_order")
    ok, out = run_coqc(proof.emit_exn())
    assert ok, f"Composition failed:\n{out}"
