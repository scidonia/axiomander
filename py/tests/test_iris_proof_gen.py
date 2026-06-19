"""Tests for the syntax-directed Iris proof generator.

Each test generates a complete .v file (table + theorem + staged proof
script) and compiles it with coqc against the SnakeletExn Iris stack.
Positive tests must PROVE; negative tests must FAIL at the predicted
stage.  These are end-to-end: Python IR in, checked Coq proof out.
"""

import os
import subprocess
import tempfile
from pathlib import Path

import pytest

from axiomander.oracle.iris_proof_gen import (
    IrisGenError, OpaqueSpec, TransparentDef, generate,
)
from axiomander.oracle.snakelet_ir import (
    SAlloc, SApp, SBinOp, SIf, SLet, SLit, SLoad, SSeq, SStore, SVar,
)

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
        for ext in ("", "o", "ok", "os"):  # .v left for inspection on fail
            try:
                os.unlink(tmp + ext if ext else tmp)
            except OSError:
                pass


def ilit(s: str) -> SLit:
    return SLit("int", s)


TABLE = {
    "square": OpaqueSpec(args=["x"], side=None, result="x * x"),
    "decr": OpaqueSpec(args=["x"], side="1 <= x", result="x - 1"),
    "twice": TransparentDef(
        params=["x"], body=SBinOp("add", SVar("x"), SVar("x"))),
}


# -- Positive: chains -----------------------------------------------------

def test_chain_opaque_transparent_opaque():
    """square(5) -> twice -> decr: mirrors the hand-written staged demo."""
    body = SLet("a", SApp("square", [ilit("5")]),
                SLet("b", SApp("twice", [SVar("a")]),
                     SApp("decr", [SVar("b")])))
    proof = generate("chain", body, "v = LitInt 49", TABLE)
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out
    cats = [s.category for s in proof.stage_list()]
    assert cats == ["call_opaque", "pure_step", "call_transparent",
                    "pure_step", "pure_step", "call_opaque", "finish_pure"]


def test_chain_with_arithmetic():
    """square(3) -> +1 -> decr: calls mixed with pure binops."""
    body = SLet("a", SApp("square", [ilit("3")]),
                SLet("b", SBinOp("add", SVar("a"), ilit("1")),
                     SApp("decr", [SVar("b")])))
    proof = generate("mixed", body, "v = LitInt 9", TABLE)
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out


def test_parametric_chain_with_theorem_pre():
    """decr(x) under the theorem premise 1 <= x: the premise flows into
    the call's precondition obligation via lia."""
    body = SApp("decr", [ilit("x")])
    proof = generate("pdecr", body, "v = LitInt (x - 1)", TABLE,
                     params=["x"], pre="1 <= x")
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out


def test_nested_binop_tree():
    """(a + b) * 2 as a let-bound tree: one pure_step per binop node."""
    body = SLet("s", SBinOp("add", ilit("x"), ilit("y")),
                SBinOp("mul", SVar("s"), ilit("2")))
    proof = generate("ntree", body, "v = LitInt ((x + y) * 2)", TABLE,
                     params=["x", "y"])
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out


# -- Positive: path forks --------------------------------------------------

def test_case_split_abs():
    """abs via a symbolic conditional: the path constraint proves the
    postcondition in both arms."""
    body = SIf(SBinOp("lt", ilit("x"), ilit("0")),
               SBinOp("sub", ilit("0"), ilit("x")),
               ilit("x"))
    proof = generate("genabs", body,
                     "exists z : Z, v = LitInt z /\\ z >= 0",
                     TABLE, params=["x"])
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out
    cats = [s.category for s in proof.stage_list()]
    assert "case_bool" in cats


def test_case_split_with_calls_in_branches():
    """Path fork where each branch makes a call: continuation stages are
    duplicated per path.  The true branch's postcondition (x*x >= 0)
    is nonlinear but provable by lia *because* the path constraint
    0 < x is in context -- path constraints are load-bearing."""
    body = SIf(SBinOp("lt", ilit("0"), ilit("x")),
               SApp("square", [ilit("x")]),
               SApp("square", [ilit("0")]))
    proof = generate("brcall", body,
                     "exists z : Z, v = LitInt z /\\ z >= 0",
                     TABLE, params=["x"])
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out


def test_case_split_branch_calls_linear_post():
    """Same fork shape with a linear post: proves mechanically."""
    body = SIf(SBinOp("lt", ilit("0"), ilit("x")),
               SApp("decr", [ilit("1")]),
               SApp("decr", [ilit("2")]))
    proof = generate("brcall2", body,
                     "exists z : Z, v = LitInt z /\\ z >= 0",
                     TABLE, params=["x"])
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out


# -- Positive: SMT axiom slot ----------------------------------------------

def test_smt_axiom_slot():
    """A nonlinear callee precondition (1 <= n*n + 1) that lia cannot
    solve, discharged via an SMT-provided axiom through
    call_opaque_pre."""
    table = dict(TABLE)
    table["nldecr"] = OpaqueSpec(
        args=["x"], side="1 <= x * x + 1", result="x")
    body = SApp("nldecr", [ilit("n")])
    proof = generate(
        "smtslot", body, "v = LitInt n", table,
        params=["n"],
        axioms=["forall x : Z, 1 <= x * x + 1"],
        pre_overrides={
            "nldecr": "eexists; split; [done | exact (smt_ax_0 n)]"},
    )
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out
    smt_stages = [s for s in proof.stage_list() if s.smt_relevant]
    assert len(smt_stages) == 1


def test_smt_slot_required():
    """Without the axiom, the same nonlinear pre fails mechanically at
    the call stage -- the SMT slot is load-bearing."""
    table = dict(TABLE)
    table["nldecr"] = OpaqueSpec(
        args=["x"], side="1 <= x * x + 1", result="x")
    body = SApp("nldecr", [ilit("n")])
    proof = generate("smtneed", body, "v = LitInt n", table, params=["n"])
    ok, out = run_coqc(proof.emit_exn())
    assert not ok


# -- Negative: failures land at the predicted stage ------------------------

def test_wrong_postcondition_fails():
    body = SLet("a", SApp("square", [ilit("5")]),
                SApp("decr", [SVar("a")]))
    proof = generate("wrongpost", body, "v = LitInt 999", TABLE)
    ok, out = run_coqc(proof.emit_exn())
    assert not ok


def test_pre_violation_fails():
    """decr(0) violates 1 <= x: the call_opaque stage cannot discharge
    the precondition, so the proof fails there (the call is stuck)."""
    body = SApp("decr", [ilit("0")])
    proof = generate("previol", body, "v = LitInt (-1)", TABLE)
    ok, out = run_coqc(proof.emit_exn())
    assert not ok


def test_unknown_callee_rejected_at_generation():
    body = SApp("nonexistent", [ilit("1")])
    with pytest.raises(IrisGenError, match="unknown function"):
        generate("unk", body, "True", TABLE)


def test_non_anf_args_rejected_at_generation():
    body = SApp("square", [SBinOp("add", ilit("1"), ilit("2"))])
    with pytest.raises(IrisGenError, match="ANF"):
        generate("nonanf", body, "True", TABLE)


# -- Table emission --------------------------------------------------------

def test_empty_table_compiles():
    body = SBinOp("add", ilit("1"), ilit("2"))
    proof = generate("notable", body, "v = LitInt 3", {})
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out


def test_multi_arg_opaque_spec():
    table: dict = {"addspec": OpaqueSpec(args=["x", "y"], side=None,
                                         result="x + y")}
    body = SApp("addspec", [ilit("3"), ilit("4")])
    proof = generate("multiarg", body, "v = LitInt 7", table)
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out


# -- Heap operations --------------------------------------------------------

def test_heap_alloc_store_load():
    """Alloc a cell, store 7, load it back: produces 7."""
    body = SLet("x", SAlloc(value=SLit(lit_type="int", value="42")),
                SSeq(exprs=[
                    SStore(loc="x", value=SLit(lit_type="int", value="7")),
                    SLoad(loc="x"),
                ]))
    proof = generate("hs_alloc", body, "v = LitInt 7", {})
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out
    stages = proof.stage_list()
    cats = [s.category for s in stages]
    assert "heap_alloc" in cats
    assert "heap_store" in cats
    assert "heap_load" in cats


def test_heap_store_nonval_rejected():
    """Store of a non-value expression is stuck in SnakeletLang's
    value-restricted ectx.  The ANF pipeline (iris_pipeline.py) would
    hoist it, but the raw generator does not — this test documents the
    boundary."""
    body = SLet("x", SAlloc(value=SLit(lit_type="int", value="0")),
                SStore(loc="x", value=SBinOp(op="add",
                       left=SLit(lit_type="int", value="1"),
                       right=SLit(lit_type="int", value="2"))))
    proof = generate("hs_nv", body, "v = LitUnit", {})
    ok, out = run_coqc(proof.emit_exn())
    assert not ok  # stuck: store RHS is a binop, not a value


def test_heap_anf_hoisted_store_roundtrip():
    """Same pattern with ANF: binop hoisted, store on the atom."""
    body = SLet("x", SAlloc(value=SLit(lit_type="int", value="0")),
                SLet("_t1", SBinOp(op="add",
                     left=SLit(lit_type="int", value="1"),
                     right=SLit(lit_type="int", value="2")),
                SSeq(exprs=[
                    SStore(loc="x", value=SVar("_t1")),
                    SLoad(loc="x"),
                ])))
    proof = generate("hs_anf", body, "v = LitInt 3", {})
    ok, out = run_coqc(proof.emit_exn())
    assert ok, out
