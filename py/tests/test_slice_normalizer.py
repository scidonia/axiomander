"""Tests for slice normalizer + Fixpoint emitter (WP-10)."""

import ast

import pytest

from axiomander.oracle.predicate_def import PredicateDef, RecKind
from axiomander.oracle.slice_normalizer import (
    NormalizedBody,
    emit_fixpoint,
    normalize_slice_rec,
)


def _parse_expr(source: str) -> ast.expr:
    """Parse a single expression from source."""
    mod = ast.parse(source)
    return mod.body[0].value  # type: ignore[attr-defined]


def _parse_body_cond(source: str) -> ast.expr:
    """Parse `body if cond else other` — return the IfExp."""
    return _parse_expr(source)


# ---------------------------------------------------------------------------
# normalize_slice_rec
# ---------------------------------------------------------------------------

def test_normalize_is_sorted():
    body = _parse_body_cond(
        "True if len(xs) <= 1 else xs[0] <= xs[1] and is_sorted(xs[1:])")
    nb = normalize_slice_rec(body, "xs")
    assert nb is not None
    assert nb.base_guards == 1
    assert nb.head_var == "hd"
    assert nb.tail_var == "tl"
    cons_text = ast.unparse(nb.cons_expr)
    assert "hd" in cons_text
    assert "is_sorted(tl)" in cons_text
    assert "xs[0]" not in cons_text
    assert "xs[1:]" not in cons_text
    assert "xs[1]" not in cons_text


def test_normalize_non_if_expr():
    body = _parse_expr("xs[0] <= xs[1] and is_sorted(xs[1:])")
    nb = normalize_slice_rec(body, "xs")
    assert nb is None


def test_normalize_head_only():
    """No length guard — return None."""
    body = _parse_body_cond("is_sorted(xs[1:]) if xs == [] else True")
    nb = normalize_slice_rec(body, "xs")
    assert nb is None


# ---------------------------------------------------------------------------
# emit_fixpoint — structural
# ---------------------------------------------------------------------------

def test_emit_structural():
    pd = PredicateDef(name="is_sorted", params=["xs"],
                      body_expr=None, rec_kind=RecKind.STRUCTURAL,
                      rec_arg="xs")
    # Valid Python expression: hd <= rest[0] and is_sorted(rest)
    nb = NormalizedBody(
        base_expr=_parse_expr("True"),
        cons_expr=_parse_expr("hd <= rest[0] and is_sorted(rest)"),
        head_var="hd", tail_var="rest", param="xs",
        base_guards=1,
    )
    coq = emit_fixpoint(pd, nb)
    assert "Fixpoint is_sorted" in coq
    assert "{struct xs}" in coq
    assert "match xs with" in coq
    assert "| hd :: rest =>" in coq


def test_emit_nonrec():
    pd = PredicateDef(name="not_recursive", params=["x"],
                      body_expr=None, rec_kind=RecKind.NONREC)
    coq = emit_fixpoint(pd)
    assert "Unimplemented" in coq


# ---------------------------------------------------------------------------
# emit_fixpoint — measured
# ---------------------------------------------------------------------------

def test_emit_measured():
    pd = PredicateDef(name="f", params=["xs"],
                      body_expr=None, rec_kind=RecKind.MEASURED,
                      rec_arg="len(xs)")
    coq = emit_fixpoint(pd)
    assert "Fixpoint f" in coq
    assert "{struct n}" in coq
    assert "f rest n'" in coq
    assert "match xs with" in coq


# ---------------------------------------------------------------------------
# NormalizedBody frozen
# ---------------------------------------------------------------------------

def test_normalized_body_frozen():
    nb = NormalizedBody(
        base_expr=ast.Constant(value=True),
        cons_expr=ast.Constant(value=False),
    )
    with pytest.raises(Exception):
        nb.head_var = "bad"