"""Tests for recursive predicate classification (WP-9)."""

import ast

import pytest

from axiomander.oracle.predicate_def import (
    PredicateDef,
    RecKind,
    classify_recursion,
)


def _parse_func(source: str) -> ast.FunctionDef:
    """Parse a single function definition from source."""
    mod = ast.parse(source)
    assert isinstance(mod.body[0], ast.FunctionDef)
    return mod.body[0]


# ---------------------------------------------------------------------------
# Non-recursive predicates
# ---------------------------------------------------------------------------

def test_nonrec_simple():
    fn = _parse_func("def f(x):\n    return x > 0")
    pd = classify_recursion(fn)
    assert pd.rec_kind == RecKind.NONREC
    assert not pd.is_recursive()


def test_nonrec_call_other():
    fn = _parse_func("def f(x):\n    return g(x)")
    pd = classify_recursion(fn)
    assert pd.rec_kind == RecKind.NONREC


# ---------------------------------------------------------------------------
# Structural recursion (D1)
# ---------------------------------------------------------------------------

def test_structural_tail_slice():
    fn = _parse_func("""
def is_sorted(xs):
    if len(xs) <= 1:
        return True
    return xs[0] <= xs[1] and is_sorted(xs[1:])
""")
    pd = classify_recursion(fn)
    assert pd.rec_kind == RecKind.STRUCTURAL
    assert pd.rec_arg == "xs"
    assert pd.is_recursive()


def test_structural_tail_slice_variable_lower():
    fn = _parse_func("""
def f(xs, n):
    if n >= len(xs):
        return True
    return xs[n] > 0 and f(xs, n + 1)
""")
    pd = classify_recursion(fn)
    # f(xs, n+1) — second arg is n+1 which is not a structural slice
    assert pd.rec_kind == RecKind.REJECT


def test_structural_multiple_same_param():
    fn = _parse_func("""
def f(xs):
    if not xs:
        return True
    return f(xs[1:]) and f(xs[1:])
""")
    pd = classify_recursion(fn)
    assert pd.rec_kind == RecKind.STRUCTURAL
    assert pd.rec_arg == "xs"


def test_structural_different_params():
    """Self-calls on different params → reject."""
    fn = _parse_func("""
def f(xs, ys):
    if not xs:
        return f(ys[1:])
    return f(xs[1:])
""")
    pd = classify_recursion(fn)
    assert pd.rec_kind == RecKind.REJECT


# ---------------------------------------------------------------------------
# Rejection (no detectable pattern)
# ---------------------------------------------------------------------------

def test_reject_nonstructural_self_call():
    """Self-call with non-structural arg → reject."""
    fn = _parse_func("""
def f(xs):
    if not xs:
        return True
    return f(xs + [1])
""")
    pd = classify_recursion(fn)
    assert pd.rec_kind == RecKind.REJECT
    assert "do not structurally decrease" in pd.reason
    assert "decreases:" in pd.reason


def test_reject_no_self_call_args():
    fn = _parse_func("""
def f(xs):
    if not xs:
        return True
    return f()
""")
    pd = classify_recursion(fn)
    assert pd.rec_kind == RecKind.REJECT


# ---------------------------------------------------------------------------
# Body expression extraction
# ---------------------------------------------------------------------------

def test_predicate_def_body_expr():
    fn = _parse_func("""
def is_sorted(xs):
    if len(xs) <= 1:
        return True
    return xs[0] <= xs[1] and is_sorted(xs[1:])
""")
    pd = classify_recursion(fn)
    assert pd.body_expr is not None
    assert isinstance(pd.body_expr, ast.BoolOp)


def test_predicate_def_params():
    fn = _parse_func("def is_sorted(xs, key):\n    return True")
    pd = classify_recursion(fn)
    assert pd.params == ["xs", "key"]


# ---------------------------------------------------------------------------
# PredicateDef frozen
# ---------------------------------------------------------------------------

def test_predicate_def_frozen():
    pd = PredicateDef(name="f", params=["x"], body_expr=None,
                      rec_kind=RecKind.NONREC)
    with pytest.raises(Exception):
        pd.name = "g"