"""Tests for loop-predicate → fold_left_acc lowering (WP-12)."""

import ast

import pytest

from axiomander.oracle.predicate_lowering import Recursor, lower_loop_to_fold


def _parse_func(source: str) -> ast.FunctionDef:
    mod = ast.parse(source)
    return mod.body[0]  # type: ignore[return-value]


def test_all_positive_fold():
    fn = _parse_func("""
def all_positive(xs):
    ok = True
    for x in xs:
        if x <= 0:
            ok = False
    return ok
""")
    result = lower_loop_to_fold(fn)
    assert result is not None
    recursor, lam, acc_init, list_name = result
    assert recursor == "forallb"  # detected by _classify_fold_pattern
    assert "Z.leb" in lam
    assert "x" in lam
    assert acc_init == "true"
    assert list_name == "xs"


def test_any_positive_fold():
    fn = _parse_func("""
def any_positive(xs):
    found = False
    for x in xs:
        if x > 0:
            found = True
    return found
""")
    result = lower_loop_to_fold(fn)
    assert result is not None
    recursor, lam, acc_init, list_name = result
    assert recursor == "existsb"  # detected by _classify_fold_pattern
    assert "Z.gtb" in lam or "Z.ltb" in lam
    assert acc_init == "false"


def test_count_positive_fold():
    fn = _parse_func("""
def count_positive(xs):
    count = 0
    for x in xs:
        if x > 0:
            count += 1
    return count
""")
    result = lower_loop_to_fold(fn)
    assert result is not None
    recursor, lam, acc_init, list_name = result
    assert recursor == "countb"  # detected by _classify_fold_pattern
    assert "Z.gtb" in lam
    assert acc_init == "0"


def test_sum_loop_fold():
    fn = _parse_func("""
def sum_list(xs):
    acc = 0
    for x in xs:
        acc += x
    return acc
""")
    result = lower_loop_to_fold(fn)
    assert result is not None
    recurse, lam, acc_init, list_name = result
    assert recurse == "fold_left"
    assert acc_init == "0"


def test_no_loop_returns_none():
    fn = _parse_func("""
def simple(x):
    return x > 0
""")
    result = lower_loop_to_fold(fn)
    assert result is None


def test_not_param_loop_returns_none():
    fn = _parse_func("""
def f(xs):
    ys = [1, 2, 3]
    ok = True
    for y in ys:
        if y < 0:
            ok = False
    return ok
""")
    result = lower_loop_to_fold(fn)
    assert result is None  # iter is not a parameter


def test_recursor_enum_values():
    assert Recursor.FORALLB.value == "forallb"
    assert Recursor.EXISTSb.value == "existsb"
    assert Recursor.COUNTB.value == "countb"
    assert Recursor.FOLD_LEFT.value == "fold_left"
    assert Recursor.NONE.value == "none"