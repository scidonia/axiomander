"""Fast tests for frame-report command (no coqc)."""

import tempfile
import os
from axiomander.oracle.mcp_server import tool_frame_report


def _report(source: str, func_name: str | None = None) -> str:
    opts = {"source": source}
    if func_name:
        opts["function_name"] = func_name
    return tool_frame_report(opts)


def test_frame_report_shows_assert_contracts():
    out = _report('''
def add(a: int, b: int):
    assert a >= 0
    assert b >= 0
    result = a + b
    assert result >= 0
    return result
''', "add")
    assert "a >= 0" in out
    assert "b >= 0" in out
    assert "result >= 0" in out


def test_frame_report_shows_docstring_contracts():
    out = _report('''
def f(order_id: int):
    """axiomander:
        requires order_id > 0
        ensures result >= 0
    """
    result = order_id
    return result
''', "f")
    assert "order_id > 0" in out
    assert "result >= 0" in out


def test_frame_enforcement_may_modify():
    out = _report('''
def f(order_id: int):
    """axiomander:
        frame:
            may_modify order_id
            must_not_modify other
    """
    order_id = 1
    result = order_id
    return result
''', "f")
    assert "declared may_modify" in out
    assert "declared must_not_modify" in out


def test_frame_enforcement_violation():
    out = _report('''
def f(order_id: int):
    """axiomander:
        frame:
            may_modify result
            must_not_modify order_id
    """
    order_id = 1        # violates must_not_modify!
    result = order_id
    return result
''', "f")
    assert "violate must_not_modify" in out
    assert "not declared in may_modify" in out


def test_owns_display():
    out = _report('''
def f(order_id: int):
    """axiomander:
        owns queue_item: OrderQueue.item(order_id)
    """
    result = order_id
    return result
''', "f")
    assert "owns queue_item" in out


def test_preserves_display():
    out = _report('''
def f(order_id: int):
    """axiomander:
        preserves GlobalInvariant.accounting_consistency
    """
    result = order_id
    return result
''', "f")
    assert "GlobalInvariant.accounting_consistency" in out


def test_implication_in_postcondition_display():
    out = _report('''
def f(order_id: int):
    """axiomander:
        ensures result == "fulfilled" ->
            order_id > 0
            and order_id < 100
    """
    result = order_id
    return result
''', "f")
    assert "implies(result == " in out
    assert "order_id > 0" in out
    assert "order_id < 100" in out
