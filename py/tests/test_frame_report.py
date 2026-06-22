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


def test_may_emit_must_not_emit_parsed():
    """may_emit and must_not_emit frame declarations are parsed and displayed."""
    out = _report('''
def f(order_id: int):
    """axiomander:
        frame:
            may_emit EventBus.topic("orders.fulfilled")
            must_not_emit EventBus.topic("inventory.low")
    """
    result = order_id
    return result
''', "f")
    assert 'may_emit' in out
    assert 'must_not_emit' in out
    assert 'orders.fulfilled' in out
    assert 'inventory.low' in out


def test_event_log_accepted_by_verify():
    """Functions with may_emit/must_not_emit in frame: are NOT rejected."""
    from axiomander.oracle.iris_pipeline import python_to_iris_proof
    source = '''
def f(order_id: int):
    """axiomander:
        frame:
            may_emit EventBus.topic("orders.fulfilled")
            must_not_emit EventBus.topic("inventory.low")
    """
    result = order_id
    return result
'''
    proof = python_to_iris_proof(source, {}, func_name='f')
    assert proof is not None
    assert 'WPE' in proof.emit_exn()


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


def test_preserves_accepted_by_verify():
    """functions with preserves are NO LONGER rejected (compile as True)."""
    from axiomander.oracle.iris_pipeline import python_to_iris_proof
    source = '''
def f(order_id: int):
    """axiomander:
        preserves GlobalInvariant.accounting_consistency
    """
    result = order_id
    return result
'''
    proof = python_to_iris_proof(source, {}, func_name='f')
    assert proof is not None
    assert 'WPE' in proof.emit_exn()


def test_owns_accepted_by_verify():
    """functions with owns are NO LONGER rejected (displayed, not enforced)."""
    from axiomander.oracle.iris_pipeline import python_to_iris_proof
    source = '''
def f(order_id: int):
    """axiomander:
        owns queue_item: OrderQueue.item(order_id)
    """
    result = order_id
    return result
'''
    proof = python_to_iris_proof(source, {}, func_name='f')
    assert proof is not None
    assert 'WPE' in proof.emit_exn()


def test_full_docstring_contract_accepted():
    """Full contract with all declarations accepted (no IrisGenError)."""
    from axiomander.oracle.iris_pipeline import python_to_iris_proof
    source = '''
def fulfil_order(order_id: int):
    """axiomander:
        requires OrderQueue.contains(order_id)
        owns queue_item: OrderQueue.item(order_id)
        frame:
            may_emit EventBus.topic("orders.fulfilled")
            must_not_emit EventBus.topic("inventory.low")
        preserves GlobalInvariant.accounting_consistency
        ensures result >= 0
    """
    result = order_id
    return result
'''
    proof = python_to_iris_proof(source, {}, func_name='fulfil_order')
    assert proof is not None
    assert 'WPE' in proof.emit_exn()
