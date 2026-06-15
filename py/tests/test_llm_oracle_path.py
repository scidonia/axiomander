import os
import uuid

import pytest

import axiomander.oracle.mcp_server as mcp
from axiomander.oracle.client import load_config

# Every test in this module invokes the full Coq toolchain.
pytestmark = [pytest.mark.slow]


def _fresh_frame_two_calls_source() -> tuple[str, str]:
    suffix = uuid.uuid4().hex[:8]
    callee = f"inc_llm_{suffix}"
    caller = f"frame_two_calls_llm_{suffix}"
    source = f'''
def {callee}(x: int):
    assert x >= 0
    result = x + 1
    assert result == x + 1
    return result

def {caller}(a: int, b: int):
    assert a >= 0; assert b >= 0
    if __debug__: old_a = a; old_b = b
    a2 = {callee}(a)
    b2 = {callee}(b)
    assert a == old_a
    assert b == old_b
    result = a2 + b2
    assert result == a + b + 2
    return result
'''
    return caller, source


@pytest.mark.skipif(
    os.environ.get("AXIOMANDER_RUN_LLM_TESTS") != "1",
    reason="Set AXIOMANDER_RUN_LLM_TESTS=1 to run expensive real-LLM tests.",
)
def test_tool_verify_function_uses_real_llm_oracle(monkeypatch):
    config = load_config()
    if not config.api_key:
        pytest.skip("No ORACLE_API_KEY / DEEPSEEK_API_KEY configured")

    called = {"llm": False}
    orig_llm = mcp._try_llm_oracle

    def wrapped_llm(source: str, func_name: str, goal, hint=None):
        called["llm"] = True
        return orig_llm(source, func_name, goal, hint)

    # Force this test to exercise the LLM path directly on a real generated
    # Coq file by bypassing the intermediate coq-lsp oracle.
    monkeypatch.setattr(mcp, "_try_llm_oracle", wrapped_llm)
    monkeypatch.setattr(mcp, "_try_coqlsp_oracle", lambda source, func_name, goal: goal)

    func_name, source = _fresh_frame_two_calls_source()
    report = mcp.tool_verify_function({"source": source, "function_name": func_name})

    assert called["llm"], report
    assert "# Verification:" in report, report
    assert "AI oracle" in report or "level3" in report or "✓ Proved" in report, report
