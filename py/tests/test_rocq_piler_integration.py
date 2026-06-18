"""
Standalone integration test: generate Coq for frame_two_calls and
attempt interactive proof via rocq-piler. Times each step.
"""
import os
import re
import sys
import time
from pathlib import Path

import pytest

# Every test in this module invokes the full Coq toolchain.
pytestmark = [pytest.mark.slow]

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(PROJECT_ROOT / "py"))

from oracle.mcp_server import _verify_function, _gen_imp_body, _build_contract_map, _generate_coq
from oracle.rocq_robot_client import RocqRobotClient


def generate_coq(source: str, func_name: str) -> str:
    """Generate the Coq theorem file for a function (same path as MCP server)."""
    from oracle.python_to_imp import translator
    from oracle.assertion_finder import find_assertions

    tree = translator.parse_source(source)
    func_node = tree.find_function(func_name)
    lint_results = find_assertions(func_node, tree)
    imp_body, imp_ir = _gen_imp_body(tree, func_node, contract_map=_build_contract_map(tree))
    
    coq_source = _generate_coq(
        func_node, lint_results, imp_body, tree, None,
        ghost_vars={}, imp_ir=imp_ir,
    )
    return coq_source


def try_prove_interactive(coq_source: str, theorem_name: str) -> dict[str, float | bool | str]:
    """Try to prove a theorem interactively via rocq-piler, timing each step."""
    # Clean up for rocq-piler
    content = coq_source
    content = content.replace("From Hammer Require Import Hammer.\n\n", "")
    content = content.replace("Require Import ZArith", "From Stdlib Require Import ZArith")
    content = re.sub(
        r"Proof\.\n  intros\.\n  wp_prove\.\nQed\.",
        "Proof.\n  Admitted.",
        content,
    )
    
    import tempfile
    with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False) as f:
        f.write(content)
        vfile = Path(f.name)

    try:
        client = RocqRobotClient(file_path=vfile, workspace_root=PROJECT_ROOT, timeout=120.0)
        assert client.start(), "rocq-piler failed to start"

        # Step 1: Focus
        t0 = time.time()
        state = client.focus(theorem_name)
        focus_time = time.time() - t0
        if not state.goals:
            return {"status": "no_goals", "focus": focus_time, "error": state.error}

        results = {"focus": focus_time}
        
        # Try standard tactics 
        tactics = [
            "intros a b [Ha Hb].",
            "unfold " + theorem_name.replace("_correct", "_body") + ".",
            "wp_reduce.",
        ]
        
        for i, tac in enumerate(tactics):
            t0 = time.time()
            state = client.insert_tactic(theorem_name, tac)
            elapsed = time.time() - t0
            results[f"step_{i}_{tac.split()[0]}"] = elapsed
            if state.is_proved():
                results["status"] = "proved"
                results["total_steps"] = i + 1
                return results
            if not state.goals:
                results["status"] = "stuck"
                results["stuck_at"] = tac
                results["error"] = state.error
                return results

        # Try frame lemmas
        frame_tactics = [
            "apply inc_frame_a_a2.",
            "apply inc_frame_b_a2.",
            "apply inc_frame_a_b2.",
            "apply inc_frame_b_b2.",
        ]
        for tac in frame_tactics:
            t0 = time.time()
            state = client.insert_tactic(theorem_name, tac)
            elapsed = time.time() - t0
            results[f"frame_{tac.split('.')[0]}"] = elapsed
            if state.is_proved():
                results["status"] = "proved"
                return results

        results["status"] = "incomplete"
        results["goals_remaining"] = len(state.goals) if state.goals else 0
        return results

    finally:
        client.stop()
        vfile.unlink(missing_ok=True)


def test_frame_two_calls_interactive():
    """End-to-end: generate Coq, attempt proof, measure time."""
    source = """def inc(x: int):
    assert x >= 0
    result = x + 1
    assert result == x + 1
    return result

def frame_two_calls(a: int, b: int):
    assert a >= 0; assert b >= 0
    if __debug__: old_a = a; old_b = b
    a2 = inc(a)
    b2 = inc(b)
    assert a == old_a
    assert b == old_b
    result = a2 + b2
    assert result == a + b + 2
    return result"""

    print("Generating Coq...")
    t0 = time.time()
    coq = generate_coq(source, "frame_two_calls")
    gen_time = time.time() - t0
    print(f"  Generated {len(coq)} chars in {gen_time:.1f}s")

    # Check __debug__ fix
    if "BTrue" in coq:
        print("  __debug__ compiled to BTrue ✓")
    else:
        print("  __debug__ NOT compiled to BTrue ✗")

    # Check frame lemmas
    if "inc_frame_a_a2" in coq:
        print("  Frame lemmas generated ✓")
    else:
        print("  No frame lemmas ✗")
        return

    print("\nAttempting interactive proof via rocq-piler...")
    total_t0 = time.time()
    results = try_prove_interactive(coq, "frame_two_calls_correct")
    total = time.time() - total_t0

    print(f"\nResults ({total:.1f}s total):")
    for k, v in results.items():
        if isinstance(v, float):
            print(f"  {k}: {v:.1f}s")
        else:
            print(f"  {k}: {v}")


if __name__ == "__main__":
    test_frame_two_calls_interactive()
