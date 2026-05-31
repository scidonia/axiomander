"""
Integration tests for rocq-piler MCP.

Verifies that rocq-piler can:
1. Start the MCP server
2. Open a Coq file and focus on a proof
3. Insert tactics interactively
4. Complete proofs that require multi-step tactic sequences
"""

import os
import subprocess
import tempfile
import time
from pathlib import Path

import pytest

from oracle.rocq_robot_client import RocqRobotClient, GoalState

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
IMPORT_PREAMBLE = """From Stdlib Require Import ZArith List.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.
"""


@pytest.fixture
def rocq_workspace():
    """Return the build directory that contains compiled .vo files."""
    build_dir = PROJECT_ROOT / "_build" / "default" / "coq"
    return build_dir


def _find_coq_lsp():
    import shutil
    for name in ["coq-lsp", "rocq-lsp", "rocq-robot"]:
        p = shutil.which(name)
        if p:
            return p
    return "coq-lsp"


def _make_client(vfile: Path) -> RocqRobotClient:
    return RocqRobotClient(
        file_path=vfile,
        coq_lsp_path=_find_coq_lsp(),
        workspace_root=PROJECT_ROOT,
        timeout=30.0,
    )


class TestRocqPiler:
    """Basic rocq-piler connectivity and tool tests."""

    def test_mcp_server_starts(self, rocq_workspace):
        """Verify rocq-piler MCP server starts and discovers tools."""
        with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False) as f:
            f.write(IMPORT_PREAMBLE + "\nLemma trivial_test : 1 = 1.\nProof. Admitted.\n")
            vpath = Path(f.name)

        try:
            client = _make_client(vpath)
            ok = client.start()
            assert ok, "MCP server failed to start"
            assert len(client._tools) > 0, "No tools discovered"
            # Verify key tools are available
            tool_names = set(client._tools.keys())
            assert "focus_proof" in tool_names, "focus_proof missing"
            assert "insert_tactic" in tool_names, "insert_tactic missing"
        finally:
            client.stop() if 'client' in dir() else None
            vpath.unlink(missing_ok=True)

    def test_focus_trivial_proof(self, rocq_workspace):
        """Verify focus_proof returns goals for a simple Admitted lemma."""
        with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False) as f:
            f.write(IMPORT_PREAMBLE + "\nLemma trivial_test : 1 = 1.\nProof. Admitted.\n")
            vpath = Path(f.name)

        try:
            client = _make_client(vpath)
            assert client.start()
            state = client.focus("trivial_test")
            assert state is not None
            # Should show 1 goal
            assert len(state.goals) > 0, f"No goals returned: {state.error}"
        finally:
            client.stop() if 'client' in dir() else None
            vpath.unlink(missing_ok=True)

    def test_insert_reflexivity_proves(self, rocq_workspace):
        """Verify insert_tactic can prove 1=1 with reflexivity."""
        with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False) as f:
            f.write(IMPORT_PREAMBLE + "\nLemma simple_refl : 1 = 1.\nProof. Admitted.\n")
            vpath = Path(f.name)

        try:
            client = _make_client(vpath)
            assert client.start()
            state = client.insert_tactic("simple_refl", "reflexivity.")
            assert state.is_proved(), f"reflexivity should close 1=1: {state.error}"
        finally:
            client.stop() if 'client' in dir() else None
            vpath.unlink(missing_ok=True)

    def test_multi_step_intros_lemma(self, rocq_workspace):
        """Verify multi-step proof: intros; split; reflexivity; reflexivity."""
        with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False) as f:
            f.write(
                IMPORT_PREAMBLE
                + "\nLemma intros_split : forall a:Z, a = a /\\ a = a.\n"
                + "Proof. Admitted.\n"
            )
            vpath = Path(f.name)

        try:
            client = _make_client(vpath)
            assert client.start()

            state = client.insert_tactic("intros_split", "intros a.")
            assert not state.is_proved(), "should still have goals after intros"
            assert not state.error, f"intros failed: {state.error}"

            state = client.insert_tactic("intros_split", "split.")
            assert not state.is_proved(), "should have 2 subgoals after split"

            state = client.insert_tactic("intros_split", "reflexivity.")
            assert not state.is_proved(), "should have 1 subgoal after 1st reflexivity"

            state = client.insert_tactic("intros_split", "reflexivity.")
            assert state.is_proved(), f"should be proved after 2nd reflexivity: {state.error}"
        finally:
            client.stop() if 'client' in dir() else None
            vpath.unlink(missing_ok=True)


class TestRocqPilerAxiomander:
    """Integration tests verifying axiomander-generated goals with rocq-piler."""

    def _generate_proof_file(self, source: str, func_name: str) -> Path:
        """Generate a .v file with the proof obligation for a Python function."""
        from oracle.mcp_server import _verify_function

        result = _verify_function(source, func_name)
        if result is None:
            raise RuntimeError(f"Failed to generate proof for {func_name}")

        # Find the generated .v file
        vfile = Path("/tmp") / f"axiomander_ai_prove_{func_name}.v"
        if not vfile.exists():
            # Try the default path
            vfile = Path("/tmp") / "axiomander_ai_prove.v"
        if not vfile.exists():
            raise RuntimeError(f"No .v file found for {func_name}")
        return vfile

    def test_level1_function_passes(self):
        """A simple function (add) should be provable by level 1 wp_reduce only."""
        source = """def add(a: int, b: int) -> int:
    assert a >= 0
    assert b >= 0
    result = a + b
    assert result == a + b
    return result"""
        from oracle.mcp_server import _verify_function

        result = _verify_function(source, "add")
        assert result is not None
        assert result.is_proved(), f"add should prove at level 1: {result.error_detail[:200]}"
