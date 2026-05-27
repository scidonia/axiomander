"""
LangGraph Coq proof oracle using rocq-robot MCP tools.

The LLM has direct function-calling access to:
  coq_focus(name) → full proof context (goals, proof script, bullet stack)
  coq_open_goals(name) → current goals with hypotheses
  coq_try_tactic(name, tactic) → speculative tactic execution
  coq_insert_tactic(name, tactic) → apply tactic, auto-bullets
  coq_search(pattern) → search available lemmas
  coq_check() → force document checking
  coq_check_term(term) → check type of expression
  coq_about(term) → get info about a definition
"""

import os
import sys
import json
import time
import tempfile
from pathlib import Path
from typing import Optional

# ── Safe imports ───────────────────────────────────────────────────

try:
    from langchain_openai import ChatOpenAI
    from langgraph.graph import StateGraph, END
    from langgraph.graph.message import add_messages
    from langgraph.prebuilt import ToolNode
    from langgraph.checkpoint.memory import MemorySaver
    from typing_extensions import TypedDict, Annotated
except ImportError:
    ChatOpenAI = None
    StateGraph = None
    END = None
    ToolNode = None
    MemorySaver = None
    TypedDict = None
    Annotated = None

from oracle.rocq_robot_client import RocqRobotClient
from oracle.mcp_server import BUILD_DIR


class ProofState(TypedDict):
    messages: Annotated[list, add_messages]
    proof_script: str
    error: str


# ── Global session state ───────────────────────────────────────────

_client: Optional[RocqRobotClient] = None
_tmp_v_file: Optional[Path] = None
PROOF_NAME = "axiomander_proof"


def _c():
    global _client
    if not _client:
        raise RuntimeError("No active rocq-robot session")
    return _client


# ── MCP tools exposed to the LLM ───────────────────────────────────

def coq_focus() -> str:
    """Get full proof context: goals, hypotheses, proof script, bullet stack."""
    result = _c().focus(PROOF_NAME)
    if result.error:
        return f"ERROR: {result.error[:300]}"
    if result.is_complete:
        return "PROOF COMPLETE — all goals closed. The theorem is proved."
    return result.proof_script


def coq_open_goals() -> str:
    """Get current goals with hypotheses (Prev mode)."""
    result = _c().open_goals(PROOF_NAME)
    if result.error:
        return f"ERROR: {result.error[:300]}"
    if result.is_complete:
        return "No open goals — proof may be complete."
    goals = "\n".join(result.goals[:5]) if result.goals else "(no goals displayed)"
    hyps = "\n".join(result.hypotheses[-20:]) if result.hypotheses else "(no hypotheses)"
    return f"GOALS:\n{goals}\n\nHYPOTHESES:\n{hyps}"


def coq_try_tactic(tactic: str) -> str:
    """Try a tactic speculatively. Does NOT modify the proof script.
    Use this to TEST a tactic before committing with coq_insert_tactic."""
    result = _c().try_tactic(PROOF_NAME, tactic)
    if result.error:
        return f"FAILED: {result.error[:300]}"
    if result.is_complete:
        return "Tactic succeeded — proof appears complete. Use coq_insert_tactic to commit."
    goals = "\n".join(result.goals[:3]) if result.goals else "(no goals)"
    hyps = "\n".join(result.hypotheses[-10:]) if result.hypotheses else ""
    return f"OK. Result:\nGOALS:\n{goals}\n\nHYPOTHESES:\n{hyps}"


def coq_insert_tactic(tactic: str) -> str:
    """Insert a tactic into the proof script. Auto-prepends bullet prefix.
    Returns the updated proof context."""
    result = _c().insert_tactic(PROOF_NAME, tactic)
    if result.error:
        return f"FAILED: {result.error[:300]}"
    if result.is_complete:
        return "PROOF COMPLETE — all goals closed. Theorem proved!"
    return result.proof_script


def coq_search(pattern: str) -> str:
    """Search for lemmas/theorems matching PATTERN.
    Example: '(_ + 0 = _)' or 'plus_n_O'"""
    results = _c().search(pattern)
    if not results:
        return "No matches found."
    return "\n".join(results[:20])


def coq_check() -> str:
    """Force document checking. Returns status."""
    return _c().check()


def coq_about(term: str) -> str:
    """Get information about a Coq term/definition (speculative)."""
    result = _c().about(term)
    return result if result else "No information available."


def coq_check_term(term: str) -> str:
    """Check the type of a Coq expression (speculative)."""
    result = _c().check_term(term)
    return result if result else "No information available."


tools = [
    coq_focus, coq_open_goals, coq_insert_tactic,
    coq_search, coq_check,
    coq_about, coq_check_term,
]


# ── LLM ────────────────────────────────────────────────────────────

def _make_llm():
    api_key = os.environ.get("DEEPSEEK_API_KEY") or os.environ.get("ORACLE_API_KEY") or ""
    base_url = os.environ.get("ORACLE_API_URL") or "https://api.deepseek.com/v1"
    model = os.environ.get("ORACLE_MODEL") or "deepseek-chat"
    return ChatOpenAI(
        api_key=api_key,
        base_url=base_url,
        model=model,
        temperature=0,
        max_tokens=4096,
    )


SYSTEM_PROMPT = """You are a Coq proof assistant with rocq-robot MCP tools.

Tools:
- coq_focus() — full proof context: goals, proof script, table of contents
- coq_open_goals() — current goals + hypotheses
- coq_insert_tactic(tactic) — COMMIT a tactic to the proof
- coq_search(pattern) — find lemmas
- coq_about(term) / coq_check_term(term) — inspect definitions

Strategy:
1. Start with coq_focus().
2. For each goal, call coq_insert_tactic() with ONE tactic.
   Available: intros, wp_prove, split, lia, reflexivity, auto,
   unfold, rewrite, apply, destruct, eexists.
3. Check coq_focus() after each tactic.
4. When coq_focus says all goals closed, you're DONE.
5. Keep it SHORT. Most proofs need 1-5 tactics."""


# ── Graph ──────────────────────────────────────────────────────────

def build_graph() -> StateGraph:
    llm = _make_llm()
    llm_with_tools = llm.bind_tools(tools)

    workflow = StateGraph(ProofState)

    def assistant(state: ProofState) -> ProofState:
        response = llm_with_tools.invoke(state["messages"])
        return {"messages": [response]}

    workflow.add_node("assistant", assistant)
    workflow.add_node("tools", ToolNode(tools))
    workflow.set_entry_point("assistant")

    def route(state: ProofState) -> str:
        last = state["messages"][-1]
        if hasattr(last, 'tool_calls') and last.tool_calls:
            return "tools"
        return END

    workflow.add_conditional_edges("assistant", route)
    workflow.add_edge("tools", "assistant")

    return workflow.compile(checkpointer=MemorySaver())


# ── Public API ─────────────────────────────────────────────────────

def run_langgraph_oracle(
    preamble: str,
    max_steps: int = 20,
) -> tuple[bool, str, str]:
    """Run the LangGraph proof agent via rocq-robot MCP tools.

    Writes the preamble to a temp .v file, starts rocq-robot MCP server,
    and lets the LLM drive the proof via tool calls.

    Returns:
        (success, proof_script, error_message)
    """
    global _client, _tmp_v_file

    if ChatOpenAI is None:
        return False, "", "langgraph not installed"

    from oracle.client import _consume_credit

    # Estimate and consume credits
    est_calls = min(max_steps, 10)
    for _ in range(est_calls):
        if not _consume_credit():
            return False, "", "Credit budget exhausted"

    # Write preamble to temp .v file
    fd, tmp_path = tempfile.mkstemp(suffix=".v", prefix="axiomander_")
    os.close(fd)
    _tmp_v_file = Path(tmp_path)
    _tmp_v_file.write_text(preamble)

    # Start rocq-robot MCP server
    client = RocqRobotClient(
        file_path=_tmp_v_file,
        timeout=60,
    )
    _client = client

    if not client.start():
        _tmp_v_file.unlink(missing_ok=True)
        return False, "", "Failed to start rocq-robot MCP server"

    try:
        # Run the agent
        initial_state = {
            "messages": [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": "Prove this theorem. Call coq_focus() to see the proof state, then use coq_try_tactic() and coq_insert_tactic()."}
            ],
            "proof_script": "",
            "error": "",
        }

        graph = build_graph()
        config = {"configurable": {"thread_id": "proof"}, "recursion_limit": max_steps * 5}
        final = graph.invoke(initial_state, config)

        # Check if proof succeeded
        proved = False
        for msg in final.get("messages", []):
            content = str(getattr(msg, 'content', ''))
            if "PROVED" in content or "PROOF COMPLETE" in content:
                proved = True
                break

        # Read the proof script from the file
        proof_script = ""
        if _tmp_v_file.exists():
            full = _tmp_v_file.read_text()
            idx = full.rfind("Proof.")
            if idx >= 0:
                proof_script = full[idx:].strip()

        return proved, proof_script, ""

    except Exception as e:
        import traceback
        return False, "", f"{e}\n{traceback.format_exc()[-300:]}"

    finally:
        client.stop()
        _client = None
        try:
            _tmp_v_file.unlink(missing_ok=True)
        except Exception:
            pass
        _tmp_v_file = None
