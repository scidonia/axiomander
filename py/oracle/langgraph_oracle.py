"""
LangGraph Coq proof oracle.

The LLM has direct function-calling access to coq-lsp:
  get_goals() → current proof state
  try_tactic(tactic: str) → apply tactic, get result
  finish_proof() → close with Qed
"""

import os
import sys
import json
import time
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

from oracle.coqpyt_session import CoqpytSession
from oracle.mcp_server import BUILD_DIR


class ProofState(TypedDict):
    messages: Annotated[list, add_messages]
    tactics_used: list[str]
    error: str


# ── Coq-lsp tools ──────────────────────────────────────────────────

_session: Optional[CoqpytSession] = None


def _s():
    global _session
    if not _session:
        raise RuntimeError("No active coq-lsp session")
    return _session


def get_goals() -> str:
    """Get current proof state: goals with hypotheses."""
    s = _s()
    state = s.get_goals()
    goals = "\n".join(state.goals[:3]) if state.goals else "(no open goals — proof may be complete)"
    hyps = "\n".join(state.hypotheses[-15:]) if state.hypotheses else "(no hypotheses)"
    return f"GOALS:\n{goals}\n\nHYPOTHESES:\n{hyps}"


def try_tactic(tactic: str) -> str:
    """Apply a Coq tactic. Returns new goal state or error."""
    s = _s()
    t = tactic.strip()
    if not t.endswith('.'):
        t += '.'
    result = s.try_tactic(t)
    if result.error:
        return f"FAILED: {result.error[:300]}"
    if result.is_proved():
        return "PROOF COMPLETE — call finish_proof to close with Qed."
    if not result.goals:
        return "No open goals. Call finish_proof to check if proof is complete."
    goals = "\n".join(result.goals[:3])
    hyps = "\n".join(result.hypotheses[-10:]) if result.hypotheses else ""
    return f"OK. New goals:\nGOALS:\n{goals}\n\nHYPOTHESES:\n{hyps}"


def finish_proof() -> str:
    """Close the proof with Qed."""
    s = _s()
    if s.finish_proof("Qed."):
        return "PROVED! Theorem closed with Qed."
    return "Qed FAILED — proof not complete. Check remaining goals."


tools = [get_goals, try_tactic, finish_proof]


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


SYSTEM_PROMPT = """You are a Coq proof assistant with coq-lsp access.

Available tools:
- get_goals() — see current goals and hypotheses
- try_tactic(tactic) — apply one Coq tactic (e.g. 'intros', 'wp_prove', 'split')
- finish_proof() — close with Qed

Strategy:
1. Call get_goals() first to see the proof state.
2. For each goal, call try_tactic() with ONE tactic.
   Available tactics: intros, wp_prove, wp_reduce, split, lia,
   reflexivity, auto, unfold, rewrite, apply, destruct, eexists.
3. If a tactic fails, try a different approach.
4. When get_goals shows no goals, call finish_proof().
5. If finish_proof fails, the proof isn't done — try more tactics.

Keep proofs SHORT. Most need 1-5 tactics total."""


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
    """Run the LangGraph proof agent.

    Args:
        preamble: Full Coq source with definitions + theorem + 'Proof.'
        max_steps: Budget (LLM interactions, not API calls)

    Returns:
        (success, proof_script, error_message)
    """
    global _session

    if ChatOpenAI is None:
        return False, "", "langgraph not installed"

    from oracle.client import _consume_credit

    session = CoqpytSession(BUILD_DIR, timeout=60)
    _session = session
    proof_script = ""

    try:
        # Check budget
        est_calls = min(max_steps, 10)
        for _ in range(est_calls):
            if not _consume_credit():
                return False, "", "Credit budget exhausted"

        # Load preamble into coq-lsp
        session.load(preamble)

        # Run LangGraph agent
        initial_state = {
            "messages": [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": "Prove this theorem. Start by calling get_goals."}
            ],
            "tactics_used": [],
            "error": "",
        }

        graph = build_graph()
        config = {"configurable": {"thread_id": "proof"}, "recursion_limit": max_steps * 3}
        final = graph.invoke(initial_state, config)

        # Check if proof succeeded by looking for PROVED message
        proved = False
        for msg in final.get("messages", []):
            content = str(getattr(msg, 'content', ''))
            if "PROVED" in content:
                proved = True
                break

        if proved:
            # Extract actual proof script from session text
            full_text = getattr(session, '_text', '')
            # Use rfind to get the LAST Proof. (theorem's, not any lemma's)
            proof_idx = full_text.rfind("Proof.")
            if proof_idx >= 0:
                script = full_text[proof_idx:]
                # Clean up: strip Admitted fallback, normalize newlines
                import re
                script = re.sub(r'\nAdmitted\.\s*\n', '\n', script)
                script = script.strip()
                proof_script = script
            else:
                proof_script = "Proof.\nQed."

        return proved, proof_script, ""

    except Exception as e:
        import traceback
        return False, "", f"{e}\n{traceback.format_exc()[-300:]}"

    finally:
        try:
            session.close(timeout=3)
        except Exception:
            pass
        _session = None
