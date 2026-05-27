"""
LangGraph Coq proof oracle using langchain-mcp-adapters + rocq-robot.

The LLM has direct access to rocq-robot MCP tools:
  coq_focus(file, name)          → full proof context
  coq_insert_tactic(file, name, tactic) → execute tactic, auto-Qed on completion

Uses langchain-mcp-adapters as the MCP client — no bespoke JSON-RPC.
"""

import asyncio
import os
import re
import tempfile
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
    from langchain_core.messages import ToolMessage
    from typing_extensions import TypedDict, Annotated
except ImportError:
    ChatOpenAI = None
    StateGraph = None
    END = None
    ToolNode = None
    MemorySaver = None
    TypedDict = None
    Annotated = None

from langchain_mcp_adapters.sessions import create_session, StdioConnection
from langchain_mcp_adapters.tools import load_mcp_tools


class ProofState(TypedDict):
    messages: Annotated[list, add_messages]
    proof_script: str
    error: str


# ── Coq LSP finder ─────────────────────────────────────────────────

def _find_coq_lsp() -> str:
    import shutil
    for name in ("rocq-robot", "rocq-lsp", "coq-lsp"):
        path = shutil.which(name)
        if path:
            return path
    return "coq-lsp"


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


SYSTEM_PROMPT = """You are a Coq proof assistant using rocq-robot MCP tools.

Tools:
  focus_proof(file, name)  — show proof state and goals
  insert_tactic(file, name, tactic)  — run a tactic

CRITICAL RULES:
1. insert_tactic automatically applies Qed. when the proof is complete.
   You will see "done — Qed applied" in the output.
2. NEVER manually insert "Qed." — the tool does it for you.
3. If focus_proof shows "Proof complete" or "done", stop. The proof is done.
4. If insert_tactic shows "next: N goal(s)", you need more tactics.

Workflow:
1. focus_proof(file, name)  — see the goal
2. insert_tactic(file, name, tactic)  — prove it
3. Repeat 2 until "done — Qed applied" or focus_proof shows "Proof complete"
4. Stop — do NOT insert Qed. yourself.
5. After every insert_tactic, call focus_proof to verify the goal state.
   If focus_proof shows 1+ goals, continue.  Only stop at "Proof complete" or
   "done — Qed applied".  apply alone does NOT close the goal — it creates subgoals.
6. Use search_lemmas to discover available tactics and lemmas when stuck.

For IMP verification goals (wp, CSeq, CCall), use wp_seq_decompose to split
a CSeq and wp_ccall_frame for callee frame conditions.  Both are available
from the WpTactics import."""


# ── Graph ──────────────────────────────────────────────────────────

def build_graph(tools: list) -> StateGraph:
    llm = _make_llm()
    llm_with_tools = llm.bind_tools(tools)

    workflow = StateGraph(ProofState)
    tool_map = {t.name: t for t in tools}

    async def assistant(state: ProofState) -> ProofState:
        response = await llm_with_tools.ainvoke(state["messages"])
        return {"messages": [response]}

    async def tool_executor(state: ProofState) -> ProofState:
        """Execute tool calls manually, bypassing ToolNode."""
        last = state["messages"][-1]
        results = []
        for tc in last.tool_calls:
            tool = tool_map.get(tc["name"])
            if tool:
                try:
                    result = await tool.ainvoke(tc["args"])
                except Exception as e:
                    result = f"Tool error: {e}"
            else:
                result = f"Unknown tool: {tc['name']}"
            results.append(ToolMessage(content=str(result), tool_call_id=tc["id"]))
        return {"messages": results}

    workflow.add_node("assistant", assistant)
    workflow.add_node("tools", tool_executor)
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

    Uses langchain-mcp-adapters to auto-wrap rocq-robot's MCP tools.
    The LLM drives the proof via coq_focus/coq_insert_tactic.

    Returns:
        (success, proof_script, error_message)
    """
    global _tmp_v_file

    thm_match = re.search(r'(?:Theorem|Lemma)\s+(\w+)', preamble)
    # If there are multiple theorems/lemmas, find the last one (the main goal)
    all_matches = re.findall(r'(?:Theorem|Lemma)\s+(\w+)', preamble)
    proof_name = all_matches[-1] if all_matches else "axiomander_proof"

    if ChatOpenAI is None:
        return False, "", "langgraph not installed"

    from oracle.client import _consume_credit

    est_calls = min(max_steps, 5)
    for _ in range(est_calls):
        if not _consume_credit():
            return False, "", "Credit budget exhausted"

    project_root = Path(__file__).resolve().parent.parent.parent

    # Write temp .v file
    fd, tmp_path = tempfile.mkstemp(suffix=".v", prefix="axiomander_")
    os.close(fd)
    _tmp_v_file = Path(tmp_path)
    _tmp_v_file.write_text(preamble + "\nAdmitted.")

    robot_js = project_root / "vendor" / "rocq-robot" / "dist" / "index.js"
    file_path = str(_tmp_v_file)

    async def _run():
        import sys as _sys_stderr
        def _log(msg):
            print(f"  [lg-oracle] {msg}", file=_sys_stderr.stderr, flush=True)

        _log(f"connecting, file={file_path}")
        coq_lsp = _find_coq_lsp()
        build_coq = str(project_root / "_build" / "default" / "coq")
        connection: StdioConnection = {
            "transport": "stdio",
            "command": "node",
            "args": [
                str(robot_js),
                "--coq-lsp-path", coq_lsp,
                "--coq-lsp-args", f"-R {build_coq},Imp",
            ],
            "cwd": str(project_root),
        }

        async with create_session(connection) as session:
            await session.initialize()
            _log("session init done")
            all_tools = await load_mcp_tools(session)

            focus_tool = next((t for t in all_tools if t.name == "focus_proof"), None)
            insert_tool = next((t for t in all_tools if t.name == "insert_tactic"), None)
            if not focus_tool or not insert_tool:
                return False, "", "rocq-robot missing required tools"

            tools = [focus_tool, insert_tool]
            _log(f"tools loaded, building graph")

            # Quick pre-flight: call focus on the file directly before the graph
            try:
                r = await focus_tool.ainvoke({"file": file_path, "name": proof_name})
                _log(f"pre-flight OK ({len(r[0]['text'])} chars)")
            except Exception as e:
                _log(f"pre-flight FAILED: {e}")

            graph = build_graph(tools)

            initial_state = {
                "messages": [
                    {"role": "system", "content": SYSTEM_PROMPT},
                    {"role": "user", "content": (
                        f"Prove the lemma '{proof_name}'.\n\n"
                        f"Always pass file=\"{file_path}\" and name=\"{proof_name}\" "
                        f"to every tool call. Use focus_proof to see goals, insert_tactic to prove them."
                    )}
                ],
                "proof_script": "",
                "error": "",
            }

            config = {"configurable": {"thread_id": "proof"}, "recursion_limit": max_steps * 5}
            _log(f"invoking graph, recursion_limit={max_steps * 5}")
            try:
                final = await graph.ainvoke(initial_state, config)
                _log(f"graph done, {len(final.get('messages', []))} messages")
            except Exception as exc:
                _log(f"graph failed: {exc}")
                return False, _tmp_v_file.read_text() if _tmp_v_file.exists() else "", str(exc)[:500]

            proved = False
            for msg in final.get("messages", []):
                content = str(getattr(msg, 'content', ''))
                if "done - Qed applied" in content or "Proof complete" in content:
                    proved = True
                    break

            proof_script = ""
            if _tmp_v_file.exists():
                full = _tmp_v_file.read_text()
                idx = full.rfind("Proof.")
                if idx >= 0:
                    proof_script = full[idx:].strip()

            # Save transcript
            import json as _json
            ts = int(time.time())
            transcripts_dir = project_root / ".axiomander" / "transcripts"
            transcripts_dir.mkdir(parents=True, exist_ok=True)
            transcript = {
                "timestamp": ts, "success": proved,
                "credits_used": getattr(__import__('oracle.client'), '_credits_used', 0),
                "messages": [
                    {"role": str(getattr(m, 'type', 'unknown')),
                     "content": str(getattr(m, 'content', ''))[:500],
                     "tool_calls": str(getattr(m, 'tool_calls', None))[:500] if hasattr(m, 'tool_calls') else None}
                    for m in final.get("messages", [])
                ],
                "proof_script": proof_script,
            }
            (transcripts_dir / f"transcript_{ts}.json").write_text(_json.dumps(transcript, indent=2))

            return proved, proof_script, ""

    try:
        return asyncio.run(_run())
    except Exception as e:
        import traceback
        return False, "", f"{e}\n{traceback.format_exc()[-300:]}"
