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


SYSTEM_PROMPT = """You are a Coq proof assistant using rocq-piler MCP tools.

Tools:
  focus_proof(file, name)  — show proof state and goals
  insert_tactic(file, name, tactic)  — run a tactic
  check_file(file)  — verify the whole file and see which proofs remain

CRITICAL RULES:
1. insert_tactic automatically applies Qed. when the proof is complete.
   You will see "done — Qed applied" in the output.
2. NEVER manually insert "Qed." — the tool does it for you.
3. If focus_proof shows "Proof complete" or "done", stop. The proof is done.
4. If insert_tactic shows "next: N goal(s)", you need more tactics.

Workflow:
1. Use focus_proof(file, name) on one unsolved theorem/lemma name.
2. Use insert_tactic(file, name, tactic) to prove it.
3. Repeat until that theorem is complete.
4. Then move to the next unsolved theorem/lemma name in the provided list.
5. Use check_file(file) near the end to confirm no admitted targets remain.
6. If focus_proof says "Proof complete" but check_file still reports admitted targets,
   trust check_file and continue working on the UNSOLVED names.
7. Stop — do NOT insert Qed. yourself.
8. After every insert_tactic, call focus_proof to verify the goal state.
   If focus_proof shows 1+ goals, continue. Only stop a proof when it says
   "Proof complete" or "done — Qed applied".

For IMP verification goals (wp, CSeq, CCall), prefer this workflow:

1. If the theorem already contains stage lemmas such as `foo_stage_1_correct`,
   `foo_stage_2_correct`, and a post lemma `foo_post`, USE THEM.
2. For sequential composition, use `wp_seq_decompose`.

`wp_seq_decompose` signature:

  forall c1 c2 (Q1 Q2 : assertion) s,
    wp c1 Q1 s ->
    (forall s', Q1 s' -> wp c2 Q2 s') ->
    wp (CSeq c1 c2) Q2 s.

When to use it:
- Goal shape: `wp (CSeq c1 c2) Q s`
- Strategy:
  - `apply (wp_seq_decompose c1 c2 Q1 Q _).`
  - first subgoal: apply the stage lemma for `c1`
  - second subgoal: `intros s' Hq.` then unfold `Q1` and continue

Typical staged proof skeleton:

  apply (wp_seq_decompose s1 rest (Q_name_1 params...) post _).
  { apply foo_stage_1_correct. ... }
  { intros s1 Hq. unfold Q_name_1 in Hq. destruct Hq as [...]. ... }

For callee frame conditions, use either generated frame lemmas such as
`inc_frame_a_a2` / `inc_frame_b_b2`, or the generic `wp_ccall_frame`.

If the file contains generated helper lemmas/theorems, prefer applying them
over inventing low-level proofs from scratch.

When the user prompt provides:
- UNSOLVED names: these are the only targets you need to finish
- SOLVED names: do not spend time reproving them; just use them"""


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
    target_names: list[str] | None = None,
    solved_names: list[str] | None = None,
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
    proof_name = (target_names[0] if target_names else None) or (all_matches[-1] if all_matches else "axiomander_proof")

    if ChatOpenAI is None:
        return False, "", "langgraph not installed"

    from axiomander.oracle.client import _consume_credit

    est_calls = min(max_steps, 5)
    for _ in range(est_calls):
        if not _consume_credit():
            return False, "", "Credit budget exhausted"

    project_root = Path(__file__).resolve().parent.parent.parent

    # Write temp .v file
    fd, tmp_path = tempfile.mkstemp(suffix=".v", prefix="axiomander_")
    os.close(fd)
    _tmp_v_file = Path(tmp_path)
    stripped = preamble.rstrip()
    if stripped.endswith("Admitted.") or stripped.endswith("Qed."):
        _tmp_v_file.write_text(preamble)
    else:
        _tmp_v_file.write_text(preamble + "\nAdmitted.")

    robot_js = project_root / "vendor" / "rocq-piler" / "dist" / "index.js"
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
            check_tool = next((t for t in all_tools if t.name == "check_file"), None)
            if not focus_tool or not insert_tool:
                return False, "", "rocq-robot missing required tools"

            tools = [t for t in [focus_tool, insert_tool, check_tool] if t is not None]
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
                        f"Prove all unsolved theorem/lemma targets in this file.\n\n"
                        f"UNSOLVED names: {target_names or [proof_name]}\n"
                        f"SOLVED names: {solved_names or []}\n\n"
                        f"Start with '{proof_name}'. Always pass file=\"{file_path}\". "
                        f"When focusing or inserting tactics, use one of the UNSOLVED names as `name`. "
                        f"Use focus_proof to inspect a target, insert_tactic to prove it, and check_file near the end to confirm all unsolved names are now proved."
                    )}
                ],
                "proof_script": "",
                "error": "",
            }

            recursion_limit = min(max_steps * 5, int(os.environ.get("AXIOMANDER_LLM_RECURSION_LIMIT", "120")))
            timeout_s = int(os.environ.get("AXIOMANDER_LLM_TIMEOUT", "180"))
            config = {"configurable": {"thread_id": "proof"}, "recursion_limit": recursion_limit}
            _log(f"invoking graph, recursion_limit={recursion_limit}, timeout={timeout_s}s")
            try:
                final = await asyncio.wait_for(graph.ainvoke(initial_state, config), timeout=timeout_s)
                _log(f"graph done, {len(final.get('messages', []))} messages")
            except asyncio.TimeoutError:
                _log(f"graph timeout after {timeout_s}s")
                return False, _tmp_v_file.read_text() if _tmp_v_file.exists() else "", f"LangGraph timeout after {timeout_s}s"
            except Exception as exc:
                _log(f"graph failed: {exc}")
                return False, _tmp_v_file.read_text() if _tmp_v_file.exists() else "", str(exc)[:500]

            proved = False
            for msg in final.get("messages", []):
                content = str(getattr(msg, 'content', ''))
                if "done - Qed applied" in content or "Proof complete" in content:
                    proved = True
                    break

            if target_names and _tmp_v_file.exists():
                final_text = _tmp_v_file.read_text()
                remaining = []
                for name in target_names:
                    m = re.search(rf'(?:Theorem|Lemma)\s+{re.escape(name)}\b.*?Proof\.(.*?)(Qed\.|Admitted\.)', final_text, re.DOTALL)
                    if m and m.group(2) == 'Admitted.':
                        remaining.append(name)
                proved = proved and not remaining

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
