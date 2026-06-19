"""
Minimal MCP stdio client for rocq-robot.

Spawns rocq-robot as a subprocess and communicates via MCP JSON-RPC
over stdin/stdout. Provides high-level methods mirroring the MCP tools:
  focus(name) → full proof context
  open_goals(name) → current goals with hypotheses
  insert_tactic(name, tactic) → apply tactic, get new state
  check() → validate the document
"""

import json
import os
import subprocess
import sys
import threading
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class GoalState:
    goals: list[str] = field(default_factory=list)
    hypotheses: list[str] = field(default_factory=list)
    proof_script: str = ""
    bullet_stack: list[str] = field(default_factory=list)
    is_complete: bool = False
    error: str = ""

    def is_proved(self) -> bool:
        return self.is_complete and not self.error


class RocqRobotClient:
    """MCP client for rocq-robot. Communicates via stdio JSON-RPC."""

    def __init__(
        self,
        robot_path: Optional[Path] = None,
        coq_lsp_path: Optional[str] = None,
        workspace_root: Optional[Path] = None,
        file_path: Optional[Path] = None,
        timeout: float = 30.0,
    ):
        if robot_path is None:
            # Default: vendor/rocq-robot/dist/index.js relative to this file
            project_root = Path(__file__).resolve().parent.parent.parent.parent
            robot_path = project_root / "vendor" / "rocq-piler" / "dist" / "index.js"

        if coq_lsp_path is None:
            import shutil
            for name in ["rocq-robot", "rocq-lsp", "coq-lsp"]:
                p = shutil.which(name)
                if p:
                    coq_lsp_path = p
                    break
            if coq_lsp_path is None:
                coq_lsp_path = "coq-lsp"

        if workspace_root is None:
            workspace_root = Path(__file__).resolve().parent.parent.parent.parent

        self.robot_path = Path(robot_path)
        self.coq_lsp_path = coq_lsp_path
        self.workspace_root = Path(workspace_root)
        self.file_path = file_path
        self.timeout = timeout
        self._process: Optional[subprocess.Popen] = None
        self._next_id = 1
        self._tools: dict[str, dict] = {}

    def start(self) -> bool:
        """Start the rocq-robot MCP server subprocess."""
        cmd = [
            "node",
            str(self.robot_path),
            "--coq-lsp-path", self.coq_lsp_path,
        ]
        if self.workspace_root:
            cmd.extend(["--workspace-root", str(self.workspace_root)])
            build_coq = str(Path(self.workspace_root) / "_build" / "default" / "coq")
            cmd.extend(["--coq-lsp-args", f"-R {build_coq},Imp"])

        self._process = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=str(self.workspace_root),
        )

        # Initialize MCP session
        init_resp = self._request("initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "axiomander", "version": "0.4.0"},
        })
        if not init_resp or "error" in init_resp:
            return False

        # Discover tools
        tools_resp = self._request("tools/list", {})
        if tools_resp and "result" in tools_resp:
            for t in tools_resp["result"].get("tools", []):
                self._tools[t["name"]] = t

        return True

    def stop(self):
        """Stop the MCP server subprocess."""
        if self._process:
            try:
                self._process.stdin.close()
                self._process.stdout.close()
                self._process.terminate()
                self._process.wait(timeout=3)
            except Exception:
                try:
                    self._process.kill()
                except Exception:
                    pass
            self._process = None

    def focus(self, proof_name: str) -> GoalState:
        """Get full proof context (like coq_focus)."""
        resp = self._request("tools/call", {
            "name": "focus_proof",
            "arguments": {"file": str(self.file_path), "name": proof_name},
        })
        return self._parse_focus_response(resp)

    def open_goals(self, proof_name: str) -> GoalState:
        """Get current goals with hypotheses (like coq_open_goals)."""
        resp = self._request("tools/call", {
            "name": "open_goals",
            "arguments": {"file": str(self.file_path), "name": proof_name},
        })
        return self._parse_goals_response(resp)

    def insert_tactic(self, proof_name: str, tactic: str) -> GoalState:
        """Insert a tactic and get new state (like coq_insert_tactic)."""
        resp = self._request("tools/call", {
            "name": "insert_tactic",
            "arguments": {
                "file": str(self.file_path),
                "name": proof_name,
                "tactic": tactic,
            },
        })
        return self._parse_focus_response(resp)

    def try_tactic(self, proof_name: str, tactic: str) -> GoalState:
        """Try a tactic speculatively (like coq_try_tactic)."""
        resp = self._request("tools/call", {
            "name": "try_step",
            "arguments": {
                "file": str(self.file_path),
                "name": proof_name,
                "tactic": tactic,
            },
        })
        return self._parse_goals_response(resp)

    def check(self) -> str:
        """Force document checking."""
        resp = self._request("tools/call", {
            "name": "check_file",
            "arguments": {"file": str(self.file_path)},
        })
        return self._extract_text(resp)

    def search(self, pattern: str) -> list[str]:
        """Search for lemmas/theorems."""
        resp = self._request("tools/call", {
            "name": "search_lemmas",
            "arguments": {"file": str(self.file_path), "pattern": pattern},
        })
        text = self._extract_text(resp)
        return text.split("\n") if text else []

    def about(self, term: str) -> str:
        """Get information about a term (speculative)."""
        resp = self._request("tools/call", {
            "name": "inspect_about",
            "arguments": {"file": str(self.file_path), "term": term},
        })
        return self._extract_text(resp)

    def check_term(self, term: str) -> str:
        """Check the type of an expression (speculative)."""
        resp = self._request("tools/call", {
            "name": "inspect_term",
            "arguments": {"file": str(self.file_path), "term": term},
        })
        return self._extract_text(resp)

    def require_lib(self, lib: str) -> str:
        """Import a library speculatively (doesn't modify the file)."""
        resp = self._request("tools/call", {
            "name": "require_lib",
            "arguments": {"file": str(self.file_path), "lib": lib},
        })
        return self._extract_text(resp)

    def locate(self, thing: str) -> str:
        """Find where a term is defined."""
        resp = self._request("tools/call", {
            "name": "locate_term",
            "arguments": {"file": str(self.file_path), "thing": thing},
        })
        return self._extract_text(resp)

    # ── Internal ──────────────────────────────────────────────────

    def _request(self, method: str, params: dict) -> Optional[dict]:
        """Send an MCP JSON-RPC request and wait for the response."""
        if self._process is None or self._process.stdin is None:
            return None

        req_id = self._next_id
        self._next_id += 1
        request = {
            "jsonrpc": "2.0",
            "id": req_id,
            "method": method,
            "params": params,
        }
        req_str = json.dumps(request) + "\n"

        try:
            self._process.stdin.write(req_str)
            self._process.stdin.flush()

            line = self._process.stdout.readline()
            if line:
                return json.loads(line)
        except Exception:
            pass
        return None

    def _extract_text(self, resp: Optional[dict]) -> str:
        """Extract text content from an MCP tool response."""
        if not resp or "result" not in resp:
            return ""
        result = resp["result"]
        for c in result.get("content", []):
            if c.get("type") == "text":
                return c.get("text", "")
        return ""

    def _parse_goals_response(self, resp: Optional[dict]) -> GoalState:
        text = self._extract_text(resp)
        if not text:
            return GoalState(error="no response from MCP server")
        if "error" in text.lower() or "failed" in text.lower():
            return GoalState(error=text[:500])
        if "0 goals" in text or "no goals" in text or "done" in text.lower() or "proof finished" in text.lower():
            return GoalState(is_complete=True, proof_script=text)
        return GoalState(goals=[text])

    def _parse_focus_response(self, resp: Optional[dict]) -> GoalState:
        text = self._extract_text(resp)
        if not text:
            return GoalState(error="no response from MCP server")
        if "error" in text.lower():
            return GoalState(error=text[:500])
        if "0 goals" in text.lower() or "done" in text.lower() or "proof finished" in text.lower():
            return GoalState(is_complete=True, proof_script=text)

        # coq_focus response has: goals, proof script, bullet info
        goals = text.split("-- goals --")[0].strip() if "-- goals --" in text else text
        return GoalState(
            goals=[goals],
            proof_script=text,
        )
