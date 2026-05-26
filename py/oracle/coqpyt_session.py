"""
Interactive Coq proof session backed by coq-lsp via coqpyt.

Direct LSP client approach — bypasses ProofFile's complex proof-state tracking.
"""

import os
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional, List

from coqpyt.lsp.structs import TextDocumentItem, TextDocumentIdentifier, Position
from coqpyt.coq.lsp.client import CoqLspClient
from coqpyt.coq.lsp.structs import GoalAnswer


@dataclass
class GoalState:
    """Structured representation of current proof goals."""
    goals: list[str] = field(default_factory=list)
    hypotheses: list[str] = field(default_factory=list)
    is_complete: bool = False
    error: str = ""

    def is_proved(self) -> bool:
        return self.is_complete and not self.error


class CoqpytSession:
    """Interactive Coq proof session using coq-lsp LSP directly.

    Usage:
        with CoqpytSession(build_dir) as session:
            session.load(coq_source)  # theorems + definitions
            goals = session.get_goals()
            session.try_tactic("intros.")
            session.try_tactic("wp_prove.")
            if session.is_proved():
                print("Proof complete!")
    """

    _CHANGE_TEMPLATE = " (changed {} -> {})"

    def __init__(self, build_dir: Path, timeout: int = 60):
        self.build_dir = build_dir.resolve()
        self.timeout = timeout
        self._client: Optional[CoqLspClient] = None
        self._tmp_path: Optional[Path] = None
        self._uri: str = ""
        self._text: str = ""
        self._version: int = 1
        self._tactics: list[str] = []
        self._last_line_end: Optional[Position] = None

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    def load(self, coq_source: str) -> bool:
        """Write a Coq source file, open it with coq-lsp.

        The source should contain everything through the 'Proof.' command
        but NOT the 'Qed.' — leaving the proof open for interaction.
        Returns True if proof mode was entered.
        """
        self._write_temp(coq_source)
        self._text = coq_source

        self._client = CoqLspClient(
            f"file://{self.build_dir}",
            timeout=self.timeout,
            coq_lsp_options=(f"--rec-load-path={self.build_dir},Imp",),
            init_options={
                "max_errors": 120000000,
                "goal_after_tactic": False,
                "show_coq_info_messages": True,
                "eager_diagnostics": False,
            },
        )

        self._client.didOpen(
            TextDocumentItem(self._uri, "coq", 1, self._text)
        )

        goals = self._client.proof_goals(
            TextDocumentIdentifier(self._uri),
            self._last_position(),
        )
        in_proof = goals is not None and goals.goals is not None
        if in_proof:
            self._last_line_end = self._estimate_last_line()
        return in_proof

    def get_goals(self) -> GoalState:
        """Get the current proof goal state."""
        if not self._client:
            return GoalState(error="No active session")

        try:
            goals = self._client.proof_goals(
                TextDocumentIdentifier(self._uri),
                self._last_position(),
            )
        except Exception as e:
            return GoalState(error=str(e)[:500])

        if goals is None or goals.goals is None:
            return GoalState(is_complete=True)

        goal_strs = []
        hyps = []
        for g in goals.goals.goals:
            pp = g.pp if hasattr(g, 'pp') else str(g)
            goal_strs.append(pp)
            h = g.hyp if hasattr(g, 'hyp') else ""
            if h:
                for hyp in h if isinstance(h, list) else [h]:
                    hyps.append(hyp.pp if hasattr(hyp, 'pp') else str(hyp))

        return GoalState(goals=goal_strs, hypotheses=hyps)

    def try_tactic(self, tactic: str) -> GoalState:
        """Apply a tactic and return the new goal state."""
        if not self._client:
            return GoalState(error="No active session")

        tactic = tactic.strip()
        if not tactic.endswith('.'):
            tactic += '.'
        if tactic in ('Qed.', 'Defined.', 'Admitted.'):
            return GoalState(error="Cannot send Qed/Defined/Admitted via try_tactic")

        old_state = self.get_goals()
        if old_state.is_proved():
            return GoalState(is_complete=True)

        try:
            self._append_text(f"\n{tactic}")
            self._tactics.append(tactic)
        except Exception as e:
            return GoalState(error=str(e)[:500])

        import time
        time.sleep(0.1)
        new_state = self.get_goals()
        return new_state

    def pop_tactic(self) -> GoalState:
        """Remove the last tactic by truncating the file."""
        if not self._client or not self._tactics:
            return GoalState(error="No tactics to pop")

        removed = self._tactics.pop()
        search = f"\n{removed}"
        last_pos = self._text.rfind(search)
        if last_pos == -1:
            return GoalState(error=f"Tactic '{removed}' not found in source")

        self._text = self._text[:last_pos]
        self._version += 1

        from coqpyt.lsp.structs import VersionedTextDocumentIdentifier, TextDocumentContentChangeEvent
        self._client.didChange(
            VersionedTextDocumentIdentifier(self._uri, self._version),
            [TextDocumentContentChangeEvent(None, None, self._text)],
        )

        self._last_line_end = self._estimate_last_line()
        return self.get_goals()

    def is_proved(self) -> bool:
        """Check if the current proof is complete."""
        state = self.get_goals()
        return state.is_proved()

    def finish_proof(self, end_cmd: str = "Qed.") -> bool:
        """Close the proof with Qed, Defined, or Admitted.

        Returns True if the proof is valid (no errors after closing).
        """
        if not self._client:
            return False

        try:
            self._append_text(f"\n{end_cmd}")
        except Exception:
            return False

        state = self.get_goals()
        return state.is_proved()

    def _append_text(self, text: str):
        """Append text to the Coq file and notify the LSP server."""
        self._text += text
        self._version += 1

        with open(self._tmp_path, "w") as f:
            f.write(self._text)

        from coqpyt.lsp.structs import VersionedTextDocumentIdentifier, TextDocumentContentChangeEvent
        self._client.didChange(
            VersionedTextDocumentIdentifier(self._uri, self._version),
            [TextDocumentContentChangeEvent(None, None, self._text)],
        )

        self._last_line_end = self._estimate_last_line()

    def _last_position(self) -> Position:
        """Estimate the last position in the file."""
        if self._last_line_end:
            return self._last_line_end
        return self._estimate_last_line()

    def _estimate_last_line(self) -> Position:
        """Return a Position at the end of the current text."""
        lines = self._text.split("\n")
        last_line = max(0, len(lines) - 1)
        last_char = len(lines[-1]) if lines else 0
        return Position(last_line, max(0, last_char))

    def _write_temp(self, source: str):
        """Write source to a temporary .v file."""
        fd, path = tempfile.mkstemp(suffix=".v", prefix="coqpyt_")
        os.close(fd)
        self._tmp_path = Path(path)
        self._tmp_path.write_text(source)
        self._uri = f"file://{self._tmp_path}"

    def close(self, timeout: float = 3.0):
        """Clean up resources. Times out shutdown after `timeout` seconds."""
        if self._client:
            import threading

            def _do_close():
                try:
                    self._client.shutdown()
                    self._client.exit()
                except Exception:
                    pass

            t = threading.Thread(target=_do_close, daemon=True)
            t.start()
            t.join(timeout)
            self._client = None
        if self._tmp_path and self._tmp_path.exists():
            try:
                self._tmp_path.unlink()
            except Exception:
                pass
            self._tmp_path = None
