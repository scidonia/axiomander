"""Interactive Coq session — fixed prompt detection."""
import os, re, subprocess, sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

@dataclass 
class ProofState:
    goals: list[str] = field(default_factory=list)
    is_complete: bool = False  
    error: str = ""

PROMPT_RE = re.compile(r'^(\S+)\s*<\s*$')

class CoqSession:
    def __init__(self, build_dir: Path):
        self.build_dir = build_dir
        self.proc = None

    def __enter__(self):
        self.proc = subprocess.Popen(
            ["coqtop", "-R", str(self.build_dir), "Imp"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True,
        )
        self._read()  # welcome banner
        return self

    def __exit__(self, *args):
        if self.proc:
            try: self.send("Quit.")
            except: pass
            self.proc.terminate()
            self.proc.wait(timeout=1)

    def send(self, command: str) -> ProofState:
        cmd = command.strip()
        if cmd and not cmd.endswith('.') and not cmd.endswith('}'):
            cmd += '.'
        self.proc.stdin.write(cmd + "\n")
        self.proc.stdin.flush()
        return self._read()

    def _read(self) -> ProofState:
        """Read lines until we see a Coq prompt. Return parsed state."""
        lines = []
        while True:
            line = self.proc.stdout.readline()
            if not line:
                break
            line = line.rstrip('\n')
            if PROMPT_RE.match(line):
                break
            if line.startswith('[Loading'):
                continue
            lines.append(line)
        
        return self._parse('\n'.join(lines))

    def _parse(self, output: str) -> ProofState:
        state = ProofState()
        
        if not output.strip():
            state.is_complete = True
            return state
        
        # Check for "No more goals" or "No more subgoals"
        if 'no more subgoals' in output.lower() or 'no more goals' in output.lower():
            state.is_complete = True
            return state
        
        # Check for errors
        for line in output.split('\n'):
            if line.startswith('Error:') or line.startswith('Tactic failure:'):
                state.error = '\n'.join(output.split('\n')[-3:])[:500]
                return state
        
        # Extract goal text (everything between the header and next blank/boundary)
        goal_match = re.search(r'(?:sub)?goal\s+\d+(?:\s+is:)?\s*\n(.*?))(?=\n\s*\n|\Z)', output, re.DOTALL | re.IGNORECASE)
        if goal_match:
            state.goals = [goal_match.group(1).strip()[:1000]]
        elif output.strip():
            state.goals = [output.strip()[:1000]]
        
        return state

    def load_theory(self) -> bool:
        for cmd in [
            'Require Import ZArith String List Lia.',
            'Require Import Imp Wp WpTactics.',
            'Import ListNotations.',
            'Open Scope Z_scope.',
        ]:
            state = self.send(cmd)
            if state.error:
                print(f"  [coq] load error: {state.error}", file=sys.stderr)
                return False
        return True


def prove_interactive(goal: str, bd: Path, max_steps: int = 5) -> tuple[bool, list[str], str]:
    """Prove a goal interactively. Returns (success, tactics, error).
    
    Starts with wp_prove, then tries lia, then split/intro patterns.
    This is the heuristic engine — wire up an LLM to drive this
    with actual goal state feedback.
    """
    steps = []
    error = ""
    with CoqSession(bd) as coq:
        if not coq.load_theory():
            return False, steps, "theory load failed"
        
        state = coq.send("Goal " + goal.strip().rstrip('.'))
        if state.error:
            return False, steps, state.error
        
        state = coq.send("Proof.")
        steps.append("Proof.")
        
        # Heuristic 1: wp_prove
        state = coq.send("wp_prove.")
        steps.append("wp_prove.")
        if state.is_complete:
            coq.send("Qed.")
            return True, steps, ""
        if state.error:
            error = state.error
        
        # Heuristic 2: lia
        state = coq.send("lia.")
        steps.append("lia.")
        if state.is_complete:
            coq.send("Qed.")
            return True, steps, ""
        
        # Heuristic 3: split + intro + apply + wp_prove
        if state.goals and "Z.leb" in str(state.goals):
            state = coq.send("split.")
            steps.append("split.")
            state = coq.send("intro H.")
            steps.append("intro H.")
            state = coq.send("apply Z.leb_le in H.")
            steps.append("apply Z.leb_le in H.")
            state = coq.send("wp_prove.")
            steps.append("wp_prove.")
            if state.is_complete:
                coq.send("Qed.")
                steps.append("Qed.")
                return True, steps, ""
        
        return False, steps, error or "could not close"


def test():
    bd = Path("/home/gavin/dev/Scidonia/axiomander/_build/default/coq")
    
    # Test basic
    ok, steps, err = prove_interactive("forall a b, a + b = b + a.", bd)
    print(f"Basic: {ok} steps={steps} err={err[:80]}")
    assert ok
    
    # Test IMP goal
    ok, steps, err = prove_interactive(
        "forall a b, True -> wp (CAss \"r\"%string (APlus (AVar \"a\"%string) (AVar \"b\"%string))) (fun s => s \"r\"%string = a + b) (upd (upd empty_state \"a\"%string a) \"b\"%string b).",
        bd)
    print(f"IMP add: {ok} steps={steps}")
    if not ok: print(f"  err={err[:200]}")
    
    print("DONE")


if __name__ == "__main__":
    test()
