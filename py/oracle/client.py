"""
LLM Oracle Client — sends Coq goals to an LLM API and validates responses.

Supports any OpenAI-compatible API (DeepSeek, OpenAI, local models).
"""

import json
import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional
from urllib.request import Request, urlopen
from urllib.error import URLError


@dataclass
class LLMConfig:
    """Configuration for an LLM API endpoint."""
    api_url: str          # e.g. "https://api.deepseek.com/v1/chat/completions"
    api_key: str          # from environment or config
    model: str            # e.g. "deepseek-chat"
    temperature: float = 0.0
    max_tokens: int = 4096


@dataclass
class OracleResult:
    """Result from an LLM oracle call."""
    success: bool
    proof_script: str
    error_message: str = ""
    attempts: int = 0


def load_config() -> LLMConfig:
    """Load LLM config from environment variables.

    Supports:
      ORACLE_API_URL  — full API endpoint URL
      ORACLE_API_KEY  — authentication key
      ORACLE_MODEL    — model name
      DEEPSEEK_API_KEY — shorthand for DeepSeek
    """
    api_key = os.environ.get("ORACLE_API_KEY") or os.environ.get("DEEPSEEK_API_KEY") or ""
    api_url = os.environ.get("ORACLE_API_URL") or "https://api.deepseek.com/v1/chat/completions"
    model = os.environ.get("ORACLE_MODEL") or "deepseek-chat"

    return LLMConfig(
        api_url=api_url,
        api_key=api_key,
        model=model,
    )


# ── Credit budget ──────────────────────────────────────────────────

_credit_budget: int = 0
_credits_used: int = 0


def reset_credit_budget(budget: int | None = None) -> None:
    """Reset the LLM credit budget for a new session.

    If budget is None, reads ORACLE_CREDIT_BUDGET from env (default 20).
    Set to 0 for unlimited.
    """
    global _credit_budget, _credits_used
    if budget is None:
        budget = int(os.environ.get("ORACLE_CREDIT_BUDGET", "20"))
    _credit_budget = budget
    _credits_used = 0


def credit_budget_exhausted() -> bool:
    """Check if the LLM credit budget is exhausted."""
    return _credit_budget > 0 and _credits_used >= _credit_budget


def credits_used() -> int:
    return _credits_used


def _consume_credit() -> bool:
    """Consume one credit. Returns True if allowed, False if budget exhausted."""
    global _credits_used
    if _credit_budget > 0 and _credits_used >= _credit_budget:
        return False
    _credits_used += 1
    return True


def call_llm(config: LLMConfig, system_prompt: str, user_prompt: str) -> str:
    """Call the LLM API and return the response text.

    Uses OpenAI-compatible chat completions format.
    Returns empty string on failure or if credit budget exhausted.
    """
    if not _consume_credit():
        import sys
        print(f"  [oracle] credit budget exhausted ({_credit_budget} max)", file=sys.stderr)
        return ""
    body = json.dumps({
        "model": config.model,
        "temperature": config.temperature,
        "max_tokens": config.max_tokens,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_prompt},
        ],
    }).encode("utf-8")

    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {config.api_key}",
    }

    try:
        req = Request(config.api_url, data=body, headers=headers, method="POST")
        with urlopen(req, timeout=120) as resp:
            data = json.loads(resp.read().decode("utf-8"))
            return data["choices"][0]["message"]["content"]
    except URLError as e:
        print(f"  [oracle] API error: {e}")
        return ""
    except (KeyError, json.JSONDecodeError) as e:
        print(f"  [oracle] parse error: {e}")
        return ""


def extract_proof(response: str) -> str:
    """Extract a Coq proof script from an LLM response.

    Contracts:
      pre:  len(response) >= 0
      post: returns the proof text (may be empty if no proof found)
    """
    assert len(response) >= 0
    # Try fenced code block first
    match = re.search(r"```(?:coq)?\s*\n(.*?)\n```", response, re.DOTALL)
    if match:
        return match.group(1).strip()

    # Try Proof .. Qed block
    match = re.search(r"Proof\..*?Qed\.", response, re.DOTALL)
    if match:
        return match.group(0).strip()

    return response.strip()


def validate_proof(coq_source: str, coq_paths: list[str]) -> tuple[bool, str]:
    """Validate a Coq proof by compiling with coqc.

    Contracts:
      pre:  len(coq_source) > 0
      post: returns (True, "") if compilation succeeds, (False, error) otherwise
    """
    assert len(coq_source) > 0
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".v", delete=False, prefix="oracle_"
    ) as f:
        f.write(coq_source)
        tmp_path = f.name

    try:
        args = ["coqc"]
        for p in coq_paths:
            args.extend(["-R", p, "Imp"])
        args.append(tmp_path)

        result = subprocess.run(
            args, capture_output=True, text=True, timeout=30,
        )
        if result.returncode == 0:
            return True, ""
        errors = result.stderr + result.stdout
        return False, errors[-2000:]
    except subprocess.TimeoutExpired:
        return False, "coqc timed out"
    finally:
        Path(tmp_path).unlink(missing_ok=True)


def _parse_tactics(proof_text: str) -> list[str]:
    """Split a Coq proof script into individual tactics.

    Handles bullet points (-, +, *), brace groups, and semicolon chains.
    Returns a list of tactic strings ready for try_tactic.

    Contracts:
      pre:  len(proof_text) >= 0
      inv:  depth >= 0
      post: every returned tactic ends with '.', none starts with '(*'
    """
    assert len(proof_text) >= 0
    tactics = []
    current = ""
    depth = 0
    i = 0

    while i < len(proof_text):
        assert depth >= 0
        c = proof_text[i]

        if c == '{':
            depth += 1
            current += c
        elif c == '}':
            depth -= 1
            current += c
        elif c == '.' and depth == 0:
            tactic = (current + '.').strip()
            if tactic != '.' and not tactic.startswith('(*'):
                tactics.append(tactic)
            current = ""
        else:
            current += c

        i += 1

    remainder = current.strip()
    if remainder and remainder != '.':
        tactics.append(remainder + '.')

    return [t for t in tactics if t]


def validate_with_coqpyt(
    coq_preamble: str,
    proof_script: str,
    build_dir: Path,
) -> tuple[bool, str]:
    """Validate a proof script via coqpyt interactive session.

    Contracts:
      pre:  len(coq_preamble) > 0, build_dir exists
      post: (True, "") if all tactics apply and proof closes, (False, error) otherwise
    """
    assert len(coq_preamble) > 0
    import sys as _sys
    from .coqpyt_session import CoqpytSession

    proof_text = proof_script.strip()
    if proof_text.startswith("Proof."):
        proof_text = proof_text[6:].strip()
    if proof_text.endswith("Qed."):
        proof_text = proof_text[:-4].strip()

    tactics = _parse_tactics(proof_text)
    if not tactics:
        return False, "No tactics found in proof script"

    try:
        with CoqpytSession(build_dir, timeout=60) as session:
            ok = session.load(coq_preamble)
            if not ok:
                return False, "Failed to load Coq source into coqpyt session"

            for i, tactic in enumerate(tactics):
                state = session.try_tactic(tactic)
                if state.error:
                    return False, f"Tactic #{i+1} '{tactic[:60]}' failed: {state.error[:300]}"

            if session.is_proved():
                session.finish_proof("Qed.")
                return True, ""

            remaining = session.get_goals()
            if remaining.is_proved():
                return True, ""

            goal_text = (
                "\n".join(remaining.goals[:3])
                if remaining.goals
                else "no remaining goals"
            )
            return False, f"Proof incomplete ({len(tactics)} tactics). Remaining: {goal_text[:500]}"
    except Exception as e:
        return False, f"coqpyt validation error: {str(e)[:500]}"


def oracle_query(
    goal: str,
    context: str,
    dependencies: list[str],
    coq_paths: list[str] | None = None,
    examples: list[str] | None = None,
    max_retries: int = 3,
    hint: str = "",
    build_dir: "Path | None" = None,
) -> OracleResult:
    """Query the LLM oracle for a Coq proof.

    Args:
        goal: The Coq goal statement (theorem, hypotheses)
        context: Additional Coq context (definitions, lemmas) — must be valid Coq
        dependencies: Lemma names that hammer identified as useful
        coq_paths: List of paths to pass to coqc via -R (fallback validation)
        examples: Example proofs for few-shot prompting
        max_retries: Maximum number of LLM attempts
        hint: Extra guidance text for the LLM (not included in validation source)
        build_dir: Path to Coq build directory for coqpyt validation (preferred).

    Returns:
        OracleResult with the proof script (if successful) and error info.
    """
    config = load_config()

    if not config.api_key:
        return OracleResult(
            success=False,
            proof_script="",
            error_message="No API key set. Set DEEPSEEK_API_KEY or ORACLE_API_KEY.",
        )

    paths = coq_paths or []
    use_coqpyt = build_dir is not None

    system_prompt = prompt_system()
    user_prompt = prompt_user(goal, context, dependencies, examples, hint)

    for attempt in range(1, max_retries + 1):
        if credit_budget_exhausted():
            print(f"  [oracle] credit budget exhausted ({_credit_budget} max)", file=__import__('sys').stderr)
            return OracleResult(
                success=False, proof_script="",
                error_message="Credit budget exhausted.",
                attempts=attempt-1,
            )
        print(f"  [oracle] attempt {attempt}/{max_retries}...", end=" ", flush=True)

        response = call_llm(config, system_prompt, user_prompt)
        if not response:
            print("no response")
            continue

        proof = extract_proof(response)
        if not proof:
            print(f"no proof extracted from: {response[:100]}", file=__import__('sys').stderr)
            continue

        print(f"  [oracle] LLM proof: {proof[:150]}...", file=__import__('sys').stderr)

        if use_coqpyt:
            coq_preamble = f"""Require Import ZArith String List Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

{context}
{goal}
Proof.
"""
            ok, error = validate_with_coqpyt(coq_preamble, proof, build_dir)
        else:
            full_source = f"""Require Import ZArith String List Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

{context}

{goal}
{proof}"""
            ok, error = validate_proof(full_source, paths)

        if ok:
            print("valid" if use_coqpyt else "valid (coqc)")
            return OracleResult(success=True, proof_script=proof, attempts=attempt)

        print(f"invalid ({'coqpyt' if use_coqpyt else 'coqc'}), retrying")
        user_prompt += f"\n\n[Previous attempt failed with: {error[:500]}]\nPlease fix the proof."

    return OracleResult(
        success=False,
        proof_script="",
        error_message="All LLM attempts produced invalid proofs.",
        attempts=max_retries,
    )


def interactive_oracle_query(
    goal: str,
    context: str,
    build_dir: Path,
    hint: str = "",
    max_steps: int = 20,
    max_retries_per_step: int = 2,
) -> OracleResult:
    """Step-by-step interactive proof via coqpyt.

    The LLM sees the current goal state and hypotheses at each step,
    proposes a single tactic, and sees the result before proposing the next.

    Args:
        goal: The Coq goal statement (theorem)
        context: Additional Coq context (definitions, lemmas)
        build_dir: Path to Coq build directory
        hint: Extra guidance text
        max_steps: Maximum number of proof steps
        max_retries_per_step: Retries per step if tactic fails

    Returns:
        OracleResult with the proof script and status.
    """
    config = load_config()
    if not config.api_key:
        return OracleResult(
            success=False, proof_script="",
            error_message="No API key set.",
        )

    coq_preamble = f"""Require Import ZArith String List Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

{context}
{goal}
Proof.
"""
    system_prompt = """You are an interactive Coq proof assistant. You receive the
current goal state (hypotheses and goal). Propose exactly ONE Coq tactic.
Output ONLY the tactic, nothing else. You may add a (* comment *) AFTER
the tactic on the same line, but the tactic must come first and be valid Coq.
Never output markdown fences or explanatory text before the tactic.
Available: wp_prove, wp_reduce, lia, split, intro, intros, apply, reflexivity,
destruct, eexists, rewrite, eapply, match goal, Z.leb_le, Z.leb_gt."""

    from .coqpyt_session import CoqpytSession
    try:
        with CoqpytSession(build_dir, timeout=120) as session:
            if not session.load(coq_preamble):
                return OracleResult(
                    success=False, proof_script="",
                    error_message="Failed to load Coq source into coqpyt session.",
                )

            tactics_used: list[str] = []
            step_history: list[str] = []
            user_prompt = "Prove the goal step by step. Start with 'wp_prove.'"

            for step in range(1, max_steps + 1):
                if credit_budget_exhausted():
                    return OracleResult(
                        success=False, proof_script="\n".join(tactics_used),
                        error_message=f"Credit budget exhausted after {step-1} steps.",
                        attempts=step-1,
                    )

                goals_state = session.get_goals()
                if goals_state.is_proved():
                    session.finish_proof("Qed.")
                    proof_script = "Proof.\n" + "\n".join(tactics_used) + "\nQed."
                    print(f"  [oracle] interactive: proved in {step} steps", file=__import__('sys').stderr)
                    return OracleResult(
                        success=True, proof_script=proof_script,
                        attempts=1,
                    )

                goal_text = "\n".join(goals_state.goals[:3]) if goals_state.goals else "no goals"
                step_prompt = (
                    f"## Current Goals\n```coq\n{goal_text}\n```\n\n"
                    f"## Previous Steps\n" + "\n".join(step_history[-6:]) + "\n\n"
                    f"Propose exactly ONE tactic for the current goal."
                )

                for retry in range(max_retries_per_step + 1):
                    if retry > 0:
                        step_prompt += f"\n\n[Previous tactic failed]\nTry a different approach."

                    response = call_llm(config, system_prompt, step_prompt)
                    if not response:
                        continue

                    tactic = _extract_tactic(response)
                    if not tactic:
                        # Fallback: take first non-empty line ending with .
                        for line in response.strip().split("\n"):
                            line = line.strip()
                            if line.endswith(".") and not line.startswith("(*"):
                                tactic = line.rstrip(".")
                                break
                    if not tactic:
                        continue

                    print(f"  [oracle] step {step}: {tactic}", file=__import__('sys').stderr)
                    result = session.try_tactic(tactic)
                    if not result.error:
                        tactics_used.append(tactic + ".")
                        step_history.append(f"Step {step}: {tactic}. ✓")
                        break
                    else:
                        step_prompt += f"\n\n[Tactic '{tactic}' failed: {result.error[:200]}]"
                        if retry == max_retries_per_step:
                            return OracleResult(
                                success=False,
                                proof_script="\n".join(tactics_used),
                                error_message=f"Step {step}: tactic '{tactic}' failed after {max_retries_per_step} retries: {result.error[:200]}",
                                attempts=step,
                            )

            return OracleResult(
                success=False,
                proof_script="\n".join(tactics_used),
                error_message=f"Max steps ({max_steps}) reached without closing proof.",
                attempts=max_steps,
            )

    except Exception as e:
        return OracleResult(
            success=False, proof_script="",
            error_message=f"Interactive oracle error: {str(e)[:500]}",
        )


def _extract_tactic(response: str) -> str | None:
    """Extract a single Coq tactic from an LLM response.

    Slurps content from inside markdown code fences, strips (* comments *),
    and returns the first line that looks like a tactic.
    """
    text = response.strip()
    # Slurp content between markdown fences: find opening ```, take everything
    # after it up to and excluding the closing ```
    fence_start = -1
    for fence in ["```coq", "```ocaml", "```"]:
        idx = text.find(fence)
        if idx >= 0:
            fence_start = idx + len(fence)
            break
    if fence_start >= 0:
        text = text[fence_start:]
        # Strip trailing fence
        for fence in ["```"]:
            idx = text.rfind(fence)
            if idx >= 0:
                text = text[:idx]
                break
    # Remove (* ... *) comments
    import re
    text = re.sub(r'\(\*.*?\*\)', '', text, flags=re.DOTALL).strip()
    # Take the first non-empty line that looks like a tactic
    for line in text.split("\n"):
        line = line.strip()
        if not line:
            continue
        if line.startswith("#") or line.startswith("//"):
            continue
        if any(line.lower().startswith(w) for w in
               ["the ", "now ", "first", "next", "this ", "we ", "i ", "let's", "lets"]):
            continue
        if line.endswith(".") or line in ("-", "+", "*", "--", "++", "**", "{", "}"):
            return line.rstrip(".")
    return None


def prompt_system() -> str:
    return """You are a Coq proof assistant. Output ONLY the proof (Proof. ... Qed.).
Use 'wp_prove.' as the FIRST tactic — it handles all WP/state simplification.
After wp_prove, the goal is a simple Z arithmetic statement or conjunction.
Then use: lia, split, intro, reflexivity, apply, intros.
Keep proofs short. Most are 1-3 lines after wp_prove.

Patterns:
- Simple assignment: Proof. intros. wp_prove. Qed.
- Conditional (single BLe): Proof. intros. wp_reduce. split; [ intro H; apply Z.leb_le in H | intro H; apply Z.leb_gt in H ]; wp_prove; split; lia. Qed.
- Conditional with BOr: Proof. intros. wp_reduce. split; intro H.
  - apply Bool.orb_true_iff in H. destruct H as [Hc|Hc]; apply Z.leb_le in Hc; wp_prove; split; lia.
  - apply Bool.orb_false_iff in H. destruct H as [Hc1 Hc2]; apply Z.leb_gt in Hc1; apply Z.leb_gt in Hc2; wp_prove; split; lia. Qed.
- Function call (CCall): After wp_reduce, you'll see a goal like (forall r : Z, ...). Use:
    match goal with [H: forall r:Z, ?P -> ?Q |- ?Q] => eapply H; [solve [auto] | reflexivity] end.
- VCG: Proof. intros Hinv Hexit. apply Z.leb_gt in Hexit. lia. Qed.

Available tactics: wp_prove, wp_reduce, lia, split, intro, intros, apply, reflexivity, destruct, eapply, match.
Key lemmas: Z.leb_le, Z.leb_gt, Bool.orb_true_iff, Bool.orb_false_iff."""


def prompt_user(
    goal: str,
    context: str,
    dependencies: list[str],
    examples: list[str] | None = None,
    hint: str = "",
) -> str:
    """User prompt with the goal, context, and known dependencies."""
    parts = ["Generate a Coq proof for the following goal:\n"]

    if context:
        parts.append(f"## Context\n```coq\n{context}\n```\n")

    parts.append(f"## Goal\n```coq\n{goal}\n```\n")

    if hint:
        parts.append(f"## Hints\n{hint}\n")

    if dependencies:
        deps = "\n".join(f"- {d}" for d in dependencies)
        parts.append(f"## Recommended lemmas (from SMT hammer)\n{deps}\n")

    if examples:
        parts.append("## Example proofs\n")
        for ex in examples:
            parts.append(f"```coq\n{ex}\n```\n")

    parts.append("## Your proof\n")
    return "\n".join(parts)
