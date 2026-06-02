"""
Structured proof pipeline logging and MCP integration.

Provides per-goal status tracking, human-readable reports, and
structured output designed for MCP tool consumption.

MCP Tool: axiomander

  Accepts Python source with assert contracts.
  Returns per-goal verification status + actionable guidance.
"""

import time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Optional


class ProofLevel(Enum):
    """Which tier closed the goal."""
    LEVEL1_LTAC = "level1"       # wp_reduce, lia
    LEVEL2_SMT = "level2"        # coq-hammer → cvc4/eprover
    LEVEL3_LLM = "level3"        # LLM oracle
    UNPROVED = "unproved"        # still open
    COUNTEREXAMPLE = "counterexample"  # SMT found a model showing the property is false


class Action(Enum):
    """Recommended next action for an unproved goal."""
    ADD_INVARIANT = "add_loop_invariant"
    ADD_PRECONDITION = "strengthen_precondition"
    ADD_POSTCONDITION = "weaken_postcondition"
    REFACTOR = "refactor_body"
    ADD_LEMMA = "add_helper_lemma"
    SPLIT_CASES = "split_into_cases"
    RETRY_LLM = "retry_llm"
    PROPERTY_FALSE = "property_may_be_false"
    OK = "no_action_needed"


@dataclass
class GoalStatus:
    name: str
    goal_statement: str
    level: ProofLevel = ProofLevel.UNPROVED
    elapsed_ms: float = 0.0
    dependencies: list[str] = field(default_factory=list)
    counterexample: dict[str, int] = field(default_factory=dict)
    proof_method: str = ""
    error_detail: str = ""
    suggested_action: "Action | None" = None
    suggestion_text: str = ""
    purity_note: str = ""

    def is_proved(self) -> bool:
        """
        axiomander:
            ensures:
                implies(result, error_detail == "")
                implies(result, proof_method != "" or level == ProofLevel.LEVEL1_LTAC)
                implies(not result, suggested_action is not None)
                implies(level == ProofLevel.COUNTEREXAMPLE, not result)
        """
        return self.level not in (ProofLevel.UNPROVED, ProofLevel.COUNTEREXAMPLE)


@dataclass
class PipelineReport:
    """Full pipeline report for a Python file."""
    source_file: str
    total_goals: int
    proved_goals: int
    goals: list[GoalStatus]
    elapsed_total_ms: float = 0.0

    def summary(self) -> str:
        """One-line summary."""
        pct = 100 * self.proved_goals // max(self.total_goals, 1)
        return f"{self.proved_goals}/{self.total_goals} proved ({pct}%) — {self.source_file}"

    def mcp_output(self) -> str:
        """Structured output for MCP tool consumption."""
        lines = [
            f"# Verification Report: {self.source_file}",
            f"**{self.summary()}**",
            f"",
            f"| Function | Status | Level | Method | Time | Guidance |",
            f"|----------|--------|-------|------|----------|",
        ]
        for g in self.goals:
            status = "✓" if g.is_proved() else "✗"
            level = g.level.value if g.is_proved() else "—"
            time_str = f"{g.elapsed_ms:.0f}ms" if g.elapsed_ms else "—"
            action = g.suggested_action.value if g.suggested_action != Action.OK else "—"
            lines.append(
                f"| `{g.name}` | {status} | {level} | {g.proof_method or "—"} | {time_str} | {action} |"
            )

        lines.append("")
        lines.append("## Unproved Goals")
        unproved = [g for g in self.goals if not g.is_proved()]
        if not unproved:
            lines.append("All goals proved. ✓")
        else:
            for g in unproved:
                lines.append(f"### `{g.name}`")
                lines.append(f"**Action**: {g.suggested_action.value if g.suggested_action else "unknown"}")
                lines.append(f"**Detail**: {g.suggestion_text}")
                if g.counterexample:
                    lines.append(f"**SMT counterexample**: {", ".join(f"`{k}={v}`" for k, v in g.counterexample.items())}")
                    lines.append(f"> The loop invariant is too weak. Strengthen it to rule out these values.")
                if g.error_detail:
                    lines.append(f"```\n{g.error_detail[:500]}\n```")
                if g.dependencies:
                    lines.append(f"**Hammer suggested lemmas**: {', '.join(g.dependencies)}")
                lines.append("")

        return "\n".join(lines)


def classify_failure(goal_name: str, error: str, has_loop: bool) -> Action:
    """Heuristically classify why a proof failed and suggest action.

    Args:
        goal_name: Function name
        error: Error message from coqc or hammer
        has_loop: Whether the function body contains a loop

    Returns:
        Suggested action for the user/agent.

    axiomander:
        requires:
            len(goal_name) > 0
        ensures:
            implies(has_loop and "invariant" in error.lower(), result == Action.ADD_INVARIANT)
            implies("counterexample" in error.lower() or "sat" in error.lower(), result == Action.PROPERTY_FALSE)
            implies("unable to unify" in error.lower() or "type error" in error.lower(), result == Action.REFACTOR)
            implies("not found" in error.lower() or "unknown" in error.lower(), result == Action.ADD_LEMMA)
    """
    error_lower = error.lower()

    if has_loop and ("inv" in error_lower or "invariant" in error_lower):
        result = Action.ADD_INVARIANT
    elif "counterexample" in error_lower or "sat" in error_lower:
        result = Action.PROPERTY_FALSE
    elif "could not prove" in error_lower or "admitted" in error_lower:
        if has_loop:
            result = Action.ADD_INVARIANT
        else:
            result = Action.RETRY_LLM
    elif "unable to unify" in error_lower or "type error" in error_lower:
        result = Action.REFACTOR
    elif "not found" in error_lower or "unknown" in error_lower:
        result = Action.ADD_LEMMA
    else:
        result = Action.RETRY_LLM
    return result


def action_guidance(action: Action, goal_name: str) -> str:
    """Human-readable guidance for an action."""
    guidance = {
        Action.ADD_INVARIANT: (
            f"The loop in `{goal_name}` needs an invariant. "
            f"Add `@invariant(lambda ...)` describing what the loop preserves. "
            f"Common pattern: `@invariant(lambda i, acc: acc == f(i))`"
        ),
        Action.ADD_PRECONDITION: (
            f"The precondition of `{goal_name}` is too weak. "
            f"Add constraints to `@requires(...)` that capture assumptions "
            f"about input values."
        ),
        Action.ADD_POSTCONDITION: (
            f"The postcondition of `{goal_name}` may be too strong. "
            f"Check if the property actually holds for all inputs. "
            f"If not, weaken `@ensures(...)` or add missing preconditions."
        ),
        Action.REFACTOR: (
            f"The body of `{goal_name}` couldn't be translated to IMP. "
            f"Simplify the function — extract complex expressions, "
            f"avoid side effects, flatten nested structures."
        ),
        Action.ADD_LEMMA: (
            f"The prover needs additional lemmas for `{goal_name}`. "
            f"Write a helper lemma about the data structure or arithmetic, "
            f"prove it separately, then use it in the main proof."
        ),
        Action.SPLIT_CASES: (
            f"Break `{goal_name}` into separate cases. "
            f"Use `destruct`/`induction` in the Coq proof, or write "
            f"separate theorems for each case."
        ),
        Action.RETRY_LLM: (
            f"The LLM oracle couldn't prove `{goal_name}`. "
            f"The LLM will retry with the error feedback. "
            f"If it keeps failing, try providing a helper lemma or invariant."
        ),
        Action.PROPERTY_FALSE: (
            f"The property for `{goal_name}` may be FALSE. "
            f"SMT found a counterexample. Check the contract — "
            f"either the code is buggy or the specification is wrong."
        ),
        Action.OK: "No action needed.",
    }
    return guidance.get(action, "Unknown action.")


def build_report(
    source_file: str,
    goals: list[GoalStatus],
    elapsed_total_ms: float = 0.0,
) -> PipelineReport:
    """Build a pipeline report from goal statuses.

    axiomander:
        requires:
            len(source_file) > 0
            len(goals) >= 0
        ensures:
            result.total_goals == len(goals)
            result.proved_goals == sum(1 for g in goals if g.is_proved())
            result.proved_goals <= result.total_goals
            implies(len(goals) == 0, result.proved_goals == 0)
    """
    proved = sum(1 for g in goals if g.is_proved())
    return PipelineReport(
        source_file=source_file,
        total_goals=len(goals),
        proved_goals=proved,
        goals=goals,
        elapsed_total_ms=elapsed_total_ms,
    )


# ─── MCP Tool interface ───────────────────────────────────────────

MCP_TOOL_DEFINITION = {
    "name": "axiomander",
    "description": (
        "Verify Python code annotated with @requires/@ensures/@invariant "
        "contracts against the Coq WP proof pipeline. "
        "Returns per-goal status with actionable guidance when proofs fail."
    ),
    "parameters": {
        "type": "object",
        "properties": {
            "source": {
                "type": "string",
                "description": "Python source code with contract decorators",
            },
            "function_name": {
                "type": "string",
                "description": "Optional: verify only this function",
            },
            "max_llm_retries": {
                "type": "integer",
                "default": 3,
                "description": "Max LLM retry attempts for Level 3 goals",
            },
            "timeout_seconds": {
                "type": "integer",
                "default": 60,
                "description": "Max total pipeline time",
            },
        },
        "required": ["source"],
    },
}


# ─── Integration guide for opencode sessions ──────────────────────

MCP_INTEGRATION_GUIDE = """
## Using axiomander in an opencode session

### Step 1: Annotate
Add contracts to your Python code:

    from py.contracts import requires, ensures

    @requires(lambda n: n >= 0)
    @ensures(lambda n, result: result == n * (n + 1) // 2)
    def sum_to(n: int) -> int:
        acc = 0
        for i in range(n + 1):
            acc += i
        return acc

### Step 2: Verify
Run the MCP tool:

    axiomander(source=...)
    ...
After making changes, run `axiomander` again.
Repeat until all goals are proved or you accept the remaining
goals as trusted (Admitted).
"""


if __name__ == "__main__":
    # Demo: build a report for the test file
    goals = [
        GoalStatus(
            name="add",
            goal_statement="...",
            level=ProofLevel.LEVEL1_LTAC,
            elapsed_ms=15,
        ),
        GoalStatus(
            name="sum_to",
            goal_statement="...",
            level=ProofLevel.UNPROVED,
            error_detail="Could not prove loop invariant.",
            suggested_action=Action.ADD_INVARIANT,
            suggestion_text=action_guidance(Action.ADD_INVARIANT, "sum_to"),
        ),
    ]
    report = build_report("demo.py", goals, 45)
    print(report.mcp_output())
