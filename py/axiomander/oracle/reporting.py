"""
Structured proof pipeline logging and MCP integration.

Provides per-goal status tracking, human-readable reports, and
structured output designed for MCP tool consumption.

MCP Tool: axiomander

  Accepts Python source with assert contracts.
  Returns per-goal verification status + actionable guidance.
"""

import json
import time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Optional


class ProofLevel(Enum):
    """Which tier closed the goal."""
    LEVEL1_LTAC        = "level1"       # wp_reduce, lia
    LEVEL2_SMT         = "level2"       # coq-hammer → cvc4/eprover
    LEVEL2B_SMT_THEORY = "level2b"      # theory-SMT oracle (strings, floats)
    LEVEL3_LLM         = "level3"       # LLM oracle
    UNPROVED           = "unproved"     # still open
    COUNTEREXAMPLE     = "counterexample"  # SMT found a model showing the property is false


class GoalOutcome(str, Enum):
    """Dafny-flavored outcome for a verification goal.

    Maps onto ProofLevel as follows:
      LEVEL1/LEVEL2/LEVEL2B/LEVEL3 -> verified
      COUNTEREXAMPLE               -> counterexample
      UNPROVED (internal error)    -> error
      UNPROVED (normal)            -> unproved
    """
    VERIFIED         = "verified"
    COUNTEREXAMPLE   = "counterexample"
    TIMEOUT          = "timeout"
    OUT_OF_RESOURCES = "out_of_resources"
    ERROR            = "error"
    UNPROVED         = "unproved"


def _outcome_for(goal: "GoalStatus") -> GoalOutcome:
    """Derive the GoalOutcome from a GoalStatus."""
    if goal.level == ProofLevel.COUNTEREXAMPLE:
        return GoalOutcome.COUNTEREXAMPLE
    if goal.is_proved():
        return GoalOutcome.VERIFIED
    # Distinguish internal errors (error_detail present but no counterexample)
    # from normal unproved goals.
    if goal.error_detail and not goal.counterexample and not goal.theory_counterexample:
        return GoalOutcome.ERROR
    return GoalOutcome.UNPROVED


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
    # Typed counterexample from the theory-SMT oracle (strings, floats).
    # Populated when level == COUNTEREXAMPLE and the violation came from
    # a theory solver rather than the integer SMT path.
    theory_counterexample: "str" = ""  # formatted report from TheoryCounterexample
    proof_method: str = ""
    error_detail: str = ""
    suggested_action: "Action | None" = None
    suggestion_text: str = ""
    purity_note: str = ""

    def is_proved(self) -> bool:
        """
        axiomander:
            ensures:
                implies(self.level == ProofLevel.UNPROVED, result == False)
                implies(self.level == ProofLevel.COUNTEREXAMPLE, result == False)
                implies(self.level != ProofLevel.UNPROVED
                        and self.level != ProofLevel.COUNTEREXAMPLE,
                        result == True)
        """
        return self.level not in (ProofLevel.UNPROVED, ProofLevel.COUNTEREXAMPLE)

    def to_dict(self) -> dict:
        """Serialize to the canonical Dafny-flavored JSON schema dict.

        Schema keys (stable contract):
          name, outcome, level, elapsed_ms, resource_count,
          proof_method, counterexample, theory_counterexample,
          error_detail, suggested_action, suggestion_text,
          dependencies, obligations
        """
        return {
            "name": self.name,
            "outcome": _outcome_for(self).value,
            "level": self.level.value if self.is_proved() else None,
            "elapsed_ms": self.elapsed_ms,
            "resource_count": None,
            "proof_method": self.proof_method or None,
            "counterexample": self.counterexample,
            "theory_counterexample": self.theory_counterexample or None,
            "error_detail": self.error_detail or None,
            "suggested_action": self.suggested_action.value if self.suggested_action else None,
            "suggestion_text": self.suggestion_text or None,
            "dependencies": self.dependencies,
            "obligations": [],
        }


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

    def to_dict(self) -> dict:
        """Serialize to the canonical Dafny-flavored JSON schema dict."""
        verified = sum(1 for g in self.goals if g.is_proved())
        total = self.total_goals
        pct = 100 * verified // max(total, 1)
        return {
            "source_file": self.source_file,
            "summary": {
                "verified": verified,
                "total": total,
                "percent": pct,
            },
            "elapsed_total_ms": self.elapsed_total_ms,
            "goals": [g.to_dict() for g in self.goals],
        }

    def to_json(self, indent: int = 2) -> str:
        """Serialize to a JSON string using the canonical schema."""
        return json.dumps(self.to_dict(), indent=indent)

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
            status = "+" if g.is_proved() else "x"
            level = g.level.value if g.is_proved() else "-"
            time_str = f"{g.elapsed_ms:.0f}ms" if g.elapsed_ms else "-"
            action_str = g.suggested_action.value if g.suggested_action and g.suggested_action != Action.OK else "-"
            lines.append(
                f"| `{g.name}` | {status} | {level} | {g.proof_method or '-'} | {time_str} | {action_str} |"
            )

        lines.append("")
        lines.append("## Unproved Goals")
        unproved = [g for g in self.goals if not g.is_proved()]
        if not unproved:
            lines.append("All goals proved.")
        else:
            for g in unproved:
                lines.append(f"### `{g.name}`")
                action_label = g.suggested_action.value if g.suggested_action else "unknown"
                lines.append(f"**Action**: {action_label}")
                lines.append(f"**Detail**: {g.suggestion_text}")
                if g.theory_counterexample:
                    lines.append("**Theory counterexample**:")
                    lines.append(f"```\n{g.theory_counterexample}\n```")
                elif g.counterexample:
                    lines.append(f"**SMT counterexample**: {', '.join(f'`{k}={v}`' for k, v in g.counterexample.items())}")
                    lines.append("> The loop invariant is too weak. Strengthen it to rule out these values.")
                if g.error_detail:
                    lines.append(f"```\n{g.error_detail[:500]}\n```")
                if g.dependencies:
                    lines.append(f"**Hammer suggested lemmas**: {', '.join(g.dependencies)}")
                lines.append("")

        return "\n".join(lines)


def classify_failure(goal_name: str, error: str, has_loop: bool) -> Action:
    """Heuristically classify why a proof failed and suggest action.

    The branches are prioritised top-to-bottom, so the counterexample
    branch only fires when the invariant branch did not.

    axiomander:
        requires:
            len(goal_name) > 0
        ensures:
            implies(has_loop and "invariant" in error.lower(),
                    result == Action.ADD_INVARIANT)
            implies("counterexample" in error.lower()
                    and not (has_loop and "invariant" in error.lower()),
                    result == Action.PROPERTY_FALSE)
            implies("type error" in error.lower()
                    and "counterexample" not in error.lower()
                    and not (has_loop and "invariant" in error.lower()),
                    result == Action.REFACTOR)
    """
    error_lower = error.lower()

    if has_loop and ("inv" in error_lower or "invariant" in error_lower):
        result = Action.ADD_INVARIANT
    elif "backing definition" in error_lower or "not yet implemented" in error_lower:
        result = Action.REFACTOR
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


# ── Verified scalar specifications ───────────────────────────────────────
# These functions extract the pure decision logic into the IMP-verifiable
# fragment.  They serve as machine-checked specifications of the core
# branching behaviour — proven at Level 1 (wp_reduce + lia).

def _spec_is_proved(level: int) -> int:
    """Scalar specification of GoalStatus.is_proved().

    Encoding: UNPROVED=0, COUNTEREXAMPLE=1, LEVEL1..LEVEL3=2..4.
    A goal is proved iff its level is not UNPROVED (0) or COUNTEREXAMPLE (1).

    axiomander:
        requires:
            level >= 0
            level <= 4
        ensures:
            implies(level == 0, result == 0)
            implies(level == 1, result == 0)
            implies(level >= 2, result == 1)
            result == 0 or result == 1
    """
    if level == 0 or level == 1:
        result = 0
    else:
        result = 1
    return result


def _spec_classify_failure(
    has_loop: int,
    has_invariant_kw: int,
    has_counterexample_kw: int,
    has_type_error_kw: int,
    has_not_found_kw: int,
) -> int:
    """Scalar specification of the classify_failure branching logic.

    Keyword flags are 1 if the pattern appears in the error, 0 otherwise.
    Return values: ADD_INVARIANT=0, PROPERTY_FALSE=1, REFACTOR=3,
                   ADD_LEMMA=4, RETRY_LLM=5.

    axiomander:
        requires:
            has_loop >= 0
            has_invariant_kw >= 0
            has_counterexample_kw >= 0
            has_type_error_kw >= 0
            has_not_found_kw >= 0
        ensures:
            implies(has_loop >= 1 and has_invariant_kw >= 1, result == 0)
            implies(has_counterexample_kw >= 1
                    and not (has_loop >= 1 and has_invariant_kw >= 1),
                    result == 1)
    """
    if has_loop >= 1 and has_invariant_kw >= 1:
        result = 0
    elif has_counterexample_kw >= 1:
        result = 1
    elif has_type_error_kw >= 1:
        result = 3
    elif has_not_found_kw >= 1:
        result = 4
    else:
        result = 5
    return result


def _spec_outcome_for(
    level: int,
    is_proved_result: int,
    error_detail: int,
    counterexample: int,
    theory_counterexample: int,
) -> int:
    """Scalar specification of _outcome_for().

    Encoding:
      level: 0=LEVEL1..3=LEVEL3, 4=UNPROVED, 5=COUNTEREXAMPLE
      is_proved_result: 0=not proved, 1=proved
      error_detail, counterexample, theory_counterexample: 0=absent, 1=present
      result: 0=COUNTEREXAMPLE, 1=VERIFIED, 2=ERROR, 3=UNPROVED

    axiomander:
        requires:
            level >= 0
            level <= 5
            is_proved_result >= 0
            is_proved_result <= 1
            error_detail >= 0
            error_detail <= 1
            counterexample >= 0
            counterexample <= 1
            theory_counterexample >= 0
            theory_counterexample <= 1
        ensures:
            implies(level == 5, result == 0)
            implies(level != 5 and is_proved_result == 1, result == 1)
            implies(level != 5 and is_proved_result == 0
                    and error_detail == 1
                    and counterexample == 0
                    and theory_counterexample == 0,
                    result == 2)
            implies(level != 5 and is_proved_result == 0
                    and not (error_detail == 1
                             and counterexample == 0
                             and theory_counterexample == 0),
                    result == 3)
    """
    if level == 5:
        result = 0
    elif is_proved_result == 1:
        result = 1
    elif error_detail == 1 and counterexample == 0 and theory_counterexample == 0:
        result = 2
    else:
        result = 3
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
            f"The function `{goal_name}` could not be verified. "
            f"Check the error detail above for the specific issue — "
            f"usually this means the function's contracts or body "
            f"need adjustment (missing precondition, undefined external "
            f"reference, or unsupported language feature)."
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


def _spec_build_report(total_goals: int, proved_goals: int) -> int:
    """Scalar specification of build_report's counting invariant.

    Every goal list must satisfy: 0 <= proved_count <= len(goals).
    An empty list has zero proved goals.

    axiomander:
        requires:
            total_goals >= 0
            proved_goals >= 0
            proved_goals <= total_goals
        ensures:
            result == proved_goals
            result <= total_goals
            implies(total_goals == 0, result == 0)
    """
    return proved_goals


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
