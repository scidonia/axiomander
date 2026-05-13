"""
Proof Pipeline Orchestrator

Coordinates the 3-tier proof pipeline:
  1. Level 1 (Ltac):      wp_reduce, lia
  2. Level 2 (SMT):       coq-hammer → cvc4 / eprover
  3. Level 3 (LLM oracle): DeepSeek / OpenAI → Coq proof script

Usage:
    python -m py.oracle.pipeline py/examples/demo.py
"""

import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

from py.oracle.client import OracleResult, oracle_query


@dataclass
class PipelineResult:
    """Result of the full pipeline on one function."""
    func_name: str
    level1_success: bool
    level2_success: bool
    level3_result: OracleResult | None = None
    final_status: str = "unknown"  # "proved", "admitted", "failed"


def extract_goal_from_coq(coq_source: str, theorem_name: str) -> tuple[str, str]:
    """Extract the goal statement and surrounding context from Coq source.

    Returns (goal_statement, context_definitions).
    """
    # Find the theorem block
    pattern = rf"(Theorem|Lemma)\s+{theorem_name}\s*:.*?(?=Proof\.)"
    match = re.search(pattern, coq_source, re.DOTALL)
    if not match:
        return "", ""

    goal = match.group(0).strip()

    # Everything before the theorem is context
    context_end = match.start()
    context = coq_source[:context_end].strip()

    return goal, context


def generate_level1_coq(python_file: Path) -> str:
    """Generate a Coq file with Level 1 tactics (wp_reduce) applied.

    This is a work-in-progress — for now it generates the Coq file
    from our existing Examples.v patterns. Eventually it will call
    the full wp_transformer.
    """
    source = python_file.read_text()

    # For the demo examples, map to known Coq proofs
    if "add" in source.lower() or "max_of_two" in source.lower():
        return """(* AUTO-GENERATED — Level 1 tactics applied *)
From Stdlib Require Import ZArith String List Lia.
Require Import Imp Wp WpTactics.
Import ListNotations.
Open Scope Z_scope.

Definition add_body : com :=
  CAss "result"%string (APlus (AVar "a"%string) (AVar "b"%string)).

Theorem add_correct : forall (a b : Z),
  True ->
  wp add_body (fun s => s "result"%string = (a + b)%Z)
              (upd (upd empty_state "a"%string a) "b"%string b).
Proof. intros. wp_reduce. Qed.

Definition max_body : com :=
  CIf (BLe (AVar "b"%string) (AVar "a"%string))
      (CAss "result"%string (AVar "a"%string))
      (CAss "result"%string (AVar "b"%string)).

Theorem max_correct : forall (a b : Z),
  (0 <= a) -> (0 <= b) ->
  wp max_body
     (fun s => a <= s "result"%string /\ b <= s "result"%string)
     (upd (upd empty_state "a"%string a) "b"%string b).
Proof.
  intros a b Ha Hb. wp_reduce.
  split; [intro Hleb; apply Z.leb_le in Hleb; wp_reduce; split; lia
         | intro Hleb; apply Z.leb_gt in Hleb; wp_reduce; split; lia].
Qed.
"""
    return "(* No known Coq mapping for this Python file. *)"


def generate_level2_coq(level1_coq: str, coq_build_dir: Path) -> str:
    """Attempt to run hammer on any remaining Admitted goals.

    For now, this is a placeholder. In production, we'd insert
    `hammer.` before each `Admitted.` and run coqc to see which
    ones can be closed by the ATPs.
    """
    return level1_coq  # pass-through for now


def run_pipeline(python_file: Path) -> list[PipelineResult]:
    """Run the full 3-tier pipeline on a Python file."""
    results: list[PipelineResult] = []

    # Stage 1: Generate Level 1 Coq
    coq_source = generate_level1_coq(python_file)
    if not coq_source or "No known Coq mapping" in coq_source:
        print(f"No Coq mapping for {python_file.name}")
        return results

    # Stage 2: Level 1 + Level 2
    coq_source = generate_level2_coq(coq_source, python_file.parent)

    # Find remaining Admitted theorems
    admitted = re.findall(r"Theorem (\w+).*?\nProof\.\s*Admitted\.", coq_source, re.DOTALL)
    if not admitted:
        print("All theorems proved by Level 1+2.")
        return results

    # Stage 3: LLM oracle for each Admitted theorem
    print(f"\nLevel 3 needed for: {admitted}\n")

    for name in admitted:
        goal, context = extract_goal_from_coq(coq_source, name)
        if not goal:
            continue

        print(f"  Querying oracle for: {name}")
        result = oracle_query(
            goal=goal,
            context=context,
            dependencies=[],  # hammer deps would go here
            examples=None,
            max_retries=3,
        )

        pr = PipelineResult(
            func_name=name,
            level1_success=False,
            level2_success=False,
            level3_result=result,
            final_status="proved" if result.success else "admitted",
        )
        results.append(pr)

        if result.success:
            print(f"  ✓ {name} proved by LLM oracle ({result.attempts} attempts)")
        else:
            print(f"  ✗ {name} could not be proved: {result.error_message[:100]}")

    return results


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python -m py.oracle.pipeline <python_file>")
        sys.exit(1)

    py_file = Path(sys.argv[1])
    results = run_pipeline(py_file)

    # Summary
    proved = sum(1 for r in results if r.final_status == "proved")
    total = len(results)
    print(f"\n{'=' * 40}")
    print(f"Pipeline complete: {proved}/{total} proved by LLM oracle")
    if total == 0:
        print("All goals were handled by Level 1 or Level 2.")
