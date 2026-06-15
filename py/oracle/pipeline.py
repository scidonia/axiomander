"""
Proof Pipeline Orchestrator

Coordinates the 3-tier proof pipeline for every contracted function in a
Python file by delegating to the real verification engine in mcp_server.

  Level 1 (Ltac):       wp_reduce, lia
  Level 2 (SMT):        coq-hammer -> cvc4 / eprover
  Level 3 (LLM oracle): DeepSeek / OpenAI -> Coq proof script

Usage:
    eval $(opam env)
    python -m py.oracle.pipeline py/examples/demo.py [--function NAME]
                                                      [--json] [--quiet]

Exit codes:
    0  all goals verified
    1  one or more goals not verified (unproved / counterexample / error)
    2  usage error, file not found, syntax error, or toolchain missing
"""

import argparse
import ast
import json as _json
import shutil
import sys
import time
from pathlib import Path

from .mcp_server import _verify_function
from .reporting import PipelineReport, GoalStatus, ProofLevel


# ---------------------------------------------------------------------------
# Toolchain guard
# ---------------------------------------------------------------------------

def _check_toolchain() -> None:
    """Raise SystemExit with a clear message if coqc is not on PATH."""
    if shutil.which("coqc") is None:
        sys.exit(
            "ERROR: coqc not found on PATH.\n"
            "Run `eval $(opam env)` to activate the Coq toolchain, then retry."
        )


# ---------------------------------------------------------------------------
# Function discovery
# ---------------------------------------------------------------------------

def _enumerate_functions(tree: ast.Module) -> list[str]:
    """Return names of top-level functions and class methods.

    Uses ast.iter_child_nodes (not ast.walk) to avoid double-counting
    nested helpers.  Descends one level into ClassDef for methods,
    mirroring the convention in mcp_server._build_contract_map.
    """
    names: list[str] = []
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.FunctionDef):
            names.append(node.name)
        elif isinstance(node, ast.ClassDef):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, ast.FunctionDef):
                    names.append(child.name)
    return names


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

def run_pipeline(python_file: Path) -> PipelineReport:
    """Run the full 3-tier pipeline on every contracted function in a file.

    Returns a PipelineReport aggregating per-function GoalStatus results.
    Prints a one-line status for each function as it is verified.
    """
    _check_toolchain()

    source = python_file.read_text()
    try:
        tree = ast.parse(source, filename=str(python_file))
    except SyntaxError as exc:
        sys.exit(f"ERROR: syntax error in {python_file}: {exc}")

    func_names = _enumerate_functions(tree)
    if not func_names:
        print(f"No functions found in {python_file.name}.")
        return PipelineReport(
            source_file=str(python_file),
            total_goals=0,
            proved_goals=0,
            goals=[],
        )

    goals: list[GoalStatus] = []
    t0 = time.monotonic()

    for name in func_names:
        result = _verify_function(source, name)
        if result is None:
            # _verify_function returns None only on internal error; treat as
            # unproved so the report is complete.
            result = GoalStatus(
                name=name,
                goal_statement="",
                level=ProofLevel.UNPROVED,
                error_detail="internal error in _verify_function",
            )

        goals.append(result)

        # Per-function status line
        if result.is_proved():
            print(f"  PROVED   {name}  [{result.level.value}]")
        elif result.level == ProofLevel.COUNTEREXAMPLE:
            ce = result.counterexample or result.theory_counterexample
            print(f"  COUNTER  {name}  counterexample: {ce}")
        else:
            detail = result.error_detail or result.suggestion_text or ""
            print(f"  UNPROVED {name}  {detail[:80]}")

    elapsed_ms = (time.monotonic() - t0) * 1000.0
    proved = sum(1 for g in goals if g.is_proved())

    report = PipelineReport(
        source_file=str(python_file),
        total_goals=len(goals),
        proved_goals=proved,
        goals=goals,
        elapsed_total_ms=elapsed_ms,
    )
    return report


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    """Argparse CLI for the pipeline.

    Returns an integer exit code:
      0  all goals verified
      1  one or more goals not verified
      2  usage / file / toolchain error
    """
    parser = argparse.ArgumentParser(
        prog="python -m py.oracle.pipeline",
        description="Run the Axiomander 3-tier proof pipeline on a Python file.",
    )
    parser.add_argument("file", help="Python source file to verify")
    parser.add_argument(
        "--function", "-f",
        metavar="NAME",
        default=None,
        help="Verify only this function (default: all functions)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        default=False,
        help="Emit the canonical JSON report to stdout instead of human text",
    )
    parser.add_argument(
        "--quiet", "-q",
        action="store_true",
        default=False,
        help="Suppress per-function status lines (summary still printed unless --json)",
    )

    try:
        args = parser.parse_args(argv)
    except SystemExit:
        return 2

    py_file = Path(args.file)
    if not py_file.exists():
        print(f"ERROR: file not found: {py_file}", file=sys.stderr)
        return 2

    if shutil.which("coqc") is None:
        print(
            "ERROR: coqc not found on PATH.\n"
            "Run `eval $(opam env)` to activate the Coq toolchain, then retry.",
            file=sys.stderr,
        )
        return 2

    source = py_file.read_text()
    try:
        tree = ast.parse(source, filename=str(py_file))
    except SyntaxError as exc:
        print(f"ERROR: syntax error in {py_file}: {exc}", file=sys.stderr)
        return 2

    func_names = _enumerate_functions(tree)

    # Filter to a single function when --function is given.
    if args.function:
        if args.function not in func_names:
            print(
                f"ERROR: function '{args.function}' not found in {py_file.name}.\n"
                f"Available: {', '.join(func_names) or '(none)'}",
                file=sys.stderr,
            )
            return 2
        func_names = [args.function]

    if not func_names:
        if not args.quiet:
            print(f"No functions found in {py_file.name}.")
        if args.json:
            from .reporting import build_report
            print(build_report(str(py_file), []).to_json())
        return 0

    goals: list[GoalStatus] = []
    t0 = time.monotonic()

    for name in func_names:
        result = _verify_function(source, name)
        if result is None:
            result = GoalStatus(
                name=name,
                goal_statement="",
                level=ProofLevel.UNPROVED,
                error_detail="internal error in _verify_function",
            )
        goals.append(result)

        if not args.quiet and not args.json:
            if result.is_proved():
                print(f"  PROVED   {name}  [{result.level.value}]")
            elif result.level == ProofLevel.COUNTEREXAMPLE:
                ce = result.counterexample or result.theory_counterexample
                print(f"  COUNTER  {name}  counterexample: {ce}")
            else:
                detail = result.error_detail or result.suggestion_text or ""
                print(f"  UNPROVED {name}  {detail[:80]}")

    elapsed_ms = (time.monotonic() - t0) * 1000.0
    proved = sum(1 for g in goals if g.is_proved())

    report = PipelineReport(
        source_file=str(py_file),
        total_goals=len(goals),
        proved_goals=proved,
        goals=goals,
        elapsed_total_ms=elapsed_ms,
    )

    if args.json:
        print(report.to_json())
    elif not args.quiet:
        print(f"\n{'=' * 50}")
        print(report.summary())
        print(f"Elapsed: {elapsed_ms:.0f} ms")

    # Exit 0 if all verified, 1 if any not verified.
    return 0 if proved == len(goals) else 1


if __name__ == "__main__":
    sys.exit(main())
