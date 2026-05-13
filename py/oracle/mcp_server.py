#!/usr/bin/env python3
"""
MCP Server — Refactoring Robots contract verification.

Tools:
  check-file     — Analyze a Python file for contract adornment opportunities.
                  Suggests where to add pre/post/invariant assertions.
                  Runs lightweight structural analysis (no Coq).
  
  check-function — Verify a single function with assert contracts.
                  Runs Level 1 (wp_reduce). Returns status + LLM guidance
                  if verification fails.
"""

import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

import ast

from .advisor import (
    analyze_function,
    analyze_file,
    generate_llm_guidance,
    AdornmentAdvice,
    FunctionAnalysis,
    FileAnalysis,
)
from .contract_linter import ContractLinter, AssertInfo
from .python_to_imp import python_to_imp
from .reporting import (
    Action, GoalStatus, ProofLevel, PipelineReport,
    build_report, action_guidance,
)

PROJECT_ROOT = Path(os.environ.get(
    "REFACTORING_ROBOTS_ROOT",
    str(Path(__file__).resolve().parent.parent.parent)
))
BUILD_DIR = PROJECT_ROOT / "_build" / "default" / "coq"


# ═══════════════════════════════════════════════════════════════════
# Tool: check-file
# ═══════════════════════════════════════════════════════════════════

def tool_check_file(args: dict) -> str:
    """Analyze a Python file and suggest where to add contracts."""
    source = args.get("source", "")
    if not source:
        return "Error: 'source' parameter is required."

    analysis = analyze_file(source)

    lines = [
        f"# Contract Analysis\n",
        f"**{analysis.summary}**\n",
        f"| Function | Pre | Post | Inv | Loops | Guidance |",
        f"|----------|-----|------|-----|-------|----------|",
    ]

    for f in analysis.functions:
        pre = "✓" if f.has_preconditions else "—"
        post = "✓" if f.has_postconditions else "—"
        inv = "✓" if f.has_invariants else "—"
        loops = "✓" if f.has_loops else "—"

        if not f.suggested_adornments:
            guidance = "Fully adorned"
        else:
            guidance = f"{len(f.suggested_adornments)} suggestion(s)"

        lines.append(f"| `{f.name}` | {pre} | {post} | {inv} | {loops} | {guidance} |")

    lines.append("")
    lines.append("## Suggested Adornments\n")

    for f in analysis.functions:
        if f.suggested_adornments:
            lines.append(f"### `{f.name}`")
            for s in f.suggested_adornments:
                lines.append(f"- **{s.location}** (line {s.line}): `{s.suggestion}`")
                if s.reasoning:
                    lines.append(f"  - *{s.reasoning}*")
                if s.template:
                    lines.append(f"  - Template: `{s.template}`")
            lines.append("")

        if f.existing_asserts:
            lines.append(f"#### Existing assertions in `{f.name}`:")
            for a in f.existing_asserts:
                lines.append(f"- {a}")
            lines.append("")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Tool: check-function
# ═══════════════════════════════════════════════════════════════════

def tool_check_function(args: dict) -> str:
    """Verify a single function and return guidance."""
    source = args.get("source", "")
    func_name = args.get("function_name", "")
    if not source:
        return "Error: 'source' parameter is required."

    # Step 1: Structural analysis
    analysis = analyze_function(source, func_name)

    # Check for missing contracts BEFORE attempting verification
    missing = []
    if not analysis.has_preconditions:
        missing.append("precondition")
    if not analysis.has_postconditions:
        missing.append("postcondition")
    # Loops without user invariants get a default invariant from the translator;
    # don't block — let verification try with the generated invariant.

    if missing:
        lines = [f"# Verification: `{analysis.name}`\n"]
        lines.append(f"**Cannot verify yet** — missing: {', '.join(missing)}\n")

        if analysis.suggested_adornments:
            lines.append("## Add these assertions first:\n")
            for s in analysis.suggested_adornments:
                lines.append(f"- **{s.location}** (line ~{s.line}): {s.suggestion}")
                if s.template:
                    lines.append(f"  ```python\n  {s.template}\n  ```")
            lines.append("")

        lines.append("After adding these assertions, run `check-function` again to verify.")
        return "\n".join(lines)

    # Step 2: Try verification
    t0 = time.time()
    goal = _verify_function(source, func_name, args.get("hint"))
    elapsed = (time.time() - t0) * 1000

    # Step 2b: If Level 1 couldn't close the goal, try LLM oracle
    if goal and not goal.is_proved():
        goal = _try_llm_oracle(source, func_name, goal)
        elapsed = (time.time() - t0) * 1000

    # Step 3: Build report
    lines = [f"# Verification: `{analysis.name}`\n"]

    if goal and goal.is_proved():
        method = f" ({goal.proof_method})" if goal.proof_method else ""
        lines.append(f"**✓ Proved ({goal.level.value}){method}** — {elapsed:.0f}ms\n")
        return "\n".join(lines)

    # Failed — generate guidance
    lines.append(f"**✗ Not proved** — {elapsed:.0f}ms\n")

    # Structural issues first
    if analysis.suggested_adornments:
        lines.append("## Missing Contracts\n")
        for s in analysis.suggested_adornments:
            lines.append(f"- **{s.location}** (line ~{s.line}): {s.suggestion}")
            if s.template:
                lines.append(f"  ```python\n  {s.template}\n  ```")
        lines.append("")

    # Verification details
    if goal:
        if goal.error_detail:
            lines.append(f"## Error\n```\n{goal.error_detail[:800]}\n```\n")
        if goal.dependencies:
            lines.append(f"## Hammer suggested lemmas\n{', '.join(goal.dependencies)}\n")

    # LLM guidance
    guidance = generate_llm_guidance(
        func_name=analysis.name,
        goal_statement=goal.goal_statement if goal else "unknown",
        error_detail=goal.error_detail if goal else "unknown",
        existing_asserts=analysis.existing_asserts,
        suggestions=analysis.suggested_adornments,
    )
    lines.append(f"## Guidance\n{guidance}\n")

    return "\n".join(lines)


def _verify_function(source: str, func_name: str, hint: str | None = None) -> GoalStatus | None:
    """Try to verify a function. Returns GoalStatus or None on error."""
    try:
        tree = ast.parse(source)
    except SyntaxError as e:
        return GoalStatus(name=func_name, goal_statement="",
                          level=ProofLevel.UNPROVED,
                          error_detail=str(e),
                          suggested_action=Action.REFACTOR,
                          suggestion_text=f"Syntax error: {e}")

    func_node = None
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and (not func_name or node.name == func_name):
            func_node = node
            break

    if func_node is None:
        return GoalStatus(name=func_name, goal_statement="",
                          level=ProofLevel.UNPROVED,
                          error_detail="Function not found",
                          suggested_action=Action.REFACTOR,
                          suggestion_text=f"Function '{func_name}' not found in source")

    # Compute expanded params from class definitions
    params = [arg.arg for arg in func_node.args.args]
    expanded, class_fields, _, init_state, record_section = _expand_params(tree, params, func_node)

    # Lint with expanded params (so result, account.balance are scoped correctly)
    linter_pre = ContractLinter(expanded, "precondition")
    linter_post = ContractLinter(expanded, "postcondition")
    lint_results: list[AssertInfo] = []
    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Assert):
            cls = _classify_assert(func_node, stmt)
            linter = linter_pre if cls == "precondition" else linter_post
            lr = linter.lint_expression(stmt.test)
            lint_results.append(AssertInfo(
                node=stmt, lineno=stmt.lineno, col_offset=stmt.col_offset,
                classification=cls, lint_result=lr,
            ))

    bad = [r for r in lint_results if not r.lint_result.is_valid]
    if bad:
        msgs = []
        for r in bad:
            for v in r.lint_result.violations:
                msgs.append(f"Line {r.lineno}: {v.message}")
        return GoalStatus(name=func_name, goal_statement="",
                          level=ProofLevel.UNPROVED,
                          error_detail="\n".join(msgs),
                          suggested_action=Action.REFACTOR,
                          suggestion_text="Fix lint errors in assertions.")

    # Generate IMP + Coq
    imp_body = python_to_imp(func_node)
    coq_source = _generate_coq(func_node, lint_results, imp_body, tree, hint)

    # Write temp file and compile
    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".v", delete=False, prefix=f"mcp_{func_name}_",
        ) as f:
            f.write(coq_source)
            tmp_path = Path(f.name)

        coq_timeout = 120 if hint == "hammer" else 30
        result = subprocess.run(
            ["coqc", "-R", str(BUILD_DIR), "Imp", str(tmp_path)],
            capture_output=True, text=True, timeout=coq_timeout,
            env={**os.environ},
        )

        if result.returncode == 0:
            # Check for remaining Admitted proofs
            with open(tmp_path) as f2:
                if "Admitted." in f2.read():
                    return GoalStatus(name=func_name,
                                    goal_statement=f"wp {func_name}_body ...",
                                    level=ProofLevel.UNPROVED,
                                    error_detail="Proof incomplete — remaining goals need SMT (Level 2) or LLM (Level 3).",
                                    suggested_action=Action.RETRY_LLM,
                                    suggestion_text="The VCG proof obligations are Admitted.")
            has_cond = "CIf" in imp_body
            has_while = "CWhile" in imp_body
            method = "wp_reduce"
            if hint == "hammer":
                method += " + hammer"
            elif has_cond:
                method += " + conditional split"
            if has_while:
                method += " + VCG"
            return GoalStatus(name=func_name,
                            goal_statement=f"wp {func_name}_body ...",
                            level=ProofLevel.LEVEL1_LTAC,
                            proof_method=method)

        error = result.stderr + result.stdout
        # Check for SMT counterexample in the generated source
        ce_hint = ""
        if "SMT counterexample:" in coq_source:
            import re
            m = re.search(r'SMT counterexample: (.*?) \*', coq_source)
            if m:
                ce_hint = f"\n\nSMT counterexample found: {m.group(1)}\nStrengthen the loop invariant to rule out these values."
        return GoalStatus(name=func_name,
                        goal_statement=f"wp {func_name}_body ...",
                        level=ProofLevel.UNPROVED,
                        error_detail=error[-800:] + ce_hint,
                        suggested_action=Action.RETRY_LLM,
                        suggestion_text=error[:200],
                        proof_method="wp_reduce")
    finally:
        if tmp_path:
            tmp_path.unlink(missing_ok=True)


def _try_llm_oracle(source: str, func_name: str, goal: GoalStatus) -> GoalStatus:
    """Try to prove remaining goals using the LLM oracle."""
    if not goal or goal.is_proved():
        return goal

    from .client import oracle_query, load_config
    import sys as _sys

    config = load_config()
    if not config.api_key:
        goal.error_detail += " (No LLM API key set)"
        return goal

    # Re-generate Coq to get the goal text
    import ast
    tree = ast.parse(source)
    func_node = None
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == func_name:
            func_node = node
            break
    if func_node is None:
        return goal

    params = [arg.arg for arg in func_node.args.args]
    expanded, _, params_coq, _, _ = _expand_params(tree, params, func_node)
    imp_body = python_to_imp(func_node)
    
    # Generate full Coq source
    linter_pre = ContractLinter(expanded, "precondition")
    linter_post = ContractLinter(expanded, "postcondition")
    lint_results: list = []
    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Assert):
            cls = _classify_assert(func_node, stmt)
            linter = linter_pre if cls == "precondition" else linter_post
            lr = linter.lint_expression(stmt.test)
            lint_results.append(AssertInfo(
                node=stmt, lineno=stmt.lineno, col_offset=stmt.col_offset,
                classification=cls, lint_result=lr,
            ))
    coq_source = _generate_coq(func_node, lint_results, imp_body, tree, None)

    # Extract the goal: the Theorem line plus the goal up to Proof
    import re
    goal_match = re.search(r'(Theorem \w+.*?)(?=Proof\.)', coq_source, re.DOTALL)
    if not goal_match:
        return goal
    goal_text = goal_match.group(1).strip()

    # Build context with definitions the LLM needs (valid Coq only)
    pres = [r for r in lint_results if r.classification == "precondition"]
    posts = [r for r in lint_results if r.classification == "postcondition"]
    coq_context = f"Definition {func_name}_body : com := {imp_body}.\n"
    llm_hint = (
        f"Use wp_prove as the FIRST tactic. Then: lia, reflexivity, split, intro, apply.\n"
        f"Keep it short. Most proofs are 1-2 lines after wp_prove.\n"
    )

    print(f"  [oracle] Attempting LLM proof for {func_name}...", file=_sys.stderr)
    result = oracle_query(
        goal=goal_text,
        context=coq_context,
        dependencies=[],
        coq_paths=[str(BUILD_DIR)],
        max_retries=2,
        hint=llm_hint,
        build_dir=BUILD_DIR,
    )

    if result.success:
        goal.level = ProofLevel.LEVEL3_LLM
        goal.error_detail = ""
        goal.suggested_action = Action.OK
        goal.suggestion_text = f"LLM proof ({result.attempts} attempts):\n{result.proof_script[:500]}"
        goal.proof_method = "LLM oracle"
    else:
        goal.error_detail += f" (LLM: {result.error_message[:80]})"

    return goal


def _classify_assert(func_node: ast.FunctionDef, assert_node: ast.Assert) -> str:
    """Classify an assert statement within a function."""
    body = func_node.body

    # Check if we're inside a loop
    for node in ast.walk(func_node):
        if isinstance(node, (ast.While, ast.For)):
            for i, s in enumerate(node.body):
                if s is assert_node:
                    if all(isinstance(x, ast.Assert) for x in node.body[:i]):
                        return "invariant"

    # Check if immediately before return, or part of a chain before return
    # Walk body to find the assert
    for i, s in enumerate(body):
        if s is assert_node:
            # Check forward: are all statements between here and the return asserts?
            j = i + 1
            while j < len(body) and isinstance(body[j], ast.Assert):
                j += 1
            if j < len(body) and isinstance(body[j], ast.Return):
                return "postcondition"

    # Check if at function start
    seen_code = False
    for i, s in enumerate(body[:body.index(assert_node) + 1]):
        is_doc = (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                  and isinstance(s.value.value, str))
        if not isinstance(s, ast.Assert) and not is_doc:
            if s is not assert_node:
                seen_code = True
    if not seen_code:
        return "precondition"

    return "general"


def _expand_params(tree, params, func_node: ast.FunctionDef | None = None):
    """Expand class params into flat fields for Coq theorem params.

    Extracts type annotations from function parameters to determine Coq types.
    Returns (expanded_params, class_fields, params_coq_str, init_state, record_section)."""
    import ast

    # Build a map of param name → Coq type from function annotations
    param_types: dict[str, str] = {}
    list_params: set[str] = set()
    if func_node:
        for arg in func_node.args.args:
            coq_type = _py_type_to_coq(arg.annotation)
            param_types[arg.arg] = coq_type
            if _is_list_param(arg.annotation):
                list_params.add(arg.arg)

    class_fields = {}
    record_section = ""
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef):
            record_section += _generate_record(node) + "\n"
            fields = []
            for stmt in node.body:
                if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                    fields.append(stmt.target.id)
            if fields:
                class_fields[node.name] = fields

    expanded = []
    parts = []
    init_state = "empty_state"
    for p in params:
        coq_type = param_types.get(p, "Z")
        cls_name = next((c for c in class_fields if c.lower() == p.lower()), None)
        if p in list_params:
            # List parameters: expose the length as a Coq parameter,
            # initialize the _len key in the state. Elements are opaque.
            len_var = f"{p}__len"
            expanded.append(len_var)
            parts.append(f"({len_var} : Z)")
            init_state = f'(upd {init_state} "{p}._len"%string {len_var})'
        elif cls_name:
            for f in class_fields[cls_name]:
                expanded.append(f"{p}_{f}")
                parts.append(f"({p}_{f} : Z)")
        else:
            expanded.append(p)
            parts.append(f"({p} : {coq_type})")
            init_state = f'(upd {init_state} "{p}"%string {p})'

    for p in params:
        cls_name = next((c for c in class_fields if c.lower() == p.lower()), None)
        if cls_name:
            for f in class_fields[cls_name]:
                init_state = f'(store_field "{p}"%string "{f}"%string {p}_{f} {init_state})'

    return expanded, class_fields, " ".join(parts), init_state, record_section


def _py_type_to_coq(annotation) -> str:
    """Map Python type annotation AST node to a Coq type string."""
    if annotation is None:
        return "Z"
    type_map = {"int": "Z", "float": "Z", "bool": "bool"}
    if isinstance(annotation, ast.Name):
        if annotation.id == "str":
            return "list"  # encode strings as Z-arrays (ordinals)
        return type_map.get(annotation.id, "Z")
    if isinstance(annotation, ast.Subscript):
        if isinstance(annotation.value, ast.Name) and annotation.value.id == "list":
            return "list"
    return "Z"


def _is_list_param(annotation) -> bool:
    """Check if a type annotation is a list type (or string — encoded as Z-array)."""
    if annotation is None:
        return False
    if isinstance(annotation, ast.Name) and annotation.id == "str":
        return True  # strings encoded as Z-arrays
    if isinstance(annotation, ast.Subscript):
        if isinstance(annotation.value, ast.Name) and annotation.value.id == "list":
            return True
    return False


def _generate_record(node) -> str:
    """Generate a Coq Record from a Python class definition."""
    import ast
    name = node.name
    fields = []
    for stmt in node.body:
        if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
            fname = stmt.target.id
            # Map Python types to Coq types
            ftype = "Z"  # default to Z
            if stmt.annotation and isinstance(stmt.annotation, ast.Name):
                py_type = stmt.annotation.id
                type_map = {"int": "Z", "float": "Z", "bool": "bool", "str": "string"}
                ftype = type_map.get(py_type, "Z")
            fields.append(f"  {name.lower()}_{fname} : {ftype}")

    if not fields:
        return f"(* Class {name} has no annotated fields *)"

    field_str = " ;\n".join(fields)
    return f"Record {name} : Type := {{\n{field_str}\n}}."


def _scope_vars(coq_expr: str, params: list[str]) -> str:
    """No-op: linter now produces state-scoped Coq directly from AST."""
    return coq_expr


def _unscope_vars(coq_expr: str) -> str:
    """Convert state lookups back to bare Coq variables for VCG.
    s \"x\"%string → x, s \"a.b\"%string → a_b."""
    import re
    result = re.sub(r's "([^"]+)"%string', r'\1', coq_expr)
    result = result.replace('.', '_')
    return result


def _vcg_result_scaffold(imp_body: str) -> str:
    """Extract the post-loop result assignment from the IMP body.
    
    For `result = len(xs)` → generates `result = xs__len ->` hypothesis.
    Returns "" if no result assignment found.
    """
    import re
    # Look for the last meaningful CAss to "result" (not the redundant copy)
    # Pattern: CAss "result"%string (expr)
    matches = list(re.finditer(
        r'\(CAss "result"%string\s+(\([^)]+(?:\([^)]*\)[^)]*)*\))',
        imp_body
    ))
    if not matches:
        return ""
    last = matches[-1].group(1)
    # If the assignment is just (AVar "result"%string), skip to the previous one
    if 'AVar "result"' in last and len(matches) > 1:
        last = matches[-2].group(1)
    if 'AVar "result"' in last:
        return ""
    # Convert the IMP aexp to an unscoped Coq Z expression
    coq_val = _imp_aexp_to_coq_z(last)
    if not coq_val:
        return ""
    return f"result = {coq_val} ->\n  "


def _imp_aexp_to_coq_z(aexp_str: str) -> str:
    """Convert an IMP aexp string to an unscoped Coq Z value.
    
    (ALen "xs"%string) → xs__len
    (AVar "x"%string) → x
    (ANum 5) → 5
    """
    import re
    aexp_str = aexp_str.strip()
    m = re.match(r'\(ALen "([^"]+)"%string\)', aexp_str)
    if m:
        return f"{m.group(1)}__len"
    m = re.match(r'\(AVar "([^"]+)"%string\)', aexp_str)
    if m:
        return m.group(1)
    m = re.match(r'\(ANum (\d+)\)', aexp_str)
    if m:
        return m.group(1)
    return ""


def _vcg_exit_condition(func_node) -> str:
    """Generate the VCG exit condition from the loop containing invariants.

    Walks the function AST to find the while/for loop whose body
    has invariant assertions, and returns the unscoped exit condition.
    """
    import ast

    def has_invariant(body: list[ast.stmt]) -> bool:
        """Check if the first non-assert stmt in body is preceded by asserts."""
        for s in body:
            if isinstance(s, ast.Assert):
                return True
            elif not isinstance(s, ast.Expr):  # skip docstrings
                return False
        return False

    for node in ast.walk(func_node):
        if isinstance(node, ast.While):
            if has_invariant(node.body):
                return _py_cond_to_vcg_exit(node.test)
        if isinstance(node, ast.For):
            if has_invariant(node.body):
                if (isinstance(node.iter, ast.Call)
                    and isinstance(node.iter.func, ast.Name)
                    and node.iter.func.id == "range"
                    and node.iter.args):
                    limit = node.iter.args[-1]
                    target = node.target
                    target_str = target.id if isinstance(target, ast.Name) else "i"
                    limit_str = _py_expr_to_coq_var(limit)
                    return f"Z.leb ({target_str} + 1) {limit_str} = false"
                return "Z.leb i n = false"

    # Fallback: use the first loop
    for node in ast.walk(func_node):
        if isinstance(node, ast.While):
            return _py_cond_to_vcg_exit(node.test)
        if isinstance(node, ast.For):
            return "Z.leb i n = false"
    return "Z.leb i n = false"


def _py_cond_to_vcg_exit(test: ast.expr) -> str:
    """Translate a Python comparison to a VCG exit condition.

    Exit means the condition evaluated to false.
    `i < n`  → `Z.leb (i + 1) n = false`
    `i <= n` → `Z.leb i n = false`
    """
    import ast
    if isinstance(test, ast.Compare) and len(test.ops) == 1 and len(test.comparators) == 1:
        left = _py_expr_to_coq_var(test.left)
        right = _py_expr_to_coq_var(test.comparators[0])
        op = test.ops[0]
        if isinstance(op, ast.Lt):
            return f"Z.leb ({left} + 1) {right} = false"
        elif isinstance(op, ast.LtE):
            return f"Z.leb {left} {right} = false"
        elif isinstance(op, ast.Gt):
            return f"Z.leb ({right} + 1) {left} = false"
        elif isinstance(op, ast.GtE):
            return f"Z.leb {right} {left} = false"
    return "Z.leb i n = false"


def _py_expr_to_coq_var(node: ast.expr) -> str:
    """Convert a simple Python expression to a Coq variable name."""
    import ast
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return str(node.value)
    if isinstance(node, ast.Call):
        name = _get_call_name(node)
        if name == "len" and node.args and isinstance(node.args[0], ast.Name):
            return f"{node.args[0].id}__len"
    return "?"


def _get_call_name(node: ast.Call) -> str | None:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        parts = []
        c = func
        while isinstance(c, ast.Attribute):
            parts.append(c.attr)
            c = c.value
        if isinstance(c, ast.Name):
            parts.append(c.id)
        return ".".join(reversed(parts))
    return None


def _try_smt_vcg(inv_coq: str, exit_cond: str, post_vcg: str, scaffold: str) -> bool:
    """Try to prove the VCG using an SMT solver. (Legacy — uses regex parser.)

    Returns True if the SMT solver proves the VCG (UNSAT).
    """
    from .smt_export import verify_vcg
    result = verify_vcg(
        invariant=inv_coq,
        exit_cond=exit_cond,
        postcondition=post_vcg,
        scaffold=scaffold.strip().rstrip('->').strip() if scaffold else "",
        solver="cvc4",
    )
    return result.is_valid


def _try_smt_vcg_ir(inv_irs: list, exit_cond: str, post_irs: list, scaffold: str = "", return_model: bool = False):
    """Try to prove the VCG using SMT, generating SMT-LIB directly from IR nodes.

    Returns SmtResult. The caller checks .is_valid.
    """
    from .contract_ir import Logical
    from .smt_export import _expr_to_smt, _extract_vars, SmtResult

    if not inv_irs or not post_irs:
        return SmtResult(is_valid=False, error="No IR nodes")

    inv = Logical("and", list(inv_irs)) if len(inv_irs) > 1 else inv_irs[0]
    post = Logical("and", list(post_irs)) if len(post_irs) > 1 else post_irs[0]
    exit_smt = _expr_to_smt(exit_cond)

    inv_smt = inv.to_smt()
    post_smt = post.to_smt()

    if not inv_smt or not exit_smt or not post_smt:
        return SmtResult(is_valid=False, error="Expression conversion failed")

    # Include scaffold in variable extraction and as an assertion
    scaffold_stripped = scaffold.strip().rstrip("->").strip() if scaffold else ""
    scaff_smt = _expr_to_smt(scaffold_stripped) if scaffold_stripped else ""
    all_vars_coq = inv.to_coq(False) + " " + exit_cond + " " + post.to_coq(False)
    if scaffold_stripped:
        all_vars_coq += " " + scaffold_stripped
    vars_set = _extract_vars(all_vars_coq)

    lines = [
        "(set-logic QF_NIA)",
        "(set-option :produce-models true)",
    ]
    for v in sorted(vars_set):
        lines.append(f"(declare-fun {v} () Int)")

    lines.append(f"(assert {inv_smt})")
    lines.append(f"(assert {exit_smt})")
    if scaff_smt:
        lines.append(f"(assert {scaff_smt})")
    lines.append(f"(assert (not {post_smt}))")
    lines.append("(check-sat)")
    lines.append("(get-model)")

    import subprocess
    import tempfile
    import os
    from pathlib import Path

    smt_src = "\n".join(lines)
    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".smt2", delete=False, prefix="vcg_ir_"
        ) as f:
            f.write(smt_src)
            tmp_path = Path(f.name)

        result = subprocess.run(
            ["cvc4", str(tmp_path)],
            capture_output=True, text=True, timeout=10,
            env={**os.environ},
        )
        from .smt_export import _parse_smt_output
        return _parse_smt_output(result.stdout + result.stderr, "cvc4")
    except Exception as e:
        return SmtResult(is_valid=False, error=str(e)[:200])
    finally:
        if tmp_path and tmp_path.exists():
            tmp_path.unlink(missing_ok=True)


def _generate_coq(func_node, lint_results, imp_body: str, full_tree=None, hint: str | None = None) -> str:
    """Generate Coq theorem file for a function."""
    import ast

    name = func_node.name
    params = [arg.arg for arg in func_node.args.args]

    # Compute expanded params, init state, and record section
    if full_tree is not None:
        expanded_params, class_fields, params_coq, init_state, record_section = \
            _expand_params(full_tree, params, func_node)
    else:
        expanded_params = params
        coq_types = {
            arg.arg: _py_type_to_coq(arg.annotation)
            for arg in func_node.args.args
        }
        params_coq = " ".join(f"({p} : {coq_types.get(p, 'Z')})" for p in params)
        init_state = "empty_state"
        for p in params:
            init_state = f'(upd {init_state} "{p}"%string {p})'
        record_section = ""

    pres = [r for r in lint_results if r.classification == "precondition"]
    posts = [r for r in lint_results if r.classification == "postcondition"]
    invs = [r for r in lint_results if r.classification == "invariant"]

    pre_coq = " /\\ ".join(
        r.lint_result.coq_translation
        for r in pres if r.lint_result.coq_translation
    ) or "True"
    post_coq = " /\\ ".join(
        r.lint_result.coq_translation
        for r in posts if r.lint_result.coq_translation
    ) or "True"

    # Check for while/for loops and generate VCG obligation
    has_while = any(isinstance(n, (ast.While, ast.For)) for n in ast.walk(func_node))
    vcg_section = ""
    if has_while and invs:
        inv_coq = " /\\ ".join(
            _unscope_vars(r.lint_result.coq_translation)
            for r in invs if r.lint_result.coq_translation
        ) or "True"
        post_vcg = " /\\ ".join(
            _unscope_vars(r.lint_result.coq_translation)
            for r in posts if r.lint_result.coq_translation
        ) or "True"
        exit_cond = _vcg_exit_condition(func_node)
        result_scaffold = _vcg_result_scaffold(imp_body)

        # Try SMT first (Level 2) for the VCG — use IR for clean SMT-LIB generation
        inv_irs = [r.lint_result.ir for r in invs if r.lint_result.ir]
        post_irs = [r.lint_result.ir for r in posts if r.lint_result.ir]
        smt_result = _try_smt_vcg_ir(inv_irs, exit_cond, post_irs, result_scaffold)

        if smt_result.is_valid:
            vcg_section = f"""
(* Verification condition proved by SMT (cvc4) *)
(* {inv_coq} -> {exit_cond} -> {post_vcg} *)
"""
        if smt_result.is_valid:
            vcg_section = f"""
(* Verification condition proved by SMT (cvc4) *)
(* {inv_coq} -> {exit_cond} -> {post_vcg} *)
"""
        else:
            # SMT couldn't prove it — generate Coq VCG (may fail via lia/LLM)
            # If SMT found a counterexample, annotate the generated Coq
            ce_note = ""
            if smt_result.counterexample:
                ce_str = ", ".join(f"{k}={v}" for k, v in smt_result.counterexample.items())
                ce_note = f" (* SMT counterexample: {ce_str} — strengthen invariant to rule this out *)"
            import re
            all_vcg_vars = set()
            for expr in [inv_coq, post_vcg]:
                for vname in re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', expr):
                    if vname not in {'True', 'False', 'Z', 'string', 'and', 'or', 'not', 'fun', 's', 'parray_key'}:
                        all_vcg_vars.add(vname)
            all_vcg_vars.add("result")
            for vname in ["i", "n"]:
                all_vcg_vars.add(vname)
            vcg_params = " ".join(f"({v} : Z)" for v in sorted(all_vcg_vars))
            n_params = len(all_vcg_vars)
            intros_pat = " ".join(["?"] * n_params) + " Hinv Hexit" if n_params > 0 else "Hinv Hexit"
            vcg_section = f"""(* Verification condition: invariant + exit → postcondition{ce_note} *)
Theorem {name}_vcg_exit : forall {vcg_params},
  ({inv_coq}) ->
  {exit_cond} ->
  {result_scaffold}
  ({post_vcg}).
Proof.
  intros {intros_pat} Hres.
  apply Z.leb_gt in Hexit.
  repeat (match goal with [H: _ /\\ _ |- _] => destruct H end).
  lia.
Qed.
"""

    has_bor = "BOr" in imp_body
    has_cif = "CIf" in imp_body

    # Don't use conditional proof if there's a while loop — CWhile's
    # (fun _ => True) makes the WP trivial; conditional is handled inside.
    use_conditional_proof = has_cif and not has_while

    # Determine the proof strategy based on body complexity
    hammer_import = ""
    if hint == "hammer":
        hammer_import = "From Hammer Require Import Hammer.\n"
        hammer_config = "  Set Hammer ATPLimit 30.\n  Set Hammer ReconstrLimit 10.\n"
        if use_conditional_proof:
            if has_bor:
                proof = hammer_config + "  intros.\n  wp_reduce.\n  split; intro Hb.\n  - apply Bool.orb_true_iff in Hb. destruct Hb as [Hc|Hc]; apply Z.leb_le in Hc; wp_prove; split; try lia; try hammer.\n  - apply Bool.orb_false_iff in Hb. destruct Hb as [Hc1 Hc2]; apply Z.leb_gt in Hc1; apply Z.leb_gt in Hc2; wp_prove; split; try lia; try hammer."
            else:
                proof = hammer_config + "  intros.\n  wp_reduce.\n  split; [ intro Hle; apply Z.leb_le in Hle | intro Hgt; apply Z.leb_gt in Hgt ];\n  wp_prove; split; try lia; try hammer.\n  (* If hammer still fails, try LLM oracle *)"
        else:
            proof = hammer_config + "  intros.\n  wp_reduce.\n  hammer."
    elif use_conditional_proof:
        if has_bor:
            proof = "  intros.\n  wp_reduce.\n  split; intro Hb.\n  - apply Bool.orb_true_iff in Hb. destruct Hb as [Hc|Hc]; apply Z.leb_le in Hc; wp_prove; split; lia.\n  - apply Bool.orb_false_iff in Hb. destruct Hb as [Hc1 Hc2]; apply Z.leb_gt in Hc1; apply Z.leb_gt in Hc2; wp_prove; split; lia."
        else:
            proof = "  intros.\n  wp_reduce.\n  split; [ intro Hle; apply Z.leb_le in Hle | intro Hgt; apply Z.leb_gt in Hgt ];\n  wp_prove; split; lia."
    else:
        proof = "  intros.\n  wp_prove."

    bool_import = "Require Import Bool.\n" if has_bor else ""

    return f"""(* Auto-generated from {name} *)
{hammer_import}
Require Import ZArith String List Lia.
{bool_import}Require Import Imp Wp Pydantic WpTactics.
Import ListNotations.
Open Scope Z_scope.

{record_section}
Definition {name}_body : com :=
  {imp_body}.

Theorem {name}_correct : forall {params_coq},
  ({pre_coq}) ->
  wp {name}_body
     (fun s => {post_coq})
     ({init_state}).
Proof.
{proof}
Qed.
{vcg_section}"""


# ═══════════════════════════════════════════════════════════════════
# MCP Protocol
# ═══════════════════════════════════════════════════════════════════

TOOLS = [
    {
        "name": "check-file",
        "description": (
            "Analyze a Python file for contract adornment opportunities. "
            "Suggests where to add assert-based preconditions, postconditions, "
            "and loop invariants. Does NOT run verification — just structural analysis."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "source": {
                    "type": "string",
                    "description": "Python source code to analyze",
                },
            },
            "required": ["source"],
        },
    },
    {
        "name": "check-function",
        "description": (
            "Verify a single Python function with assert-based contracts. "
            "Runs Level 1 verification (wp_reduce). If it fails, returns "
            "LLM-generated guidance on what assertions to add or change, "
            "and whether the property might be false."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "source": {
                    "type": "string",
                    "description": "Python source code containing the function",
                },
                "function_name": {
                    "type": "string",
                    "description": "Name of the function to verify",
                },
            },
            "required": ["source", "function_name"],
        },
    },
]


def handle_initialize(params: dict) -> dict:
    return {
        "protocolVersion": "2024-11-05",
        "capabilities": {"tools": {}},
        "serverInfo": {"name": "verify-contracts", "version": "0.2.0"},
    }


def handle_list_tools() -> dict:
    return {"tools": TOOLS}


def handle_call_tool(params: dict) -> dict:
    name = params.get("name", "")
    args = params.get("arguments", {})

    if name == "check-file":
        result = tool_check_file(args)
    elif name == "check-function":
        result = tool_check_function(args)
    else:
        return {"content": [{"type": "text", "text": f"Unknown tool: {name}"}], "isError": True}

    return {"content": [{"type": "text", "text": result}]}


def main():
    import sys
    if len(sys.argv) > 1:
        _cli(sys.argv)
        return
    for line in sys.stdin:
        try:
            request = json.loads(line.strip())
        except json.JSONDecodeError:
            continue

        rid = request.get("id")
        method = request.get("method", "")

        if method == "initialize":
            res = handle_initialize(request.get("params", {}))
        elif method == "tools/list":
            res = handle_list_tools()
        elif method == "tools/call":
            res = handle_call_tool(request.get("params", {}))
        else:
            sys.stdout.write(json.dumps({
                "jsonrpc": "2.0", "id": rid,
                "error": {"code": -32601, "message": f"Unknown: {method}"}
            }) + "\n")
            sys.stdout.flush()
            continue

        sys.stdout.write(json.dumps({"jsonrpc": "2.0", "id": rid, "result": res}) + "\n")
        sys.stdout.flush()


def _cli(argv: list[str] | None = None):
    """CLI mode using Typer."""
    import typer
    from pathlib import Path as _Path
    from typing import Optional

    app = typer.Typer(no_args_is_help=True)

    @app.command()
    def check_file(file: str):
        """Analyze a Python file for contract adornment opportunities."""
        typer.echo(tool_check_file({"source": _Path(file).read_text()}))

    @app.command()
    def check_function(
        file: str,
        function: str = typer.Option(..., "--function", "-f", help="Function name to verify"),
        hint: Optional[str] = typer.Option(None, "--hint", help="Tactic hint: hammer, smt, lia, auto"),
    ):
        """Verify a single function with assert contracts."""
        opts = {"source": _Path(file).read_text(), "function_name": function}
        if hint:
            opts["hint"] = hint
        typer.echo(tool_check_function(opts))

    app()


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1:
        _cli(sys.argv)
    else:
        main()
