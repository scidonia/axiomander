#!/usr/bin/env python3
"""
MCP Server — Axiomander contract verification.

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
from .cache import (
    VerificationCache, FunctionHashes,
    compute_body_hash, compute_contract_hash, compute_local_assert_hash,
    compute_cache_key,
)
from .contract_linter import ContractLinter, AssertInfo
from .purity_analyzer import (
    analyze_purity, generate_frame_conditions, generate_havoc_body,
    PurityReport,
)
from .python_to_imp import python_to_imp
from .reporting import (
    Action, GoalStatus, ProofLevel, PipelineReport,
    build_report, action_guidance,
)

PROJECT_ROOT = Path(os.environ.get(
    "AXIOMANDER_ROOT",
    str(Path(__file__).resolve().parent.parent.parent)
))
BUILD_DIR = PROJECT_ROOT / "_build" / "default" / "coq"

_cache = VerificationCache()


def _compute_hashes(source: str, func_name: str, tree: "ast.Module | None" = None) -> FunctionHashes | None:
    """Compute all hashes for a function without running full verification.

    Returns FunctionHashes or None if the function can't be found/parsed.
    """
    if tree is None:
        try:
            tree = ast.parse(source)
        except SyntaxError:
            return None

    func_node = None
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == func_name:
            func_node = node
            break
    if func_node is None:
        return None

    params = [name for name, _ in _func_params(func_node)]
    expanded, _, _, _, _ = _expand_params(tree, params, func_node)

    # Generate IMP body (normalized IR — good for hashing)
    imp_body = python_to_imp(func_node, contract_map=_build_contract_map(tree), tree=tree)
    body_hash = compute_body_hash(func_node, imp_body)

    # Classify and extract contracts
    predicates = _collect_predicates(tree)
    var_types = _infer_var_types(func_node)
    linter_pre = ContractLinter(expanded, "precondition", predicates=predicates)
    linter_post = ContractLinter(expanded, "postcondition", predicates=predicates)
    linter_pre.var_types = var_types
    linter_post.var_types = var_types
    pres_coq: list[str] = []
    posts_coq: list[str] = []
    invs_coq: list[str] = []
    other_asserts: list[str] = []
    callees: set[str] = set()

    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Assert):
            cls = _classify_assert(func_node, stmt)
            linter = linter_pre if cls == "precondition" else linter_post
            lr = linter.lint_expression(stmt.test)
            coq = lr.coq_translation or ""
            if cls == "precondition":
                pres_coq.append(coq)
            elif cls == "postcondition":
                posts_coq.append(coq)
            elif cls == "invariant":
                invs_coq.append(coq)
            else:
                other_asserts.append(coq)
        elif isinstance(stmt, ast.Expr):
            # Walk expression for calls — detect callees
            for n in ast.walk(stmt):
                if isinstance(n, ast.Call):
                    callee = _get_call_name(n)
                    if callee:
                        callees.add(callee)

    # Also walk body for calls (non-assert, non-expr)
    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Call):
            callee = _get_call_name(stmt)
            if callee:
                callees.add(callee)

    pre_coq = " /\\ ".join(pres_coq) or "True"
    post_coq = " /\\ ".join(posts_coq) or "True"
    inv_coq = " /\\ ".join(invs_coq) or "True"
    other_coq = " /\\ ".join(other_asserts) or "True"

    contract_hash = compute_contract_hash(pre_coq, post_coq)
    local_assert_hash = compute_local_assert_hash(inv_coq, other_coq)

    # Compute callee contract hashes from the graph (use current values from source)
    callee_contract_hashes: dict[str, str] = {}
    contract_map = _build_contract_map(tree)
    for callee in callees:
        if callee in contract_map:
            _, cpre, cpost, *_ = contract_map[callee]
            callee_contract_hashes[callee] = compute_contract_hash(cpre, cpost)
        else:
            # Use last known contract hash from graph for external/library callees
            gh = _cache.graph.get_contract_hash(callee)
            if gh:
                callee_contract_hashes[callee] = gh

    return FunctionHashes(
        name=func_name,
        body_hash=body_hash,
        contract_hash=contract_hash,
        local_assert_hash=local_assert_hash,
        callees=sorted(callees),
        callee_contract_hashes=callee_contract_hashes,
    )


def _subst_param_names(coq_expr: str, func_node, full_tree) -> str:
    """Replace bare string/list param names with their length equivalents.

    'name: str' → Coq param is 'name__len: Z', so bare 'name' in unscoped
    contracts must become 'name__len' for Coq to resolve it.
    """
    import ast, re
    result = coq_expr
    for arg, annot in _func_params(func_node):
        if _is_list_param(annot):
            # Replace bare 'arg' with 'arg__len', but not if already 'arg__len'
            result = re.sub(
                rf'\b{re.escape(arg)}\b(?!__len)',
                f'{arg}__len', result
            )
    return result


def _infer_var_types(func_node: ast.FunctionDef) -> dict[str, str]:
    """Infer Python types by walking the function body in order.

    Types: "int", "float", "bool", "str", "dict", "list", "set", or a class name.
    Returns dict of var_name → type_name.
    """
    var_types: dict[str, str] = {}

    def _type_str(annot) -> str | None:
        """Convert type annotation to a Python type string."""
        if annot is None:
            return None
        if isinstance(annot, ast.Name):
            return annot.id  # int, float, bool, str, dict, list, set, or ClassName
        if isinstance(annot, ast.Subscript):
            if isinstance(annot.value, ast.Name):
                base = annot.value.id.lower()
                if base in ("dict", "set"):
                    return "dict" if base == "dict" else "set"
                if base == "list":
                    return "list"
                if base in ("optional", "union"):
                    slice_nodes = annot.slice.elts if isinstance(annot.slice, ast.Tuple) else [annot.slice]
                    if slice_nodes and isinstance(slice_nodes[0], ast.expr):
                        return _type_str(slice_nodes[0])
        return None

    def _call_object(call_node: ast.Call) -> str | None:
        """Extract the object from a method call: x.append() → 'x', self.nodes.get() → None."""
        if isinstance(call_node.func, ast.Attribute):
            val = call_node.func.value
            if isinstance(val, ast.Name):
                return val.id
        return None

    def _expr_type(expr: ast.expr) -> str | None:
        if isinstance(expr, ast.Name):
            return var_types.get(expr.id)
        if isinstance(expr, ast.Dict):
            return "dict"
        if isinstance(expr, ast.List):
            return "list"
        if isinstance(expr, ast.Call):
            name = _get_call_name(expr)
            if name == "dict":
                return "dict"
            if name == "list":
                return "list"
            if name == "set":
                return "set"
        return None

    def _assign(target: ast.expr, expr: ast.expr):
        if isinstance(target, ast.Name):
            t = _expr_type(expr)
            if t:
                var_types[target.id] = t

    # Seed from parameter annotations
    for arg, annot in _func_params(func_node):
        t = _type_str(annot)
        if t:
            var_types[arg] = t

    # Walk body in order
    for stmt in func_node.body:
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                _assign(target, stmt.value)
        elif isinstance(stmt, ast.AnnAssign):
            if isinstance(stmt.target, ast.Name):
                t = _type_str(stmt.annotation) or _expr_type(stmt.value)
                if t:
                    var_types[stmt.target.id] = t
        elif isinstance(stmt, ast.Expr):
            if isinstance(stmt.value, ast.Call):
                name = _get_call_name(stmt.value)
                if name:
                    obj = _call_object(stmt.value)
                    if obj and obj not in var_types:
                        if name.endswith(".append"):
                            var_types[obj] = "list"
                        if name.endswith(".add"):
                            var_types[obj] = "set"
        elif isinstance(stmt, ast.For):
            if isinstance(stmt.iter, ast.Call):
                name = _get_call_name(stmt.iter)
                if name and (name.endswith(".items") or name.endswith(".keys") or name.endswith(".values")):
                    obj = _call_object(stmt.iter)
                    if obj and obj not in var_types:
                        var_types[obj] = "dict"

    return var_types

def tool_check_file(args: dict) -> str:
    """Analyze a Python file and suggest where to add contracts."""
    source = args.get("source", "")
    if not source:
        return "Error: 'source' parameter is required."

    analysis = analyze_file(source)

    lines = [
        f"# Contract Analysis\n",
        f"**{analysis.summary}**\n",
        f"| Function | Pre | Post | Inv | Loops | Purity | Guidance |",
        f"|----------|-----|------|-----|-------|--------|----------|",
    ]

    for f in analysis.functions:
        pre = "✓" if f.has_preconditions else "—"
        post = "✓" if f.has_postconditions else "—"
        inv = "✓" if f.has_invariants else "—"
        loops = "✓" if f.has_loops else "—"
        if f.has_impure_calls:
            purity = f"⚠ {', '.join(f.impure_calls[:2])}"
        else:
            purity = "✓"

        if not f.suggested_adornments:
            guidance = "Fully adorned"
        else:
            guidance = f"{len(f.suggested_adornments)} suggestion(s)"

        lines.append(f"| `{f.name}` | {pre} | {post} | {inv} | {loops} | {purity} | {guidance} |")

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


def _collect_smt_names(ir, name_map: dict[str, str]):
    """Walk IR tree to map SMT variable names to Python-level expressions."""
    if hasattr(ir, 'name') and hasattr(ir, 'kind'):
        kind = ir.kind
        if kind in ('dict_count',):
            # dict_count(name) → smt: name__count → py: f"len({name})"
            name_map[f'{ir.name}__count'] = f'len({ir.name})'
        elif kind == 'len':
            name_map[f'{ir.name}__len'] = f'len({ir.name})'
        elif kind == 'var':
            name_map[ir.name] = ir.name
        elif kind == 'index':
            name_map[f'{ir.name}_at'] = f'{ir.name}[...]'
    if hasattr(ir, 'operands'):
        for o in ir.operands:
            _collect_smt_names(o, name_map)
    if hasattr(ir, 'left'):
        _collect_smt_names(ir.left, name_map)
    if hasattr(ir, 'right'):
        _collect_smt_names(ir.right, name_map)
    if hasattr(ir, 'pred'):
        _collect_smt_names(ir.pred, name_map)


def _extract_ir_vars(ir) -> set[str]:
    """Walk an IR tree and collect variable names from Var nodes."""
    vars_set: set[str] = set()
    def walk(node):
        if node is None:
            return
        if hasattr(node, 'kind'):
            if node.kind == 'var':
                vars_set.add(node.name)
            elif node.kind == 'len':
                vars_set.add(f'{node.name}__len')
            elif node.kind == 'dict_count':
                vars_set.add(f'{node.name}__count')
            elif node.kind == 'dict_len':
                key_str = str(node.key)
                vars_set.add(f'{node.name}_v_{key_str}__len')
        if hasattr(node, 'left'):
            walk(node.left)
        if hasattr(node, 'right'):
            walk(node.right)
        if hasattr(node, 'operands'):
            for o in node.operands:
                walk(o)
        if hasattr(node, 'pred'):
            walk(node.pred)
        if hasattr(node, 'lower'):
            walk(node.lower)
        if hasattr(node, 'upper'):
            walk(node.upper)
    walk(ir)
    return vars_set


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

    # Step 2: Check cache before running verification
    t0 = time.time()
    hashes = _compute_hashes(source, func_name)
    if hashes:
        cached = _cache.lookup(func_name, hashes)
        if cached is not None:
            elapsed = (time.time() - t0) * 1000
            lines = [f"# Verification: `{analysis.name}`\n"]
            method = f" ({cached.proof_method})" if cached.proof_method else ""
            lines.append(f"**✓ Proved ({cached.level.value}){method}** — cached — {elapsed:.0f}ms\n")
            return "\n".join(lines)

    # Step 3: Try verification
    goal = _verify_function(source, func_name, args.get("hint"))
    elapsed = (time.time() - t0) * 1000

    # Step 3b: If Level 1 couldn't close the goal, try LLM oracle
    if goal and not goal.is_proved():
        goal = _try_llm_oracle(source, func_name, goal, args.get("hint"))
        elapsed = (time.time() - t0) * 1000

    # Step 3c: Store result in cache (only if proved)
    if hashes and goal and goal.is_proved():
        _cache.store(hashes, goal)

    # Step 4: Build report
    lines = [f"# Verification: `{analysis.name}`\n"]

    if goal and goal.is_proved():
        method = f" ({goal.proof_method})" if goal.proof_method else ""
        lines.append(f"**✓ Proved ({goal.level.value}){method}** — {elapsed:.0f}ms\n")
        if goal.purity_note:
            lines.append(goal.purity_note + "\n")
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


# ═══════════════════════════════════════════════════════════════════
# Tool: verify-function (cache-aware)
# ═══════════════════════════════════════════════════════════════════

def tool_verify_function(args: dict) -> str:
    """Verify a function with cache support. Thin wrapper around check-function."""
    return tool_check_function(args)


# ═══════════════════════════════════════════════════════════════════
# Tool: verify-changed
# ═══════════════════════════════════════════════════════════════════

def tool_verify_changed(args: dict) -> str:
    """Find changed functions in a source file and re-verify impacted ones.

    Walks all functions in the source, computes hashes, compares against
    the dependency graph, and re-verifies functions whose body, contracts,
    or callee contracts have changed.
    """
    source = args.get("source", "")
    if not source:
        return "Error: 'source' parameter is required."

    try:
        tree = ast.parse(source)
    except SyntaxError as e:
        return f"Error: Syntax error: {e}"

    # Collect all functions
    funcs: dict[str, ast.FunctionDef] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            funcs[node.name] = node

    if not funcs:
        return "No functions found in source."

    # Compute hashes for all functions
    current_hashes: dict[str, FunctionHashes] = {}
    for name in funcs:
        h = _compute_hashes(source, name, tree)
        if h:
            current_hashes[name] = h

    # Find what changed
    to_reverify, body_set, contract_set = _cache.compute_impacted(current_hashes)

    lines = [
        f"# Incremental Verification\n",
        f"**{len(funcs)} functions**, **{len(to_reverify)} need re-verification**\n",
    ]

    if not to_reverify:
        lines.append("All functions up to date. ✓\n")
        return "\n".join(lines)

    # Report what changed and why
    lines.append("## Changes detected\n")
    if body_set:
        lines.append(f"**Body/assert changed** ({len(body_set)}): {', '.join(sorted(body_set))}")
    if contract_set:
        impacted = set()
        for name in contract_set:
            impacted |= set(_cache.graph.get_transitive_callers(name))
        lines.append(f"**Contract changed** ({len(contract_set)}): {', '.join(sorted(contract_set))}")
        if impacted:
            lines.append(f"  → re-verifying callers: {', '.join(sorted(impacted))}")
    lines.append("")

    # Re-verify changed functions
    lines.append("## Results\n")
    lines.append(f"| Function | Status | Level | Method | Note |")
    lines.append(f"|----------|--------|-------|--------|------|")

    t0_total = time.time()
    proved = 0
    failed = 0

    for name in sorted(to_reverify):
        t0 = time.time()
        h = current_hashes.get(name)

        # Check cache first
        if h:
            cached = _cache.lookup(name, h)
            if cached is not None:
                elapsed = (time.time() - t0) * 1000
                lines.append(f"| `{name}` | ✓ | {cached.level.value} | {cached.proof_method or '—'} | cached ({elapsed:.0f}ms) |")
                proved += 1
                continue

        goal = _verify_function(source, name, args.get("hint"))
        if goal and not goal.is_proved():
            goal = _try_llm_oracle(source, name, goal, args.get("hint"))

        elapsed = (time.time() - t0) * 1000

        if goal:
            if h and goal.is_proved():
                _cache.store(h, goal)
            if goal.is_proved():
                proved += 1
                lines.append(f"| `{name}` | ✓ | {goal.level.value} | {goal.proof_method or '—'} | {elapsed:.0f}ms |")
            else:
                failed += 1
                note = goal.suggested_action.value if goal.suggested_action else "unknown"
                lines.append(f"| `{name}` | ✗ | — | — | {note} ({elapsed:.0f}ms) |")
        else:
            failed += 1
            lines.append(f"| `{name}` | ✗ | — | — | verification error ({elapsed:.0f}ms) |")

    total_elapsed = (time.time() - t0_total) * 1000
    lines.append("")
    lines.append(f"**{proved} proved, {failed} failed** — {total_elapsed:.0f}ms total")
    lines.append("")

    # Guidance for remaining failures
    if failed > 0:
        lines.append("## Unproved\n")
        lines.append("Re-run `verify.changed` after adding missing contracts or fixing code.")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Tool: verify-impacted
# ═══════════════════════════════════════════════════════════════════

def tool_verify_impacted(args: dict) -> str:
    """Show which functions would be re-verified without running verification.

    Dry-run: computes hashes and shows the impact of current changes.
    """
    source = args.get("source", "")
    if not source:
        return "Error: 'source' parameter is required."

    try:
        tree = ast.parse(source)
    except SyntaxError as e:
        return f"Error: Syntax error: {e}"

    funcs: dict[str, ast.FunctionDef] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            funcs[node.name] = node

    if not funcs:
        return "No functions found in source."

    current_hashes: dict[str, FunctionHashes] = {}
    for name in funcs:
        h = _compute_hashes(source, name, tree)
        if h:
            current_hashes[name] = h

    to_reverify, body_set, contract_set = _cache.compute_impacted(current_hashes)

    lines = [f"# Impact Analysis\n", f"**{len(funcs)} functions** in source\n"]

    # What changed
    changed = body_set | contract_set
    if not changed:
        lines.append("No changes detected. All functions up to date. ✓\n")
        return "\n".join(lines)

    lines.append("## Changed\n")
    for name in sorted(changed):
        reason = []
        if name in body_set:
            reason.append("body")
        if name in contract_set:
            reason.append("contract")
        lines.append(f"- `{name}` ({', '.join(reason)})")

    lines.append("")
    lines.append("## Will re-verify\n")
    for name in sorted(to_reverify):
        if name in changed:
            lines.append(f"- `{name}` (direct change)")
        else:
            # Find which changed function triggered this
            triggered_by = []
            for changed_name in contract_set:
                if name in _cache.graph.get_transitive_callers(changed_name):
                    triggered_by.append(changed_name)
            triggered = ", ".join(triggered_by) if triggered_by else "contract propagation"
            lines.append(f"- `{name}` (caller of {triggered})")

    lines.append("")
    lines.append(f"**{len(to_reverify)}** of {len(funcs)} functions would be re-verified.")
    lines.append(f"Run `verify.changed` to execute.")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Tool: explain-cache
# ═══════════════════════════════════════════════════════════════════

def tool_explain_cache(args: dict) -> str:
    """Explain the cache state for a function."""
    source: str = args.get("source", "")
    func_name: str | None = args.get("function_name", "")
    if not source or not func_name:
        return "Error: 'source' and 'function_name' parameters are required."

    try:
        import ast as _ast
        tree = _ast.parse(source)
    except SyntaxError as e:
        return f"Error: syntax error — {e}"

    func_node = None
    for node in _ast.walk(tree):
        if isinstance(node, _ast.FunctionDef) and node.name == func_name:
            func_node = node
            break
    if func_node is None:
        return f"Error: function '{func_name}' not found in source."

    params = [name for name, _ in _func_params(func_node)]
    expanded, _, _, _, _ = _expand_params(tree, params, func_node)
    contract_map = _build_contract_map(tree)
    imp_body = python_to_imp(func_node, contract_map=contract_map, tree=tree)
    body_hash = compute_body_hash(func_node, imp_body)

    linter_pre = ContractLinter(expanded, "precondition")
    linter_post = ContractLinter(expanded, "postcondition")
    pres_coq: list[str] = []
    posts_coq: list[str] = []
    for stmt in func_node.body:
        if isinstance(stmt, _ast.Assert):
            cls = _classify_assert(func_node, stmt)
            linter = linter_pre if cls == "precondition" else linter_post
            lr = linter.lint_expression(stmt.test)
            if lr.coq_translation:
                if cls == "precondition":
                    pres_coq.append(lr.coq_translation)
                elif cls == "postcondition":
                    posts_coq.append(lr.coq_translation)
    contract_hash = compute_contract_hash(
        " /\\ ".join(pres_coq) or "True",
        " /\\ ".join(posts_coq) or "True",
    )

    return (f"## Cache state for `{func_name}`\n\n"
            f"Body hash: `{body_hash[:24]}...`\n"
            f"Contract hash: `{contract_hash[:24]}...`\n")


def tool_frame_report(args: dict) -> str:
    """Report contracts and frame conditions for functions."""
    import ast as _ast
    from .stub_loader import get_stub_loader

    source: str = args.get("source", "")
    func_name: str | None = args.get("function_name")

    if not source:
        return "Error: 'source' parameter is required."

    tree = _ast.parse(source)

    targets: list[_ast.FunctionDef] = []
    for node in _ast.walk(tree):
        if isinstance(node, _ast.FunctionDef):
            if func_name is None or node.name == func_name:
                targets.append(node)

    if not targets:
        name_hint = f" '{func_name}'" if func_name else ""
        return f"Error: no function{name_hint} found in source."

    stub_loader = get_stub_loader()
    contract_map = _build_contract_map(tree)
    expanded_all, _, _, _, _ = _expand_params(tree, [], None)

    lines: list[str] = []
    lines.append(f"# Contract & Frame Report{f' for `{func_name}`' if func_name else ''}")
    lines.append("")

    for fn in targets:
        # Extract pre/post/inv from asserts
        pres: list[str] = []
        posts: list[str] = []
        invs: list[str] = []
        for stmt in fn.body:
            if isinstance(stmt, _ast.Assert):
                cls = _classify_assert(fn, stmt)
                src = _ast.get_source_segment(source, stmt) or _ast.unparse(stmt)
                if cls == "precondition":
                    pres.append(src)
                elif cls == "postcondition":
                    posts.append(src)
                elif cls == "invariant":
                    invs.append(src)

        # Frame: reads/writes from AST
        params = {arg.arg for arg in fn.args.args}
        reads: set[str] = set()
        writes: set[str] = set()
        callee_effects: list[str] = []

        class Visitor(_ast.NodeVisitor):
            def visit_FunctionDef(self, node):
                # visit body but don't recurse into nested functions
                for stmt in node.body:
                    if not isinstance(stmt, _ast.FunctionDef):
                        self.visit(stmt)

            def visit_Assign(self, node):
                for target in node.targets:
                    if isinstance(target, _ast.Name):
                        writes.add(target.id)
                    elif isinstance(target, _ast.Tuple):
                        for elt in target.elts:
                            if isinstance(elt, _ast.Name):
                                writes.add(elt.id)
                self.generic_visit(node)

            def visit_AugAssign(self, node):
                if isinstance(node.target, _ast.Name):
                    writes.add(node.target.id)
                self.generic_visit(node)

            def visit_AnnAssign(self, node):
                if isinstance(node.target, _ast.Name):
                    writes.add(node.target.id)
                # skip annotation — don't descend into type hints

            def visit_arg(self, node):
                pass  # skip parameter type annotations

            def visit_Name(self, node):
                if isinstance(node.ctx, _ast.Load) and node.id not in writes:
                    reads.add(node.id)
                self.generic_visit(node)

            def visit_Call(self, node):
                # collect callee frame effects but don't count callee name as a write
                if isinstance(node.func, _ast.Name):
                    callee = node.func.id
                    if callee in contract_map:
                        _, _, _, c_reads, c_writes = contract_map[callee]
                        if c_reads or c_writes:
                            callee_effects.append(
                                f"  ↳ `{callee}()` reads {{{', '.join(c_reads) or '—'}}} "
                                f"writes {{{', '.join(c_writes) or '—'}}}"
                            )
                    elif callee in stub_loader.known_functions:
                        sc = stub_loader.get_contract_info(callee)
                        if sc:
                            callee_effects.append(
                                f"  ↳ `{callee}()` reads {{{', '.join(sc.reads) or '—'}}} "
                                f"writes {{{', '.join(sc.writes) or '—'}}}"
                            )
                # visit call args (but not the callee name)
                for arg in node.args:
                    self.visit(arg)
                for kw in node.keywords:
                    self.visit(kw.value)

        Visitor().visit(fn)
        reads -= writes  # variables both read and written are writes

        # Contract map info
        cm_entry = contract_map.get(fn.name)
        cm_reads: list[str] = []
        cm_writes: list[str] = []
        if cm_entry:
            _, _, _, cm_reads, cm_writes = cm_entry

        lines.append(f"## `{fn.name}`")
        lines.append("")

        if pres:
            lines.append("### Preconditions")
            for p in pres:
                lines.append(f"  {p}")
            lines.append("")
        else:
            lines.append("### Preconditions  *(none)*")
            lines.append("")

        if posts:
            lines.append("### Postconditions")
            for p in posts:
                lines.append(f"  {p}")
            lines.append("")
        else:
            lines.append("### Postconditions  *(none)*")
            lines.append("")

        if invs:
            lines.append("### Loop Invariants")
            for inv in invs:
                lines.append(f"  {inv}")
            lines.append("")

        lines.append("### Frame")
        r = ', '.join(sorted(reads - params)) or '—'
        w = ', '.join(sorted(writes)) or '—'
        lines.append(f"  reads:  {{{r}}}")
        lines.append(f"  writes: {{{w}}}")
        if cm_reads or cm_writes:
            lines.append(f"  declared (stub): reads {{{', '.join(cm_reads) or '—'}}}, "
                         f"writes {{{', '.join(cm_writes) or '—'}}}")
        lines.append("")

        if callee_effects:
            lines.append("### Callee Effects")
            for ce in callee_effects:
                lines.append(ce)
            lines.append("")

    return "\n".join(lines)
    """Explain the cache state for a function."""
    source = args.get("source", "")
    func_name = args.get("function_name", "")
    if not source or not func_name:
        return "Error: 'source' and 'function_name' are required."

    try:
        tree = ast.parse(source)
    except SyntaxError as e:
        return f"Error: Syntax error: {e}"

    h = _compute_hashes(source, func_name, tree)
    if h is None:
        return f"Error: Function '{func_name}' not found."

    return _cache.explain(func_name, h)


def _compute_purity_note(tree, func_node, imp_body: str) -> str:
    """Generate a short purity/frame note for the verification result."""
    import ast
    from .purity_analyzer import analyze_purity, generate_frame_conditions

    param_names = [name for name, _ in _func_params(func_node)]
    _, class_fields, _, _, _ = _expand_params(tree, param_names, func_node)
    contract_map = _build_contract_map(tree)
    purity = analyze_purity(func_node, tree, contract_map, class_fields)

    if not purity.is_pure:
        calls = list(dict.fromkeys(purity.impure_calls))
        return f"⚠ **Black hole**: impure call{'s' if len(calls) > 1 else ''} `{', '.join(calls[:3])}` — frame conditions not verified"

    if class_fields:
        post_nodes = [n for n in ast.walk(func_node)
                      if isinstance(n, ast.Assert)
                      and _classify_assert(func_node, n) == "postcondition"]
        frames = generate_frame_conditions(func_node, tree, class_fields, post_nodes)
        if frames:
            field_names = [fc.split('"')[1] for fc in frames]
            return f"🔒 **Frame**: {len(frames)} field{'s' if len(frames) > 1 else ''} proved unchanged: `{'`, `'.join(field_names)}`"

    return ""


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
    params = [name for name, _ in _func_params(func_node)]
    expanded, class_fields, _, init_state, record_section = _expand_params(tree, params, func_node)

    old_err = _check_old_captures(func_node, params)
    if old_err:
        return GoalStatus(name=func_name, goal_statement="",
                          level=ProofLevel.UNPROVED,
                          error_detail=old_err,
                          suggested_action=Action.REFACTOR,
                          suggestion_text=old_err)

    predicates = _collect_predicates(tree)

    # Lint with expanded params (so result, account.balance are scoped correctly)
    var_types = _infer_var_types(func_node)
    linter_pre = ContractLinter(expanded, "precondition", predicates=predicates)
    linter_post = ContractLinter(expanded, "postcondition", predicates=predicates)
    linter_pre.var_types = var_types
    linter_post.var_types = var_types
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
    imp_body = python_to_imp(func_node, contract_map=_build_contract_map(tree), tree=tree)
    coq_source = _generate_coq(func_node, lint_results, imp_body, tree, hint)

    # Write temp file and compile
    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".v", delete=False, prefix=f"mcp_{func_name}_",
        ) as f:
            f.write(coq_source)
            tmp_path = Path(f.name)

        coq_timeout = 300 if hint == "hammer" else 180
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

            purity_note = _compute_purity_note(tree, func_node, imp_body)

            return GoalStatus(name=func_name,
                            goal_statement=f"wp {func_name}_body ...",
                            level=ProofLevel.LEVEL1_LTAC,
                            proof_method=method,
                            purity_note=purity_note)

        error = result.stderr + result.stdout
        # Try SMT counterexample extraction for the postcondition
        ce_hint = ""
        ce_dict: dict[str, int] = {}
        if result.returncode != 0:
            from .smt_export import _expr_to_smt, _extract_vars
            post_irs = [r.lint_result.ir for r in lint_results 
                       if r.classification == "postcondition" and r.lint_result.ir]
            pre_irs = [r.lint_result.ir for r in lint_results
                      if r.classification == "precondition" and r.lint_result.ir]
            if post_irs:
                post_smt = " and ".join(ir.to_smt() for ir in post_irs)
                pre_smt = " and ".join(ir.to_smt() for ir in pre_irs) if pre_irs else None
                all_smt = f"(and {pre_smt} (not {post_smt}))" if pre_smt else f"(not {post_smt})"
                lines = ['(set-logic QF_NIA)', '(set-option :produce-models true)']
                vars_set = _extract_vars(all_smt)
                for v in sorted(vars_set):
                    lines.append(f'(declare-fun {v} () Int)')
                lines.append(f'(assert {all_smt})')
                lines.append('(check-sat)')
                lines.append('(get-model)')
                with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as sf:
                    sf.write('\n'.join(lines))
                    smt_tmp = Path(sf.name)
                smt_result = subprocess.run(['cvc4', str(smt_tmp)], capture_output=True, text=True, timeout=10)
                if 'sat' in smt_result.stdout.lower():
                    # Map SMT names back to human-readable Python expressions
                    name_map: dict[str, str] = {}
                    for r in lint_results:
                        if r.lint_result.ir:
                            _collect_smt_names(r.lint_result.ir, name_map)
                    ce_hint = "SMT counterexample found for postcondition:\n"
                    for line in smt_result.stdout.splitlines():
                        line = line.strip()
                        if line.startswith('(define-fun') and not line.startswith('(define-fun-sort'):
                            parts = line.split()
                            if len(parts) >= 3:
                                smt_name = parts[1]
                                py_name = name_map.get(smt_name, smt_name)
                                val = parts[-1].rstrip(')')
                                try:
                                    ce_dict[py_name] = int(val)
                                    ce_hint += f"  {py_name} = {val}\n"
                                except ValueError:
                                    pass
                    # Add source position of postcondition asserts that failed
                    post_asserts = [r for r in lint_results if r.classification == "postcondition"]
                    if post_asserts:
                        ce_hint += f"\nThe following postcondition(s) failed:\n"
                        for r in post_asserts:
                            src = ast.unparse(r.node) if hasattr(ast, 'unparse') else str(r.node)
                            ce_hint += f"  line {r.lineno}: {src}\n"
                smt_tmp.unlink(missing_ok=True)
        # Check for SMT counterexample in the generated source (VCG)
            import re
            m = re.search(r'SMT counterexample: (.*?) \*', coq_source)
            if m:
                ce_str = m.group(1).strip()
                ce_hint = f"\n\nSMT counterexample found: {ce_str}\nStrengthen the loop invariant to rule out these values."
                for pair in ce_str.split(","):
                    pair = pair.strip()
                    if "=" in pair:
                        k, v = pair.split("=", 1)
                        try:
                            ce_dict[k.strip()] = int(v.strip())
                        except ValueError:
                            pass
        return GoalStatus(name=func_name,
                        goal_statement=f"wp {func_name}_body ...",
                        level=ProofLevel.COUNTEREXAMPLE if ce_dict else ProofLevel.UNPROVED,
                        counterexample=ce_dict,
                        error_detail=error[-800:] + ce_hint,
                        suggested_action=Action.PROPERTY_FALSE if ce_dict else Action.RETRY_LLM,
                        suggestion_text=error[:200],
                        proof_method="wp_reduce")
    finally:
        if tmp_path:
            tmp_path.unlink(missing_ok=True)


def _try_llm_oracle(source: str, func_name: str, goal: GoalStatus, hint: str | None = None) -> GoalStatus:
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

    params = [name for name, _ in _func_params(func_node)]
    expanded, _, params_coq, _, _ = _expand_params(tree, params, func_node)
    imp_body = python_to_imp(func_node, contract_map=_build_contract_map(tree), tree=tree)

    # Generate full Coq source
    var_types2 = _infer_var_types(func_node)
    linter_pre = ContractLinter(expanded, "precondition")
    linter_post = ContractLinter(expanded, "postcondition")
    linter_pre.var_types = var_types2
    linter_post.var_types = var_types2
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
    # Pass hint through to oracle for thinking-time control
    if hint and hint != "hammer":
        llm_hint += f"\n\nTake your time thinking. {hint}\n"

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

    # Check if at function start (only direct children of the function body)
    seen_code = False
    if assert_node in body:
        idx = body.index(assert_node)
        for i, s in enumerate(body[:idx + 1]):
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
        for arg, annot in _func_params(func_node):
            coq_type = _py_type_to_coq(annot)
            param_types[arg] = coq_type
            if _is_list_param(annot):
                list_params.add(arg)

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
            # List/vararg parameters: expose the length as a Coq parameter
            len_var = f"{p}__len"
            expanded.append(len_var)
            parts.append(f"({len_var} : Z)")
            init_state = f'(upd {init_state} "{p}._len"%string (VZ {len_var}))'
        elif func_node and func_node.args.vararg and p == func_node.args.vararg.arg:
            # *args (vararg) — always treated as list
            len_var = f"{p}__len"
            expanded.append(len_var)
            parts.append(f"({len_var} : Z)")
            init_state = f'(upd {init_state} "{p}._len"%string (VZ {len_var}))'
        elif cls_name:
            for f in class_fields[cls_name]:
                expanded.append(f"{p}_{f}")
                parts.append(f"({p}_{f} : Z)")
        else:
            expanded.append(p)
            parts.append(f"({p} : {coq_type})")
            init_state = f'(upd {init_state} "{p}"%string (VZ {p}))'

    for p in params:
        cls_name = next((c for c in class_fields if c.lower() == p.lower()), None)
        if cls_name:
            for f in class_fields[cls_name]:
                init_state = f'(store_field "{p}"%string "{f}"%string (VZ {p}_{f}) {init_state})'

    return expanded, class_fields, " ".join(parts), init_state, record_section


def _py_type_to_coq(annotation) -> str:
    """Map Python type annotation AST node to a Coq type string."""
    if annotation is None:
        return "Z"
    type_map = {"int": "Z", "float": "Z", "bool": "Z"}
    if isinstance(annotation, ast.Name):
        if annotation.id == "str":
            return "list"
        return type_map.get(annotation.id, "Z")
    if isinstance(annotation, ast.Subscript):
        if isinstance(annotation.value, ast.Name):
            base = annotation.value.id
            if base == "list":
                return "list"
            if base in ("Optional", "Union"):
                # Extract inner type from Optional[T] or Union[T, ...]
                args = annotation.slice if isinstance(annotation.slice, ast.Tuple) else [annotation.slice]
                if args and isinstance(args[0], ast.expr):
                    return _py_type_to_coq(args[0])
            if base in ("dict", "Dict"):
                return "Z"  # opaque dict → no Coq dict type
    if isinstance(annotation, ast.Attribute):
        parts = []
        n = annotation
        while isinstance(n, ast.Attribute):
            parts.append(n.attr)
            n = n.value
        if isinstance(n, ast.Name):
            parts.append(n.id)
        full = ".".join(reversed(parts))
        full_lower = full.lower()
        for name, coq in type_map.items():
            if name in full_lower:
                return coq
        if "str" in full_lower:
            return "list"
        if "list" in full_lower:
            return "list"
        if "dict" in full_lower:
            return "Z"  # opaque dict
        if "optional" in full_lower:
            return "Z"
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


def _check_old_captures(func_node, params: list[str]) -> str:
    """Check *_old variables are only used in captures and asserts.

    Convention: `x_old = expr` at function start captures pre-state value,
    where `expr` is either a parameter name or `param.field`.
    _old variables may only appear in:
      - The initial capture assignment
      - `assert` statements (contracts)
    Any other use (mutation, computation, conditional) is an error.
    Returns error message or "".
    """
    import ast
    param_set = set(params)
    captured: dict[str, int] = {}

    for stmt in func_node.body:
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Name) and target.id.endswith("_old"):
                    name = target.id
                    if name in captured:
                        return (f"Line {stmt.lineno}: '{name}' already captured "
                                f"as old-value at line {captured[name]}")
                    if _is_valid_capture(stmt.value, param_set):
                        captured[name] = stmt.lineno
                    else:
                        return (f"Line {stmt.lineno}: '{name}' must capture a "
                                f"parameter or parameter field: `{name} = param` "
                                f"or `{name} = param.field`")
        elif isinstance(stmt, ast.Assert):
            continue
        elif isinstance(stmt, (ast.Expr, ast.Return)):
            continue
        else:
            for n in ast.walk(stmt):
                if isinstance(n, ast.Name) and n.id in captured:
                    return (f"Line {stmt.lineno}: '{n.id}' is an old-value "
                            f"capture (line {captured[n.id]}) and must only "
                            f"appear in `assert` statements")

    for stmt in func_node.body:
        if isinstance(stmt, ast.Assign) and not any(
            isinstance(t, ast.Name) and t.id.endswith("_old") and t.id in captured
            for t in stmt.targets
        ):
            for n in ast.walk(stmt.value):
                if isinstance(n, ast.Name) and n.id in captured:
                    return (f"Line {stmt.lineno}: '{n.id}' is an old-value "
                            f"capture (line {captured[n.id]}) and must only "
                            f"appear in `assert` statements")
    return ""


def _is_valid_capture(node: ast.expr, param_set: set[str]) -> bool:
    """Check if a capture expression is valid: param or param.field."""
    if isinstance(node, ast.Name) and node.id in param_set:
        return True
    if isinstance(node, ast.Attribute):
        base = _get_attribute_base(node)
        return base is not None and base in param_set
    return False


def _get_attribute_base(node: ast.Attribute) -> str | None:
    """Extract the base variable from an attribute chain: a.b.c → 'a'."""
    if isinstance(node.value, ast.Name):
        return node.value.id
    if isinstance(node.value, ast.Attribute):
        return _get_attribute_base(node.value)
    return None



def _collect_predicates(tree) -> dict[str, tuple[list[str], "ast.expr | None"]]:
    """Find user-defined predicate functions in a file.

    Returns dict of name → (param_names, return_expression).
    return_expression is None for multi-statement/looping predicates.
    """
    import ast
    predicates: dict[str, tuple[list[str], ast.expr | None]] = {}
    for node in ast.iter_child_nodes(tree):
        if not isinstance(node, ast.FunctionDef):
            continue
        params = [p.arg for p in node.args.args]
        param_set = set(params)
        def _mutates(n):
            if isinstance(n, ast.Assign):
                for t in n.targets:
                    if isinstance(t, ast.Name) and (t.id == "result" or t.id in param_set):
                        return True
            if isinstance(n, ast.AugAssign):
                if isinstance(n.target, ast.Name) and (n.target.id == "result" or n.target.id in param_set):
                    return True
            return False
        if any(_mutates(n) for n in ast.walk(node)):
            continue
        non_doc = [s for s in node.body
                   if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant))]
        if len(non_doc) == 1 and isinstance(non_doc[0], ast.Return) and non_doc[0].value:
            predicates[node.name] = (params, non_doc[0].value)
        else:
            predicates[node.name] = (params, None)
    return predicates


def _build_contract_map(tree) -> dict[str, tuple[list[str], str, str, list[str], list[str]]]:
    """Build a map of function_name -> (param_names, pre_coq, post_coq, reads, writes) from AST.

    Contracts:
      post: keys are function names, values are (params, pre, post, reads, writes) tuples
            for functions that have pre/post assertions or stub contracts.
    """
    import ast
    from .contract_linter import ContractLinter

    def _add_function_to_map(fn_node: ast.FunctionDef, cmap: dict):
        name = fn_node.name
        param_names = [p[0] for p in _func_params(fn_node)]
        linter_pre = ContractLinter(param_names, "precondition")
        linter_post = ContractLinter(param_names, "postcondition")
        pres = []
        posts = []
        for stmt in fn_node.body:
            if isinstance(stmt, ast.Assert):
                cls = _classify_assert(fn_node, stmt)
                if cls == "precondition":
                    lr = linter_pre.lint_expression(stmt.test)
                    if lr.is_valid and lr.coq_translation:
                        pres.append(lr.coq_translation)
                elif cls == "postcondition":
                    lr = linter_post.lint_expression(stmt.test)
                    if lr.is_valid and lr.coq_translation:
                        posts.append(lr.coq_translation)
        pre_coq = " /\\ ".join(pres) or "True"
        post_coq = " /\\ ".join(posts) or "True"
        # Include if there are ANY asserts (even True) — caller needs CCall target
        if pres or posts or pre_coq != "True" or post_coq != "True":
            cmap[name] = (param_names, pre_coq, post_coq, [], [])

    contract_map: dict[str, tuple[list[str], str, str, list[str], list[str]]] = {}
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.FunctionDef):
            _add_function_to_map(node, contract_map)
        elif isinstance(node, ast.ClassDef):
            for class_child in ast.iter_child_nodes(node):
                if isinstance(class_child, ast.FunctionDef):
                    _add_function_to_map(class_child, contract_map)

    # Merge in library stub contracts
    # Source code takes precedence for pre/post, but stub provides
    # frame info (reads/writes) and any contracts missing from source.
    from .stub_loader import get_stub_loader
    for name in get_stub_loader().known_functions:
        sc = get_stub_loader().get_contract_info(name)
        if sc is None:
            continue
        params, pre, post = get_stub_loader().get_contract(name) or (sc.params, "True", "True")
        reads = sc.reads
        writes = sc.writes
        if name not in contract_map:
            contract_map[name] = (params, pre, post, reads, writes)
        else:
            src_p, src_pre, src_post, src_reads, src_writes = contract_map[name]
            merged_pre = src_pre if src_pre != "True" else pre
            merged_post = src_post if src_post != "True" else post
            merged_reads = list(set(src_reads) | set(reads))
            merged_writes = list(set(src_writes) | set(writes))
            contract_map[name] = (src_p, merged_pre, merged_post, merged_reads, merged_writes)

    return contract_map


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


COQ_KEYWORDS = {
    "end", "match", "fix", "struct", "cofix", "with", "let", "in",
    "if", "then", "else", "fun", "forall", "exists", "as", "at",
    "return", "module", "type", "where", "when", "using", "by",
}


def _coq_safe_name(name: str) -> str:
    """Rename Python variables that collide with Coq keywords."""
    if name.lower() in COQ_KEYWORDS:
        return f"{name}_var"
    return name


def _coq_safe_id(name: str) -> str:
    """Sanitize a name for use as a Coq identifier (no parens, ops, etc)."""
    return name.replace("(", "_L_").replace(")", "_R_").replace(" + ", "_plus_") \
               .replace(" - ", "_minus_").replace("*", "_star_").replace("/", "_div_") \
               .replace("-", "_minus_").replace("+", "_plus_").replace(" ", "_")


def _find_closing_paren(s: str, start: int) -> int:
    """Find the matching ')' for the opening '(' at position `start`."""
    depth = 0
    for i in range(start, len(s)):
        if s[i] == '(':
            depth += 1
        elif s[i] == ')':
            depth -= 1
            if depth == 0:
                return i
    return -1


def _unscope_vars(coq_expr: str) -> str:
    """Convert state lookups back to bare Coq variables for VCG.
    s \"x\"%string → x, s \"a.b\"%string → a_b."""
    import re
    result = re.sub(r's "([^"]+)"%string', lambda m: _coq_safe_name(m.group(1)), coq_expr)
    result = result.replace('.', '_')
    return result


def _vcg_result_scaffold(imp_body: str) -> tuple[str, set[str]]:
    """Extract the post-loop result assignment from the IMP body.
    Uses depth-aware paren matching (no regex on nested structures).
    Returns (scaffold_string, set_of_referenced_variable_names).
    """
    needle = '(CAss "result"%string '
    pos = imp_body.rfind(needle)
    if pos == -1:
        return "", set()
    start = pos + len(needle)
    depth = 0
    idx = start
    while idx < len(imp_body):
        if imp_body[idx] == '(':
            depth += 1
        elif imp_body[idx] == ')':
            depth -= 1
            if depth == 0:
                aexp_str = imp_body[start:idx+1]
                if 'AVar "result"' in aexp_str and '(' not in aexp_str[aexp_str.index('AVar "result"')+13:]:
                    prev = imp_body.rfind(needle, 0, pos)
                    if prev == -1:
                        return "", set()
                    start2 = prev + len(needle)
                    depth2 = 0
                    idx2 = start2
                    while idx2 < len(imp_body):
                        if imp_body[idx2] == '(': depth2 += 1
                        elif imp_body[idx2] == ')':
                            depth2 -= 1
                            if depth2 == 0:
                                aexp_str = imp_body[start2:idx2+1]
                                break
                        idx2 += 1
                coq_val, scaffold_vars = _imp_aexp_to_coq_z_with_vars(aexp_str)
                if not coq_val:
                    return "", set()
                return f"result = {coq_val} ->\n  ", scaffold_vars
        idx += 1
    return "", set()


def _imp_aexp_to_coq_z_with_vars(aexp_str: str) -> tuple[str, set[str]]:
    """Like _imp_aexp_to_coq_z but also returns referenced variable names."""
    aexp_str = aexp_str.strip()
    vars_found: set[str] = set()

    if aexp_str.startswith('(AVar "'):
        end = aexp_str.index('"%string)')
        name = aexp_str[7:end]
        safe = _coq_safe_name(name)
        vars_found.add(safe)
        return safe, vars_found

    if aexp_str.startswith('(ALen "'):
        end = aexp_str.index('"%string)')
        name = aexp_str[7:end]
        safe = f"{_coq_safe_name(name)}__len"
        vars_found.add(safe)
        return safe, vars_found

    if aexp_str.startswith('(ANum '):
        end = aexp_str.index(')')
        return aexp_str[6:end], vars_found

    op_end = aexp_str.index(' ', 1)
    op = aexp_str[1:op_end]
    rest = aexp_str[op_end+1:]

    left_end = _find_closing_paren(rest, 0)
    left_str = rest[:left_end+1]

    right_start = left_end + 1
    while right_start < len(rest) and rest[right_start] == ' ':
        right_start += 1
    right_str = rest[right_start:-1]

    left_val, left_vars = _imp_aexp_to_coq_z_with_vars(left_str)
    right_val, right_vars = _imp_aexp_to_coq_z_with_vars(right_str)
    if not left_val or not right_val:
        return "", vars_found
    vars_found |= left_vars | right_vars

    if op == "APlus":
        return f"({left_val} + {right_val})", vars_found
    if op == "AMinus":
        return f"({left_val} - {right_val})", vars_found
    return "", vars_found


def _imp_aexp_to_coq_z(aexp_str: str) -> str:
    """Convert an IMP aexp string to an unscoped Coq Z expression.
    Uses paren-depth parsing (no regex on nested structures).
    (ALen "xs"%string) → xs__len
    (AVar "x"%string) → x
    (ANum 5) → 5
    (APlus a b) → (a + b)
    (AMinus a b) → (a - b)
    """
    aexp_str = aexp_str.strip()

    if aexp_str.startswith('(AVar "'):
        end = aexp_str.index('"%string)')
        name = aexp_str[7:end]
        return _coq_safe_name(name)

    if aexp_str.startswith('(ALen "'):
        end = aexp_str.index('"%string)')
        name = aexp_str[7:end]
        return f"{_coq_safe_name(name)}__len"

    if aexp_str.startswith('(ANum '):
        end = aexp_str.index(')')
        return aexp_str[6:end]

    op_end = aexp_str.index(' ', 1)
    op = aexp_str[1:op_end]
    rest = aexp_str[op_end+1:]

    left_end = _find_closing_paren(rest, 0)
    left_str = rest[:left_end+1]

    right_start = left_end + 1
    while right_start < len(rest) and rest[right_start] == ' ':
        right_start += 1
    right_str = rest[right_start:-1]

    left = _imp_aexp_to_coq_z(left_str)
    right = _imp_aexp_to_coq_z(right_str)
    if not left or not right:
        return ""

    if op == "APlus":
        return f"({left} + {right})"
    if op == "AMinus":
        return f"({left} - {right})"
    return ""


def _loop_exit_condition(loop_node) -> str:
    """Generate VCG exit condition for a specific loop node."""
    import ast
    if isinstance(loop_node, ast.While):
        return _py_cond_to_vcg_exit(loop_node.test)
    if isinstance(loop_node, ast.For):
        if (isinstance(loop_node.iter, ast.Call)
            and isinstance(loop_node.iter.func, ast.Name)
            and loop_node.iter.func.id == "range"
            and loop_node.iter.args):
            limit = loop_node.iter.args[-1]
            target_str = loop_node.target.id if isinstance(loop_node.target, ast.Name) else "i"
            limit_str = _py_expr_to_coq_var(limit)
            return f"Z.leb ({target_str} + 1) {limit_str} = false"
    return "Z.leb i n = false"


def _loops_with_invariants(func_node, lint_results):
    """Find the last while/for loop containing invariant assertions.
    For nested loops, picks the outermost. For sequential, picks the last.
    Returns list with at most one element.
    """
    import ast
    inv_nodes = set()
    for r in lint_results:
        if r.classification == "invariant":
            inv_nodes.add(id(r.node))
    if not inv_nodes:
        return []
    # Find all loops containing invariants, pick the outermost one
    candidates = []
    for node in ast.walk(func_node):
        if not isinstance(node, (ast.While, ast.For)):
            continue
        for body_node in ast.walk(node):
            if id(body_node) in inv_nodes:
                loop_invs = [r for r in lint_results
                           if r.classification == "invariant" and
                           any(body_node is r.node for body_node in ast.walk(node))]
                candidates.append((node, loop_invs))
                break
    if not candidates:
        return []
    if len(candidates) == 1:
        return candidates
    # If loops are nested, pick the outermost (first in walk order).
    # Otherwise (sequential), pick the last (closest to postcondition).
    loops = [c[0] for c in candidates]
    # Check if the first loop contains any other candidate loop
    if any(loop in ast.walk(loops[0]) for loop in loops[1:]):
        return [candidates[0]]  # nested → outermost
    return [candidates[-1]]  # sequential → last


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
    r"""Translate a Python comparison to a VCG exit condition.

    Exit means the condition evaluated to false.
    `i < n`  → `Z.leb (i + 1) n = false`
    `i <= n` → `Z.leb i n = false`
    `a and b` → `(exit a) \/ (exit b)`
    `a or b`  → `(exit a) /\ (exit b)`
    """
    import ast
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
        parts = [_py_cond_to_vcg_exit(v) for v in test.values]
        return " \\/ ".join(f"({p})" for p in parts)
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.Or):
        parts = [_py_cond_to_vcg_exit(v) for v in test.values]
        return " /\\ ".join(f"({p})" for p in parts)
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


def _func_params(func_node) -> list[tuple[str, ast.expr | None]]:
    """Extract all named parameters from a function definition.

    Returns list of (name, annotation) for positional-only, regular,
    keyword-only args, and *args (vararg). Skips **kwargs.
    """
    import ast
    params = []
    for a in func_node.args.args:
        params.append((a.arg, a.annotation))
    for a in func_node.args.posonlyargs:
        params.append((a.arg, a.annotation))
    for a in func_node.args.kwonlyargs:
        params.append((a.arg, a.annotation))
    if func_node.args.vararg:
        # *args → expose as list parameter with _len
        params.append((func_node.args.vararg.arg, func_node.args.vararg.annotation))
    return params


def _py_expr_to_coq_var(node: ast.expr) -> str:
    """Convert a simple Python expression to a Coq variable name."""
    import ast
    if isinstance(node, ast.Name):
        return _coq_safe_name(node.id)
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return str(node.value)
    if isinstance(node, ast.Call):
        name = _get_call_name(node)
        if name == "len" and node.args and isinstance(node.args[0], ast.Name):
            return f"{_coq_safe_name(node.args[0].id)}__len"
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Sub):
        left = _py_expr_to_coq_var(node.left)
        right = _py_expr_to_coq_var(node.right)
        if left != "?" and right != "?":
            return f"({left} - {right})"
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left = _py_expr_to_coq_var(node.left)
        right = _py_expr_to_coq_var(node.right)
        if left != "?" and right != "?":
            return f"({left} + {right})"
    if isinstance(node, ast.Subscript):
        base = _py_expr_to_coq_var(node.value)
        idx = _py_expr_to_coq_var(node.slice)
        if base != "?" and idx != "?":
            return _coq_safe_id(f"{base}_at_{idx}")
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

    inv = Logical(op="and", operands=list(inv_irs)) if len(inv_irs) > 1 else inv_irs[0]
    post = Logical(op="and", operands=list(post_irs)) if len(post_irs) > 1 else post_irs[0]
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

    has_quantifier = any(
        getattr(e, "kind", "") in ("all", "any")
        for e in (inv_irs + post_irs)
    )
    if has_quantifier:
        vars_set |= _extract_vars(inv_smt, post_smt, scaff_smt or "")

    lines = [
        f"(set-logic {'NIA' if has_quantifier else 'QF_NIA'})",
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
    params = [name for name, _ in _func_params(func_node)]

    # Compute expanded params, init state, and record section
    if full_tree is not None:
        expanded_params, class_fields, params_coq, init_state, record_section = \
            _expand_params(full_tree, params, func_node)
    else:
        expanded_params = params
        coq_types = {
            arg: _py_type_to_coq(annot)
            for arg, annot in _func_params(func_node)
        }
        params_coq = " ".join(f"({p} : {coq_types.get(p, 'Z')})" for p in params)
        init_state = "empty_state"
        for p in params:
            init_state = f'(upd {init_state} "{p}"%string (VZ {p}))'
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

    # Fix unscoped string/list parameter names in contracts
    # When 'name: str' is encoded as 'name__len: Z', bare 'name' in the
    # precondition doesn't resolve. Substitute → name__len for comparisons.
    if full_tree is not None:
        pre_coq = _subst_param_names(pre_coq, func_node, full_tree)

    # Check for while/for loops and generate VCG obligations (one per loop with invariants)
    vcg_section = ""
    loops_with_invs = _loops_with_invariants(func_node, lint_results)
    for loop_node, loop_invs in loops_with_invs:
        inv_coq = " /\\ ".join(
            r.lint_result.ir.to_coq(False)
            for r in loop_invs if r.lint_result.ir
        ) or "True"
        post_vcg = " /\\ ".join(
            r.lint_result.ir.to_coq(False)
            for r in posts if r.lint_result.ir
        ) or "True"
        pre_vcg = " /\\ ".join(
            r.lint_result.ir.to_coq(False)
            for r in pres if r.lint_result.ir
        ) or "True"
        exit_cond = _loop_exit_condition(loop_node)
        result_scaffold, scaffold_vars = _vcg_result_scaffold(imp_body)

        inv_irs = [r.lint_result.ir for r in loop_invs if r.lint_result.ir]
        post_irs = [r.lint_result.ir for r in posts if r.lint_result.ir]
        smt_result = _try_smt_vcg_ir(inv_irs, exit_cond, post_irs, result_scaffold)

        if smt_result.is_valid:
            vcg_section += f"""
(* Verification condition proved by SMT (cvc4) *)
(* {inv_coq} -> {exit_cond} -> {post_vcg} *)
"""
        else:
            ce_note = ""
            if smt_result.counterexample:
                ce_str = ", ".join(f"{k}={v}" for k, v in smt_result.counterexample.items())
                ce_note = f" (* SMT counterexample: {ce_str} — strengthen invariant to rule this out *)"
            all_vcg_vars = set()
            all_vcg_vars.add("result")
            for r in pres + loop_invs + posts:
                if r.lint_result.ir:
                    all_vcg_vars |= _extract_ir_vars(r.lint_result.ir)
            all_vcg_vars |= scaffold_vars
            vcg_params = " ".join(f"({v} : Z)" for v in sorted(all_vcg_vars))
            n_params = len(all_vcg_vars)
            intros_pat = " ".join(["?"] * n_params) + " Hpre Hinv Hexit" if n_params > 0 else "Hpre Hinv Hexit"
            vcg_section += f"""(* Verification condition: precondition + invariant + exit -> postcondition{ce_note} *)
Theorem {name}_vcg_exit_{loop_node.lineno} : forall {vcg_params},
  ({pre_vcg}) ->
  ({inv_coq}) ->
  {exit_cond} ->
  {result_scaffold}
  ({post_vcg}).
Proof.
  intros {intros_pat}{' Hres' if result_scaffold.strip() else ''}.
  repeat (match goal with
    | H: _ /\\ _ |- _ => destruct H
  end).
  match type of Hexit with
  | _ \\/ _ => destruct Hexit as [H1 | H2];
    [rewrite Z.leb_gt in H1; lia | rewrite Z.leb_gt in H2; lia]
  | _ => rewrite Z.leb_gt in Hexit; lia
  end.
Qed.
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
                ce_note = f" -- SMT counterexample: {ce_str} -- strengthen invariant to rule this out"
            all_vcg_vars = set()
            all_vcg_vars.add("result")
            for r in pres + loop_invs + posts:
                if r.lint_result.ir:
                    all_vcg_vars |= _extract_ir_vars(r.lint_result.ir)
            all_vcg_vars |= scaffold_vars
            vcg_params = " ".join(f"({v} : Z)" for v in sorted(all_vcg_vars))
            n_params = len(all_vcg_vars)
            intros_pat = " ".join(["?"] * n_params) + " Hpre Hinv Hexit" if n_params > 0 else "Hpre Hinv Hexit"
            vcg_section = f"""(* Verification condition: precondition + invariant + exit -> postcondition{ce_note} *)
Theorem {name}_vcg_exit : forall {vcg_params},
  ({pre_vcg}) ->
  ({inv_coq}) ->
  {exit_cond} ->
  {result_scaffold}
  ({post_vcg}).
Proof.
  intros {intros_pat}{' Hres' if result_scaffold.strip() else ''}.
  repeat (match goal with
    | H: _ /\\ _ |- _ => destruct H
  end).
  match type of Hexit with
  | _ \\/ _ => destruct Hexit as [H1 | H2];
    [rewrite Z.leb_gt in H1; lia | rewrite Z.leb_gt in H2; lia]
  | _ => rewrite Z.leb_gt in Hexit; lia
  end.
Qed.
"""

    use_conditional_proof = False  # wp_prove handles conditionals generically now

    # Purity analysis — determine if frame conditions can be inferred
    purity_report: "PurityReport | None" = None
    frame_comment = ""
    if full_tree is not None:
        contract_map_coq = _build_contract_map(full_tree)
        purity_report = analyze_purity(
            func_node, full_tree, contract_map_coq, class_fields,
        )
        if not purity_report.is_pure:
            imp_body = generate_havoc_body(imp_body, purity_report)
            frame_comment = f" (* Black hole: {purity_report.black_hole_reason} *)"
        elif class_fields:
            post_asserts = [r.node for r in lint_results if r.classification == "postcondition"]
            frame_conds = generate_frame_conditions(func_node, full_tree, class_fields, post_asserts)
            if frame_conds:
                post_frame = " /\\ ".join(frame_conds)
                post_coq = f"({post_coq}) /\\ ({post_frame})"

    hammer_import = ""
    if hint == "hammer":
        hammer_import = "From Hammer Require Import Hammer.\n"
        proof = "  intros.\n  wp_reduce.\n  hammer."
    elif post_coq == "True":
        proof = "  intros.\n  apply wp_True."
    elif "forall" in post_coq or "exists" in post_coq:
        proof = "  intros.\n  wp_reduce.\n  lia."
    else:
        proof = "  intros.\n  wp_prove."

    bool_import = "Require Import Bool.\n" if "BOr" in imp_body else ""

    # Build annotated source comments for pre/post conditions
    source_notes = ""
    for r in lint_results:
        if r.lint_result.coq_translation:
            safe = r.lint_result.coq_translation.replace("*)", "* )")[:60]
            source_notes += f"(* line {r.lineno}: [{r.classification}] {safe} *)\n"

    return f"""(* Auto-generated from {name} *){frame_comment}
{source_notes}
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
            "and loop invariants. Detects: for-loops, while-loops, list/dict/set "
            "operations, string indexing, function calls. Does NOT run verification."
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
            "Level 1: wp_reduce/wp_prove (structural + linear arithmetic). "
            "Level 2: SMT (cvc4) for VCG obligations (non-linear, division). "
            "Level 3: LLM oracle (DeepSeek) with coqpyt interactive proof "
            "for remaining goals. Supports: lists, dicts, sets, strings, "
            "function calls (CCall), for-loops, while-loops, BOr conditionals. "
            "Returns proof status + SMT counterexample if invariant is too weak. "
            "Results are cached for instant re-verification of unchanged functions."
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
                "hint": {
                    "type": "string",
                    "description": "Optional: 'hammer' for SMT ATP fallback, or guidance text for LLM thinking time",
                },
            },
            "required": ["source", "function_name"],
        },
    },
    {
        "name": "verify-function",
        "description": (
            "Cache-aware single function verification. Same as check-function "
            "but emphasizes caching — instant response for previously verified "
            "functions whose body, contracts, and callee contracts are unchanged."
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
                "hint": {
                    "type": "string",
                    "description": "Optional: 'hammer' for SMT ATP fallback",
                },
            },
            "required": ["source", "function_name"],
        },
    },
    {
        "name": "verify-changed",
        "description": (
            "Incremental verification: find changed functions in a source file "
            "and re-verify only those impacted. Tracks: body changes (local only), "
            "contract changes (self + transitive callers), callee contract changes. "
            "Use after editing contracts or function bodies to quickly re-check "
            "only what's affected."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "source": {
                    "type": "string",
                    "description": "Python source code to analyze for changes",
                },
                "hint": {
                    "type": "string",
                    "description": "Optional: 'hammer' for SMT ATP fallback",
                },
            },
            "required": ["source"],
        },
    },
    {
        "name": "verify-impacted",
        "description": (
            "Dry-run: show which functions would be re-verified without running "
            "verification. Computes hashes of all functions in a source file and "
            "reports which have body/contract/callee-contract changes, plus which "
            "transitive callers would be re-verified due to contract propagation."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "source": {
                    "type": "string",
                    "description": "Python source code to analyze for impact",
                },
            },
            "required": ["source"],
        },
    },
    {
        "name": "explain-cache",
        "description": (
            "Explain the cache state for a function: show current vs cached hashes "
            "for body, contract, local asserts, and callee contracts. Reports which "
            "dimensions changed and lists callers that would be re-verified on "
            "contract changes."
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
                    "description": "Name of the function to explain",
                },
            },
            "required": ["source", "function_name"],
        },
    },
    {
        "name": "frame-report",
        "description": (
            "Report contracts (pre/post/invariant) and frame conditions "
            "(reads/writes) for functions. Shows assert-based contracts classified "
            "by position, frame variables inferred from the AST, and callee effects "
            "from library stubs. Optionally filter to a single function."
        ),
        "inputSchema": {
            "type": "object",
            "properties": {
                "source": {
                    "type": "string",
                    "description": "Python source code to analyze",
                },
                "function_name": {
                    "type": "string",
                    "description": "Optional: report only this function",
                },
            },
            "required": ["source"],
        },
    },
]


def handle_initialize(params: dict) -> dict:
    return {
        "protocolVersion": "2024-11-05",
        "capabilities": {"tools": {}},
        "serverInfo": {"name": "axiomander", "version": "0.4.0"},
    }


def handle_list_tools() -> dict:
    return {"tools": TOOLS}


def handle_call_tool(params: dict) -> dict:
    name = params.get("name", "")
    args = params.get("arguments", {})

    try:
        if name == "check-file":
            result = tool_check_file(args)
        elif name == "check-function":
            result = tool_check_function(args)
        elif name == "verify-function":
            result = tool_verify_function(args)
        elif name == "verify-changed":
            result = tool_verify_changed(args)
        elif name == "verify-impacted":
            result = tool_verify_impacted(args)
        elif name == "explain-cache":
            result = tool_explain_cache(args)
        elif name == "frame-report":
            result = tool_frame_report(args)
        else:
            return {"content": [{"type": "text", "text": f"Unknown tool: {name}"}], "isError": True}
    except Exception as e:
        import traceback
        return {"content": [{"type": "text", "text": f"Error: {e}\n{traceback.format_exc()[-500:]}"}], "isError": True}

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

    @app.command()
    def verify_function(
        file: str,
        function: str = typer.Option(..., "--function", "-f", help="Function name to verify"),
        hint: Optional[str] = typer.Option(None, "--hint", help="Tactic hint: hammer, smt, lia, auto"),
    ):
        """Verify a function with caching (alias for check-function)."""
        opts = {"source": _Path(file).read_text(), "function_name": function}
        if hint:
            opts["hint"] = hint
        typer.echo(tool_verify_function(opts))

    @app.command()
    def verify_changed(
        file: str,
        hint: Optional[str] = typer.Option(None, "--hint", help="Tactic hint: hammer"),
    ):
        """Incremental verification: re-verify only changed functions."""
        opts = {"source": _Path(file).read_text()}
        if hint:
            opts["hint"] = hint
        typer.echo(tool_verify_changed(opts))

    @app.command()
    def verify_impacted(file: str):
        """Show which functions would be re-verified (dry-run)."""
        typer.echo(tool_verify_impacted({"source": _Path(file).read_text()}))

    @app.command()
    def explain_cache(
        file: str,
        function: str = typer.Option(..., "--function", "-f", help="Function name to explain"),
    ):
        """Explain the cache state for a function."""
        typer.echo(tool_explain_cache({
            "source": _Path(file).read_text(),
            "function_name": function,
        }))

    app()


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1:
        _cli(sys.argv)
    else:
        main()
