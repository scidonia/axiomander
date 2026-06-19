"""
Advisor — LLM-powered contract guidance for the MCP server.

When verification fails, generates specific, actionable advice about:
  - Why the current assertions are insufficient
  - What invariants/preconditions/postconditions to add
  - Whether the property might be false
  - How to restructure the function for verifiability

Uses the LLM oracle (client.py) to generate guidance when
the templated heuristics aren't sufficient.
"""

from dataclasses import dataclass, field
from typing import Optional

from .docstring_contracts import parse_axiomander_docstring


import ast
@dataclass
class AdornmentAdvice:
    """Advice for where to add assertions in a function."""
    location: str           # "function_start", "loop_body", "before_return"
    line: int
    suggestion: str         # e.g. "Add precondition: assert x >= 0"
    template: str = ""      # e.g. "assert <condition>"
    reasoning: str = ""     # Why this assertion is needed


@dataclass
class FunctionAnalysis:
    """Complete analysis of a function's contract status."""
    name: str
    has_preconditions: bool = False
    has_postconditions: bool = False
    has_invariants: bool = False
    has_loops: bool = False
    has_conditionals: bool = False
    has_side_effects: bool = False
    has_impure_calls: bool = False
    impure_calls: list[str] = field(default_factory=list)
    frame_fields: list[str] = field(default_factory=list)
    existing_asserts: list[str] = field(default_factory=list)
    suggested_adornments: list[AdornmentAdvice] = field(default_factory=list)
    verification_status: str = "not_attempted"
    failure_detail: str = ""
    llm_guidance: str = ""


@dataclass
class FileAnalysis:
    """Analysis of an entire Python file."""
    functions: list[FunctionAnalysis]
    summary: str


def analyze_function(source: str, func_name: str | None = None) -> FunctionAnalysis:
    """Analyze a function and suggest where to add assertions.

    Does NOT run verification — just structural analysis.
    """
    import ast

    tree = ast.parse(source)
    func_node = None
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            if func_name is None or node.name == func_name:
                func_node = node
                break

    if func_node is None:
        return FunctionAnalysis(name=func_name or "unknown")

    analysis = FunctionAnalysis(name=func_node.name)

    doc_contracts = parse_axiomander_docstring(func_node)
    if doc_contracts.requires:
        analysis.has_preconditions = True
        for req in doc_contracts.requires:
            analysis.existing_asserts.append(f"Docstring [precondition]: {req}")
    if doc_contracts.ensures:
        analysis.has_postconditions = True
        for ens in doc_contracts.ensures:
            analysis.existing_asserts.append(f"Docstring [postcondition]: {ens}")

    # Check for loops and conditionals
    for node in ast.walk(func_node):
        if isinstance(node, (ast.While, ast.For)):
            analysis.has_loops = True
        if isinstance(node, ast.If):
            analysis.has_conditionals = True
        if isinstance(node, ast.Call):
            name = _get_call_name(node)
            if name and name not in _PURE:
                analysis.has_side_effects = True
        if isinstance(node, ast.Assert):
            classification = _classify_in_function(func_node, node)
            analysis.existing_asserts.append(
                f"Line {node.lineno} [{classification}]: {ast.unparse(node)}"
            )
            if classification == "precondition":
                analysis.has_preconditions = True
            elif classification == "postcondition":
                analysis.has_postconditions = True
            elif classification == "invariant":
                analysis.has_invariants = True

    # Purity analysis
    from .purity_analyzer import analyze_purity as _analyze_purity
    class_fields_map: dict[str, list[str]] = {}
    for n in ast.walk(tree):
        if isinstance(n, ast.ClassDef):
            fields = []
            for s in n.body:
                if isinstance(s, ast.AnnAssign) and isinstance(s.target, ast.Name):
                    fields.append(s.target.id)
            if fields:
                class_fields_map[n.name] = fields
    purity = _analyze_purity(func_node, tree, {}, class_fields_map)
    analysis.has_impure_calls = not purity.is_pure
    analysis.impure_calls = list(dict.fromkeys(purity.impure_calls))

    # Generate adornment suggestions
    analysis.suggested_adornments = _suggest_adornments(func_node, analysis)

    return analysis


def analyze_file(source: str) -> FileAnalysis:
    """Analyze an entire Python file for contract adornment opportunities."""
    import ast
    tree = ast.parse(source)
    funcs = []

    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            analysis = analyze_function(source, node.name)
            funcs.append(analysis)

    # Build summary
    total = len(funcs)
    adorned = sum(1 for f in funcs if f.has_preconditions or f.has_postconditions)
    with_loops = sum(1 for f in funcs if f.has_loops)
    missing_invariants = sum(1 for f in funcs if f.has_loops and not f.has_invariants)

    summary = f"{total} function(s), {adorned} with contracts, {with_loops} with loops, {missing_invariants} missing invariants"

    return FileAnalysis(functions=funcs, summary=summary)


def generate_llm_guidance(
    func_name: str,
    goal_statement: str,
    error_detail: str,
    existing_asserts: list[str],
    suggestions: list[AdornmentAdvice],
) -> str:
    """Use the LLM to generate specific guidance for a failed verification.

    Returns templated guidance if no API key is set, otherwise calls the LLM.
    """
    # Build a templated fallback
    fallback = _templated_guidance(func_name, error_detail, suggestions)
    return fallback
    prompt = f"""A Coq verification of this Python function failed.

Function: {func_name}

Existing assertions:
{chr(10).join(existing_asserts) if existing_asserts else '(none)'}

Suggested adornments:
{chr(10).join(f'- {s.location} line {s.line}: {s.suggestion}' for s in suggestions) if suggestions else '(none)'}

Verification error:
{error_detail[:1000]}

Goal statement:
{goal_statement[:500]}

Please provide specific, actionable guidance:
1. Why did the verification fail? (one sentence)
2. What specific assert statements should be added or changed? (use Python syntax)
3. Should the user try a different approach (e.g., add a helper lemma, restructure the loop)?
"""

    system = "You are a formal verification advisor. Give concise, actionable advice about Python assert-based contracts. Use Python assert syntax in your suggestions."

    try:
        response = call_llm(config, system, prompt)
        if response:
            return response.strip()
    except Exception:
        pass

    return fallback


def _templated_guidance(name: str, error: str, suggestions: list[AdornmentAdvice]) -> str:
    """Generate templated guidance when LLM is unavailable."""
    parts = [f"## Verification of `{name}` failed\n"]

    if "invariant" in error.lower() or "loop" in error.lower():
        parts.append("**Issue**: The function contains a loop but no loop invariant.\n")
        parts.append("**Fix**: Add an assert at the top of the loop body describing what the loop preserves.\n")
        parts.append("Example:")
        parts.append("```python")
        parts.append("while i < n:")
        parts.append("    assert acc == i * (i + 1) // 2  # loop invariant")
        parts.append("    i += 1; acc += i")
        parts.append("```\n")
    elif "type" in error.lower() or "unify" in error.lower():
        parts.append("**Issue**: The expressions in your assertions could not be translated.\n")
        parts.append("**Fix**: Use simple expressions: comparisons (==, !=, <, <=, >, >=), arithmetic (+, -, *, //), and logical operators (and, or, not).\n")
    elif "could not" in error.lower():
        parts.append("**Issue**: The prover could not automatically close the goal.\n")
        parts.append("**Fix**: Try adding more assertions to break the proof into smaller steps.\n")
    else:
        parts.append("**Issue**: The verification could not be completed.\n")
        parts.append(f"**Error**: {error[:200]}\n")

    if suggestions:
        parts.append("## Suggested assertions to add\n")
        for s in suggestions:
            parts.append(f"- **{s.location}** (line {s.line}): `{s.suggestion}`")
            if s.reasoning:
                parts.append(f"  - Reason: {s.reasoning}")
        parts.append("")

    parts.append("\nTry adding the suggested assertions and re-running verification.")
    return "\n".join(parts)


# ─── Helpers ──────────────────────────────────────────────────────

_PURE = frozenset({"abs", "len", "min", "max", "sum", "sorted", "all", "any",
                    "isinstance", "int", "float", "bool", "str", "ord", "chr",
                    "range", "round", "pow", "sqrt"})


def _get_call_name(node: ast.Call) -> Optional[str]:
    """Get the name of a function call."""
    import ast
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        parts = []
        c = node.func
        while isinstance(c, ast.Attribute):
            parts.append(c.attr)
            c = c.value
        if isinstance(c, ast.Name):
            parts.append(c.id)
        return ".".join(reversed(parts))
    return None


def _classify_in_function(func_node, assert_node) -> str:
    """Classify an assert within a function."""
    import ast
    # Check if it's in a loop body
    for node in ast.walk(func_node):
        if isinstance(node, (ast.While, ast.For)):
            for child in ast.iter_child_nodes(node):
                if child is assert_node:
                    return "invariant"
            for i, stmt in enumerate(node.body):
                if stmt is assert_node:
                    # Check if it's the first non-docstring statement
                    all_asserts_before = all(
                        isinstance(s, ast.Assert)
                        for s in node.body[:i]
                    )
                    if all_asserts_before:
                        return "invariant"

    # Check if immediately before a return
    body = func_node.body
    for i, stmt in enumerate(body):
        if stmt is assert_node:
            if i + 1 < len(body) and isinstance(body[i + 1], ast.Return):
                return "postcondition"

    # Check if at function start
    seen_code = False
    for stmt in body:
        if stmt is assert_node:
            if not seen_code:
                return "precondition"
            break
        is_doc = (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant)
                  and isinstance(stmt.value.value, str))
        if not isinstance(stmt, ast.Assert) and not is_doc:
            seen_code = True

    return "general"


def _structural_facts(func_node) -> dict:
    """Extract structural facts from a function for contract guidance.

    Returns a dict with:
      shaped_params   -- params accessed via .field (need is_shape)
      list_params     -- params annotated as list[T] or used with len()
      str_params      -- params annotated as str
      readonly_params -- params that are never assigned in the body
      mutated_params  -- params (or their fields) that are assigned
      loop_vars       -- (loop_var, bound_expr) pairs from while/for
      accumulators    -- names assigned 0 before a loop
      builds_list     -- names that have .append() called on them
      return_type     -- return annotation string, or ""
      calls           -- set of function/method names called
    """
    params = {arg.arg for arg in func_node.args.args}

    shaped: set[str] = set()
    list_params: set[str] = set()
    str_params: set[str] = set()
    mutated: set[str] = set()
    loop_vars: list[tuple[str, str]] = []
    accumulators: set[str] = set()
    builds_list: set[str] = set()
    calls: set[str] = set()

    # Param type annotations
    for arg in func_node.args.args:
        if arg.annotation:
            try:
                annot = ast.unparse(arg.annotation)
            except Exception:
                annot = ""
            if "list" in annot.lower() or "List" in annot:
                list_params.add(arg.arg)
            elif annot in ("str", "string"):
                str_params.add(arg.arg)

    for node in ast.walk(func_node):
        # Attribute access on a param -> shaped
        if isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Name) and node.value.id in params:
                if node.value.id != "self":
                    shaped.add(node.value.id)

        # Assignments -> mutated
        if isinstance(node, ast.Assign):
            for t in node.targets:
                if isinstance(t, ast.Name):
                    mutated.add(t.id)
            # Accumulator: x = 0 before any loop
            for t in node.targets:
                if (isinstance(t, ast.Name)
                        and isinstance(node.value, ast.Constant)
                        and node.value.value == 0):
                    accumulators.add(t.id)
        if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
            mutated.add(node.target.id)

        # len() used with a param -> list-like
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == "len"
                and node.args
                and isinstance(node.args[0], ast.Name)
                and node.args[0].id in params):
            list_params.add(node.args[0].id)

        # list.append() -> builds_list
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "append"
                and isinstance(node.func.value, ast.Name)):
            builds_list.add(node.func.value.id)

        # While loop bounds
        if isinstance(node, ast.While) and isinstance(node.test, ast.Compare):
            try:
                var = ast.unparse(node.test.left)
                bound = ast.unparse(node.test.comparators[0])
                loop_vars.append((var, bound))
            except Exception:
                pass

        # For loop
        if isinstance(node, ast.For):
            try:
                var = ast.unparse(node.target)
                it = ast.unparse(node.iter)
                loop_vars.append((var, it))
            except Exception:
                pass

        # Function/method calls
        if isinstance(node, ast.Call):
            try:
                calls.add(ast.unparse(node.func))
            except Exception:
                pass

    readonly = params - mutated - {"self"}

    return_type = ""
    if func_node.returns:
        try:
            return_type = ast.unparse(func_node.returns)
        except Exception:
            pass

    return {
        "shaped_params":   shaped,
        "list_params":     list_params,
        "str_params":      str_params,
        "readonly_params": readonly,
        "mutated_params":  mutated & params,
        "loop_vars":       loop_vars,
        "accumulators":    accumulators,
        "builds_list":     builds_list,
        "return_type":     return_type,
        "calls":           calls,
    }


def _suggest_adornments(func_node, analysis: FunctionAnalysis) -> list[AdornmentAdvice]:
    """Suggest where to add assertions based on structural analysis.

    Uses structural facts (shaped params, read-only params, loop vars,
    return type) to produce targeted guidance and starting templates.
    The templates are concise starters -- the user or LLM fills in the
    domain-specific semantic content.
    """
    import ast
    suggestions = []
    facts = _structural_facts(func_node)
    params = [arg.arg for arg in func_node.args.args if arg.arg != "self"]

    # ── Preconditions ────────────────────────────────────────────────
    if not analysis.has_preconditions and params:
        first_line = func_node.body[0].lineno if func_node.body else func_node.lineno + 1

        # Build specific requires lines from structural facts
        req_lines: list[str] = []
        for p in params:
            if p in facts["shaped_params"]:
                req_lines.append(f"        is_shape({p})")
            elif p in facts["list_params"]:
                req_lines.append(f"        len({p}) >= 0")
            elif p in facts["str_params"]:
                req_lines.append(f"        len({p}) >= 0")
        if not req_lines:
            req_lines = [f"        <condition on {', '.join(params)}>"]

        # Reasoning notes what was detected
        notes: list[str] = []
        if facts["shaped_params"]:
            notes.append(f"{', '.join(sorted(facts['shaped_params']))} accessed via attributes")
        if facts["list_params"]:
            notes.append(f"{', '.join(sorted(facts['list_params']))} used as list")

        template = (
            '"""\n'
            'axiomander:\n'
            '    requires:\n'
            + "\n".join(req_lines) + "\n"
            '"""'
        )
        reasoning = (
            ("Structural: " + "; ".join(notes) + ". " if notes else "")
            + "Add any domain-specific constraints (value ranges, non-emptiness, "
            "relationships between params)."
        )
        suggestions.append(AdornmentAdvice(
            location="function_start",
            line=first_line,
            suggestion=f"Add precondition for {', '.join(params)}",
            template=template,
            reasoning=reasoning,
        ))

    # ── Loop invariants ──────────────────────────────────────────────
    if analysis.has_loops and not analysis.has_invariants:
        for node in ast.walk(func_node):
            if isinstance(node, (ast.While, ast.For)):
                # Build invariant hints from loop structure
                inv_lines: list[str] = []
                notes_inv: list[str] = []

                if isinstance(node, ast.While) and isinstance(node.test, ast.Compare):
                    try:
                        var = ast.unparse(node.test.left)
                        bound = ast.unparse(node.test.comparators[0])
                        inv_lines.append(f"    assert {var} <= {bound}")
                        notes_inv.append(f"loop counter {var} bounded by {bound}")
                    except Exception:
                        pass

                for acc in sorted(facts["accumulators"]):
                    inv_lines.append(f"    assert {acc} >= 0  # accumulator")
                    notes_inv.append(f"{acc} is an accumulator")

                for lst in sorted(facts["builds_list"]):
                    inv_lines.append(f"    assert len({lst}) >= 0  # growing list")

                if not inv_lines:
                    inv_lines = ["    assert <invariant condition>"]

                template = "\n".join(inv_lines)
                reasoning = (
                    ("Structural: " + "; ".join(notes_inv) + ". " if notes_inv else "")
                    + "The invariant must hold at every iteration. Add relationships "
                    "between accumulators, counters, and the collection being processed."
                )
                suggestions.append(AdornmentAdvice(
                    location="loop_body",
                    line=node.lineno,
                    suggestion="Add loop invariant at the top of this loop body",
                    template=template,
                    reasoning=reasoning,
                ))
                break

    # ── Postconditions ───────────────────────────────────────────────
    if not analysis.has_postconditions:
        returns = [n for n in ast.walk(func_node) if isinstance(n, ast.Return)]
        if returns:
            last_return = returns[-1]

            ens_lines: list[str] = []
            notes_post: list[str] = []

            # Return type hint
            rt = facts["return_type"]
            if rt and rt not in ("None", ""):
                ens_lines.append(f"        # result : {rt}")

            # Frame conditions for read-only params
            for p in sorted(facts["readonly_params"]):
                ens_lines.append(f"        {p} == old({p})  # {p} not modified")
                notes_post.append(f"{p} is read-only")

            # Placeholder for value postcondition
            ens_lines.append("        <what result satisfies>")

            template = (
                '"""\n'
                'axiomander:\n'
                '    ensures:\n'
                + "\n".join(ens_lines) + "\n"
                '"""'
            )
            reasoning = (
                ("Structural: " + "; ".join(notes_post) + ". " if notes_post else "")
                + "Frame conditions for read-only params are shown. "
                "Add the semantic guarantee about result."
            )
            suggestions.append(AdornmentAdvice(
                location="before_return",
                line=last_return.lineno - 1,
                suggestion="Add postcondition describing what the function guarantees",
                template=template,
                reasoning=reasoning,
            ))

    return suggestions
