"""
SMT Export — convert VCG obligations to SMT-LIB and call z3/cvc4.

The VCG formula is a quantifier-free Z arithmetic problem:
  invariant /\ exit_condition -> postcondition

We check validity by asking the SMT solver if the negation is satisfiable.
If UNSAT, the VCG is valid (proved). If SAT, there's a counterexample.
"""

import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


@dataclass
class SmtResult:
    """Result of an SMT solver call."""
    is_valid: bool       # True = UNSAT (formula is valid/proved)
    counterexample: dict[str, int] = field(default_factory=dict)
    solver: str = ""
    raw_output: str = ""
    error: str = ""


def verify_vcg(
    invariant: str,
    exit_cond: str,
    postcondition: str,
    scaffold: str = "",
    solver: str = "cvc4",
) -> SmtResult:
    """Verify a VCG obligation using an SMT solver.

    Args:
        invariant: Unscoped Coq formula (e.g. "acc = i*(i+1)/2 /\ i <= n")
        exit_cond: Coq exit condition (e.g. "Z.leb (i+1) n = false")
        postcondition: Unscoped Coq postcondition (e.g. "acc = n*(n+1)/2 /\ i = n")
        scaffold: Optional result scaffolding (e.g. "result = acc")
        solver: SMT solver binary name (cvc4 or z3)

    Returns:
        SmtResult with is_valid=True if the VCG is proved.
    """
    declarations = _extract_vars(invariant, exit_cond, postcondition, scaffold)
    if not declarations:
        return SmtResult(is_valid=False, error="No variables found")

    inv_smt = _expr_to_smt(invariant)
    exit_smt = _expr_to_smt(exit_cond)
    post_smt = _expr_to_smt(postcondition)
    scaff_smt = _expr_to_smt(scaffold) if scaffold else ""

    if not inv_smt or not exit_smt or not post_smt:
        return SmtResult(is_valid=False, error="Expression conversion failed")

    smt_lines = [
        "(set-logic QF_NIA)",
        "(set-option :produce-models true)",
    ]
    for var in sorted(declarations):
        smt_lines.append(f"(declare-fun {var} () Int)")

    smt_lines.append(f"(assert {inv_smt})")
    smt_lines.append(f"(assert {exit_smt})")
    if scaff_smt:
        smt_lines.append(f"(assert {scaff_smt})")
    smt_lines.append(f"(assert (not {post_smt}))")
    smt_lines.append("(check-sat)")

    smt_src = "\n".join(smt_lines)

    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".smt2", delete=False, prefix="vcg_"
        ) as f:
            f.write(smt_src)
            tmp_path = Path(f.name)

        result = subprocess.run(
            [solver, str(tmp_path)],
            capture_output=True, text=True, timeout=10,
        )
        output = result.stdout + result.stderr
        return _parse_smt_output(output, solver)
    except subprocess.TimeoutExpired:
        return SmtResult(is_valid=False, error=f"{solver} timed out")
    except FileNotFoundError:
        return SmtResult(is_valid=False, error=f"Solver '{solver}' not found")
    finally:
        if tmp_path and tmp_path.exists():
            tmp_path.unlink(missing_ok=True)


def _extract_vars(*args: str) -> set[str]:
    """Extract Z variable names from Coq expressions.

    Contracts:
      post: vars_set contains all identifier-like substrings from all args,
            minus the excluded keyword set.
    """
    vars_set: set[str] = set()
    for expr in args:
        if not expr:
            continue
        for name in re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', expr):
            if name.lower() not in {
                'true', 'false', 'z', 'string', 'and', 'or', 'not',
                'fun', 's', 'leb', 'parray_key', '%', 'prop',
            }:
                vars_set.add(name)
    return vars_set


# ─── Coq → SMT-LIB expression converter ──────────────────────────

_COMP_OPS = {'<=': '<=', '>=': '>=', '<': '<', '>': '>', '=': '='}
_LOGIC_OPS = {'/\\': 'and', '\\/': 'or'}


def _expr_to_smt(expr: str) -> str:
    """Convert a Coq expression to an SMT-LIB expression."""
    expr = expr.strip()

    # Handle Z.leb x y = false → (not (<= x y))
    m = re.match(r'Z\.leb\s+(.+)\s+(.+)\s*=\s*false\s*$', expr)
    if m:
        a = _expr_to_smt(m.group(1))
        b = _expr_to_smt(m.group(2))
        return f"(not (<= {a} {b}))"

    # Handle Z.leb x y = true → (<= x y)
    m = re.match(r'Z\.leb\s+(.+)\s+(.+)\s*=\s*true\s*$', expr)
    if m:
        a = _expr_to_smt(m.group(1))
        b = _expr_to_smt(m.group(2))
        return f"(<= {a} {b})"

    # Handle ~ (expr) → (not expr)
    m = re.match(r'~\s*\((.+)\)\s*$', expr)
    if m:
        return f"(not {_expr_to_smt(m.group(1))})"

    # Handle negation without parens: ~ A
    m = re.match(r'~\s+(.+)\s*$', expr)
    if m:
        return f"(not {_expr_to_smt(m.group(1))})"

    # Split on /\ or \/ at the top level
    top_op = _find_top_level_logical_op(expr)
    if top_op:
        op_str, left, right = top_op
        smt_op = _LOGIC_OPS[op_str]
        return f"({smt_op} {_expr_to_smt(left)} {_expr_to_smt(right)})"

    # Split on comparison operators at top level
    for coq_op, smt_op in [('=', '='), ('<=', '<='), ('>=', '>='),
                              ('<', '<'), ('>', '>')]:
        comp = _find_top_level_binop(expr, coq_op)
        if comp:
            left, right = comp
            return f"({smt_op} {_expr_to_smt(left)} {_expr_to_smt(right)})"

    # Split on +, - at top level
    for coq_op, smt_op in [('+', '+'), ('-', '-')]:
        add = _find_top_level_binop(expr, coq_op)
        if add:
            left, right = add
            return f"({smt_op} {_expr_to_smt(left)} {_expr_to_smt(right)})"

    # Split on *, / at top level
    for coq_op, smt_op in [('*', '*'), ('/', 'div')]:
        mul = _find_top_level_binop(expr, coq_op)
        if mul:
            left, right = mul
            return f"({smt_op} {_expr_to_smt(left)} {_expr_to_smt(right)})"

    # Strip outer parens and recurse
    if expr.startswith('(') and expr.endswith(')'):
        inner = expr[1:-1].strip()
        if _balanced(inner):
            return _expr_to_smt(inner)

    # Literal or variable
    stripped = expr.strip()
    # Strip %Z suffix
    stripped = re.sub(r'%Z$', '', stripped)
    return stripped


def _find_top_level_logical_op(expr: str) -> Optional[tuple[str, str, str]]:
    """Find a top-level /\ or \/ in expr (not inside parens)."""
    return _find_top_level_op(expr, list(_LOGIC_OPS.keys()))


def _find_top_level_binop(expr: str, op: str) -> Optional[tuple[str, str]]:
    """Find a top-level occurrence of op (not inside parens).
    Returns (left, right) or None.
    """
    result = _find_top_level_op(expr, [op])
    if result:
        _, left, right = result
        return (left, right)
    return None


def _find_top_level_op(expr: str, ops: list[str]) -> Optional[tuple[str, str, str]]:
    """Find the first top-level operator from ops (not inside parens).

    Contracts:
      pre:  expr is not empty
      inv:  depth >= 0
      post: returns (op, left, right) where op is at paren-depth 0, or None
    """
    assert len(expr) > 0
    depth = 0
    for i in range(len(expr) - 1, -1, -1):
        c = expr[i]
        if c == ')':
            depth += 1
        elif c == '(':
            depth -= 1
        elif depth == 0:
            for op in ops:
                op_len = len(op)
                end = i + 1
                start = end - op_len
                if start >= 0 and expr[start:end] == op:
                    # Check: not part of a larger token
                    before = expr[start - 1] if start > 0 else ' '
                    after = expr[end] if end < len(expr) else ' '
                    if before in ' \t\n' or before == '(':
                        left = expr[:start].strip()
                        right = expr[end:].strip()
                        if left and right:
                            return (op, left, right)
    return None


def _balanced(expr: str) -> bool:
    """Check if parentheses are balanced.

    Contracts:
      pre:  len(expr) >= 0
      inv:  depth >= 0
      post: result == True iff each '(' has a matching ')' and no ')' precedes its '('
    """
    assert len(expr) >= 0
    depth = 0
    for c in expr:
        assert depth >= 0
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def _parse_smt_output(output: str, solver: str) -> SmtResult:
    """Parse SMT solver output."""
    lines = output.strip().split('\n')
    status = ""
    model: dict[str, int] = {}

    for line in lines:
        line = line.strip()
        if line == 'sat':
            status = 'sat'
        elif line == 'unsat':
            status = 'unsat'
        elif line.startswith('(define-fun') and status == 'sat':
            m = re.match(r'\(define-fun\s+(\w+)\s+\(\)\s+Int\s+(-?\d+)\)', line)
            if m:
                model[m.group(1)] = int(m.group(2))

    if status == 'unsat':
        return SmtResult(is_valid=True, solver=solver, raw_output=output)
    elif status == 'sat':
        return SmtResult(
            is_valid=False, counterexample=model,
            solver=solver, raw_output=output,
            error=f"Counterexample: {model}" if model else "SAT",
        )
    else:
        return SmtResult(
            is_valid=False,
            error=f"Unknown SMT output: {output[:200]}",
            solver=solver, raw_output=output,
        )
