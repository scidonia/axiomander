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


def verify_inv_update(
    inv_old: str,
    body_equalities: list[tuple[str, str]],
    inv_new: str,
    extra_vars: list[str] | None = None,
    solver: str = "cvc4",
) -> SmtResult:
    """Verify that a loop invariant is preserved by the body.

    Given:
      - inv_old: invariant at start of iteration (Coq expression)
      - body_equalities: [(new_var, expr)] from body execution
      - inv_new: invariant to prove after body (Coq expression)
      - extra_vars: additional variable names (e.g. ['z', 'bound'])

    Checks: inv_old /\\ body -> inv_new is valid (UNSAT of negation).
    """
    # Collect all variable names explicitly
    all_exprs = [inv_old, inv_new] + [e for _, e in body_equalities]
    vars_found = _extract_vars(*all_exprs)
    if extra_vars:
        vars_found.update(extra_vars)
    # Add body new-variables
    for new_var, _ in body_equalities:
        vars_found.add(new_var)
    if not vars_found:
        return SmtResult(is_valid=False, error="No variables found")

    inv_old_smt = _expr_to_smt(inv_old)
    inv_new_smt = _expr_to_smt(inv_new)
    body_smt_parts = [
        f"(= {new_var} {_expr_to_smt(expr)})"
        for new_var, expr in body_equalities
    ]
    body_smt = ("(and " + " ".join(body_smt_parts) + ")"
                if len(body_smt_parts) > 1
                else body_smt_parts[0] if body_smt_parts else "true")

    smt_lines = ["(set-logic QF_NIA)"]
    for var in sorted(vars_found):
        smt_lines.append(f"(declare-fun {var} () Int)")
    smt_lines.append(f"(assert {inv_old_smt})")
    if body_smt_parts:
        smt_lines.append(f"(assert {body_smt})")
    smt_lines.append(f"(assert (not {inv_new_smt}))")
    smt_lines.append("(check-sat)")

    smt_src = "\n".join(smt_lines)

    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".smt2", delete=False, prefix="inv_"
        ) as f:
            f.write(smt_src)
            tmp_path = Path(f.name)

        for s in ([solver] if solver != "any"
                  else ["cvc4", "z3", "cvc5"]):
            if not __import__("shutil").which(s):
                continue
            try:
                result = subprocess.run(
                    [s, str(tmp_path)],
                    capture_output=True, text=True, timeout=15)
                out = result.stdout.strip()
                if "unsat" in out:
                    return SmtResult(is_valid=True, solver=s, raw_output=out)
                if "sat" in out and "unsat" not in out:
                    return SmtResult(is_valid=False, solver=s, raw_output=out)
            except (subprocess.TimeoutExpired, FileNotFoundError):
                continue
        return SmtResult(is_valid=False, error="All solvers timed out or failed")
    finally:
        if tmp_path:
            try:
                tmp_path.unlink()
            except OSError:
                pass


def verify_vcg(
    invariant: str,
    exit_cond: str,
    postcondition: str,
    scaffold: str = "",
    solver: str = "cvc4",
) -> SmtResult:
    """Verify a VCG obligation using an SMT solver.

    Contracts:
      pre:  len(invariant) >= 0, len(exit_cond) >= 0, len(postcondition) >= 0
      post: SmtResult.is_valid iff the VCG is valid (UNSAT)
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
    """Extract variable-name identifiers from Coq expressions.

    Contracts:
      post: vars_set contains all substrings matching [a-zA-Z_][a-zA-Z0-9_]*
            from all args, minus the excluded keyword set.
    """
    EXCLUDED = {'true', 'false', 'z', 'string', 'and', 'or', 'not',
                'fun', 's', 'leb', 'parray_key', 'prop',
                'forall', 'exists', 'int', 'ite', 'mod', 'div', 'abs'}
    vars_set = set()
    for expr in args:
        if not expr:
            continue
        current = ""
        for c in expr:
            if c.isalnum() or c == '_':
                current += c
            else:
                if current and (current[0].isalpha() or current[0] == '_'):
                    if current.lower() not in EXCLUDED:
                        vars_set.add(current)
                current = ""
        if current and (current[0].isalpha() or current[0] == '_'):
            if current.lower() not in EXCLUDED:
                vars_set.add(current)
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
      pre: len(expr) > 0
      post: returns (op, left, right) at depth 0, or None
    """
    assert len(expr) > 0
    depth = 0
    for i in range(len(expr) - 1, -1, -1):
        c = expr[i]
        if c == ')':
            depth += 1
        elif c == '(':
            depth -= 1
        if depth == 0:
            for op in ops:
                op_len = len(op)
                end = i + 1
                start = end - op_len
                if start >= 0 and expr[start:end] == op:
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
