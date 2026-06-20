"""Parser for Axiomander docstring contracts.

This is intentionally small: it implements the first usable slice of the
Nagini-lifted syntax (`where`, `requires`, `ensures`, `reads`, `modifies`,
`raises`) and leaves ownership, predicates, etc. for later phases.
"""

from __future__ import annotations

import ast
import inspect
import re
from dataclasses import dataclass, field


@dataclass
class DocstringContracts:
    where: dict[str, str] = field(default_factory=dict)
    requires: list[str] = field(default_factory=list)
    ensures: list[str] = field(default_factory=list)
    reads: list[str] = field(default_factory=list)
    modifies: list[str] = field(default_factory=list)
    raises: list[tuple[str, str]] = field(default_factory=list)
    units_lines: list[str] = field(default_factory=list)
    # owns: resource ownership declarations
    #   e.g. ["queue_item: OrderQueue.item(order_id)", "order_row: Orders.row(order_id)"]
    owns: list[str] = field(default_factory=list)
    # frame: frame-condition clauses (may_modify, must_not_modify, may_emit, must_not_emit)
    frame: dict[str, list[str]] = field(default_factory=dict)
    # preserves: global invariants the function must maintain
    preserves: list[str] = field(default_factory=list)

    @property
    def has_contracts(self) -> bool:
        return bool(self.where or self.requires or self.ensures
                    or self.reads or self.modifies or self.raises)

    @property
    def has_units(self) -> bool:
        return bool(self.units_lines)


def parse_axiomander_docstring(func_node: ast.FunctionDef) -> DocstringContracts:
    """Parse `axiomander:` function-docstring contracts.

    Supports two formats:
      (A) Section-header style:
            axiomander:
                requires:
                    a >= 0
                ensures:
                    result >= 0
      (B) Per-line keyword style (used by fulfil_order contract.py):
            axiomander:
                requires OrderQueue.contains(order_id)
                ensures result.status in {\"fulfilled\", \"failed\"}
                ensures result == \"fulfilled\" ->
                    Orders.row(order_id).status == \"fulfilled\"
                    and Payment(order_id).state == \"captured\"
                preserves GlobalInvariant.foo

    In style (B), `ensures X ->` opens a continuation block where each
    continuation line contributes to the conjunction; `ensures X:` opens
    an indented sub-block (like exactly_once_domain_effect).
    """
    doc = ast.get_docstring(func_node, clean=False) or ""
    if "axiomander:" not in doc:
        return DocstringContracts()

    result = DocstringContracts()
    section: str | None = None
    in_axiomander = False
    # Per-line-keyword tracking: when an ensures/requires keyword appears
    # inline, subsequent indented continuation lines feed into the same
    # expression (joined by "and" for ensures, ignored for requires).
    cont_ensures: str | None = None  # active ensures expression being continued
    cont_block: str | None = None    # "and" or "block" — how to join continuations
    cont_is_implies: bool = False    # True if the antecedent was followed by ->

    for raw in inspect.cleandoc(doc).splitlines():
        stripped = raw.strip()
        if not stripped:
            continue
        if stripped == "axiomander:":
            in_axiomander = True
            section = None
            continue
        # One-liner: axiomander: requires: expr; ensures: expr
        if stripped.startswith("axiomander:") and stripped != "axiomander:":
            in_axiomander = True
            section = None
            stripped = stripped[len("axiomander:"):].strip()
            # Recurse into this line to handle per-line keywords
            raw = stripped  # feed back to the keyword handler below
        if not in_axiomander:
            continue

        # ── Section-header style: word: on its own line ──
        m_section = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):\s*$", stripped)
        if m_section and not cont_ensures:
            section = m_section.group(1)
            continue

        # ── Per-line-keyword style: <keyword> <expr> ──
        m_kw = re.match(
            r"^(requires|ensures|owns|preserves)(?:\s+|\s*:\s*)(.+?)$", stripped)
        if m_kw:
            kw = m_kw.group(1)
            rest = m_kw.group(2).strip()
            # Flush pending continuation from a previous [ensures X ->]
            # before starting a new ensures block.
            if cont_ensures is not None:
                expr = _rewrite_old_refs(cont_ensures, result.where)
                if cont_is_implies:
                    # Reconstruct the implies(antecedent, consequent) that
                    # the -> arrow originally indicated.
                    parts = expr.split(" and ", 1)
                    if len(parts) == 2:
                        expr = f"implies({parts[0]}, {parts[1]})"
                else:
                    expr = _rewrite_arrow_implies(expr)
                result.ensures.append(expr)
                cont_ensures = None
                cont_is_implies = False
            if kw == "requires":
                result.requires.append(
                    _rewrite_old_refs(rest, result.where))
                continue
            if kw == "preserves":
                result.preserves.append(rest)
                continue
            if kw == "owns":
                # Format: name: expression
                result.owns.append(rest)
                continue
            if kw == "ensures":
                rest_stripped = rest.rstrip()
                if rest_stripped.endswith("->"):
                    ante = rest_stripped[:-2].strip()
                    cont_ensures = ante
                    cont_block = "and"
                    cont_is_implies = True
                elif rest_stripped.endswith(":"):
                    # Sub-block (e.g. exactly_once_domain_effect):
                    ante = rest_stripped[:-1].strip()
                    cont_ensures = ante
                    cont_block = "block"
                else:
                    expr = _rewrite_old_refs(rest, result.where)
                    expr = _rewrite_arrow_implies(expr)
                    result.ensures.append(expr)
                continue

        # ── Continuation lines (after ensures X ->) ──
        if cont_ensures is not None:
            stripped_cont = stripped
            # Strip "and " prefix if present (word, not character set)
            if stripped_cont.startswith("and "):
                stripped_cont = stripped_cont[4:]
            if cont_block == "and":
                cont_ensures += " and " + stripped_cont
                continue
            elif cont_block == "block":
                # Indented sub-block content
                cont_ensures += " and " + stripped_cont
                continue

        # ── Frame section dispatch ──
        if section == "frame":
            m_sub = re.match(r"^([a-z_][a-z0-9_]*)\s+(.+?)$", stripped)
            if m_sub:
                sub = m_sub.group(1)
                val = m_sub.group(2).strip()
                result.frame.setdefault(sub, []).append(val)
            continue

        # ── Section-body style ──
        if section == "where":
            m = re.match(
                r"^([A-Za-z_][A-Za-z0-9_]*)(?:\s*:\s*[^=]+)?\s*=\s*([A-Za-z_][A-Za-z0-9_]*)\s*$",
                stripped,
            )
            if m:
                result.where[m.group(1)] = m.group(2)
            continue

        if section == "requires":
            result.requires.append(_rewrite_old_refs(stripped, result.where))
            continue

        if section == "ensures":
            expr = _rewrite_old_refs(stripped, result.where)
            expr = _rewrite_arrow_implies(expr)
            result.ensures.append(expr)
            continue

        if section == "reads":
            result.reads.extend(_parse_name_list(stripped))
            continue

        if section == "modifies":
            result.modifies.extend(_parse_name_list(stripped))
            continue

        if section == "raises":
            m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):\s*(.+)$", stripped)
            if m:
                exc_type = m.group(1)
                cond = _rewrite_old_refs(m.group(2).strip(), result.where)
                result.raises.append((exc_type, cond))
            continue

        if section == "owns":
            result.owns.append(stripped)
            continue

        if section == "preserves":
            result.preserves.append(stripped)
            continue

        if section == "units":
            result.units_lines.append(stripped)
            continue

    # Flush any pending continuation
    if cont_ensures is not None:
        expr = _rewrite_old_refs(cont_ensures, result.where)
        if cont_is_implies:
            parts = expr.split(" and ", 1)
            if len(parts) == 2:
                expr = f"implies({parts[0]}, {parts[1]})"
        else:
            expr = _rewrite_arrow_implies(expr)
        result.ensures.append(expr)

    return result


def _rewrite_old_refs(expr: str, where: dict[str, str]) -> str:
    """Rewrite `old(x)` in docstring specs to an implicit where binding.

    Minimal first slice: only `old(name)` is supported.  It becomes `old_name`,
    and `where["old_name"] = "name"` is added unless already present.
    """
    def repl(match: re.Match[str]) -> str:
        name = match.group(1)
        ghost_name = f"old_{name}"
        where.setdefault(ghost_name, name)
        return ghost_name

    return re.sub(r"\bold\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)", repl, expr)


def _parse_name_list(line: str) -> list[str]:
    if line in {"none", "[]", "(none)"}:
        return []
    return [part.strip() for part in re.split(r",|\s+", line) if part.strip()]


def _rewrite_arrow_implies(expr: str) -> str:
    """Rewrite Python docstring arrow syntax `P -> Q` to `implies(P, Q)`.

    The arrow [->] is replaced with [implies(] and a closing [)] is appended.
    Only handles a single arrow (the top-level implication); nested arrows
    need explicit `implies()` calls.
    """
    if "->" not in expr:
        return expr
    # Split at the first ->, treating what's before as the condition and
    # what's after as the (potentially compound) consequent.
    parts = expr.split("->", 1)
    ante = parts[0].strip()
    cons = parts[1].strip()
    return f"implies({ante}, {cons})"


def docstring_assert_nodes(func_node: ast.FunctionDef) -> list[tuple[ast.Assert, str]]:
    """Return docstring requires/ensures/raises as synthetic ast.Assert nodes.

    Multi-line expressions in ensures/requires sections are joined into single
    entries before parsing.  A line that fails to parse as a standalone
    expression is treated as a continuation of the previous incomplete line.
    """
    parsed = parse_axiomander_docstring(func_node)
    out: list[tuple[ast.Assert, str]] = []

    def _group_expressions(entries: list[str]) -> list[str]:
        """Join continuation lines into complete expressions.

        Each line that parses as a standalone eval expression starts a new
        group.  Each line that does NOT parse is joined (with a space) to
        the most recent incomplete group — or starts a new one if there
        is no incomplete group already open.
        """
        groups: list[str] = []
        incomplete = False
        for text in entries:
            try:
                ast.parse(text, mode="eval")
                groups.append(text)
                incomplete = False
            except SyntaxError:
                if incomplete and groups:
                    groups[-1] = groups[-1] + " " + text
                else:
                    groups.append(text)
                    incomplete = True
        return groups

    # requires -> precondition, ensures -> postcondition
    for expr_text, cls in [
        (e, "precondition") for e in _group_expressions(parsed.requires)
    ] + [
        (e, "postcondition") for e in _group_expressions(parsed.ensures)
    ]:
        try:
            expr = ast.parse(expr_text, mode="eval").body
        except SyntaxError:
            continue
        node = ast.Assert(test=expr, msg=None)
        node.lineno = getattr(func_node, "lineno", 1)
        node.col_offset = 0
        ast.fix_missing_locations(node)
        out.append((node, cls))

    # raises -> exception_postcondition via raises(ExcType, cond) synthetic call
    for exc_type, cond_text in parsed.raises:
        try:
            cond_expr = ast.parse(cond_text, mode="eval").body
        except SyntaxError:
            continue
        # Build: raises(ExcType, cond_expr)  as an AST Call node
        call = ast.Call(
            func=ast.Name(id="raises", ctx=ast.Load()),
            args=[ast.Name(id=exc_type, ctx=ast.Load()), cond_expr],
            keywords=[],
        )
        node = ast.Assert(test=call, msg=None)
        node.lineno = getattr(func_node, "lineno", 1)
        node.col_offset = 0
        ast.fix_missing_locations(node)
        out.append((node, "exception_postcondition"))

    return out
