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
    # raises: list of (exc_type, condition_expr) pairs
    # e.g. [("ValueError", "n < 0"), ("KeyError", "key not in mapping")]
    raises: list[tuple[str, str]] = field(default_factory=list)
    # units: raw lines from the units: section, parsed by dim_ir.parse_units_section
    units_lines: list[str] = field(default_factory=list)

    @property
    def has_contracts(self) -> bool:
        return bool(self.where or self.requires or self.ensures
                    or self.reads or self.modifies or self.raises)

    @property
    def has_units(self) -> bool:
        return bool(self.units_lines)


def parse_axiomander_docstring(func_node: ast.FunctionDef) -> DocstringContracts:
    """Parse minimal `axiomander:` function-docstring contracts.

    Accepted minimal shape:

        axiomander:
            where:
                old_a: int = a
                old_b = b
            requires:
                a >= 0
            ensures:
                result == old_a
            modifies:
                none

    Section bodies are one expression/binding per non-empty line.  More complex
    continuation syntax is intentionally not supported yet.
    """
    doc = ast.get_docstring(func_node, clean=False) or ""
    if "axiomander:" not in doc:
        return DocstringContracts()

    result = DocstringContracts()
    section: str | None = None
    in_axiomander = False

    for raw in inspect.cleandoc(doc).splitlines():
        stripped = raw.strip()
        if not stripped:
            continue
        if stripped == "axiomander:":
            in_axiomander = True
            section = None
            continue
        if not in_axiomander:
            continue

        m_section = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):\s*$", stripped)
        if m_section:
            section = m_section.group(1)
            continue

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
            result.ensures.append(_rewrite_old_refs(stripped, result.where))
            continue

        if section == "reads":
            result.reads.extend(_parse_name_list(stripped))
            continue

        if section == "modifies":
            result.modifies.extend(_parse_name_list(stripped))
            continue

        if section == "raises":
            # Format: ExcType: condition_expression
            # e.g.  ValueError: n < 0
            m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):\s*(.+)$", stripped)
            if m:
                exc_type = m.group(1)
                cond = _rewrite_old_refs(m.group(2).strip(), result.where)
                result.raises.append((exc_type, cond))
            continue

        if section == "units":
            # Raw lines accumulated and parsed lazily by dim_ir.parse_units_section
            result.units_lines.append(stripped)
            continue

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
