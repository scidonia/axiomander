"""Parser for Axiomander docstring contracts.

This is intentionally small: it implements the first usable slice of the
Nagini-lifted syntax (`where`, `requires`, `ensures`) and leaves ownership,
raises, predicates, etc. for later phases.
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

    @property
    def has_contracts(self) -> bool:
        return bool(self.where or self.requires or self.ensures)


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
            result.requires.append(stripped)
            continue

        if section == "ensures":
            result.ensures.append(stripped)
            continue

    return result


def docstring_assert_nodes(func_node: ast.FunctionDef) -> list[tuple[ast.Assert, str]]:
    """Return docstring requires/ensures as synthetic ast.Assert nodes."""
    parsed = parse_axiomander_docstring(func_node)
    out: list[tuple[ast.Assert, str]] = []
    for expr_text, cls in [(e, "precondition") for e in parsed.requires] + [
        (e, "postcondition") for e in parsed.ensures
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
    return out
