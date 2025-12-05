"""Utility functions for the LSP server."""

from typing import Optional, List
from pathlib import Path
from lsprotocol.types import Position, Range, Diagnostic, DiagnosticSeverity

from ..storage.models import Component


def path_to_uri(path: Path) -> str:
    """Convert a file path to a URI."""
    return path.as_uri()


def uri_to_path(uri: str) -> Path:
    """Convert a URI to a file path."""
    if uri.startswith("file://"):
        return Path(uri[7:])
    return Path(uri)


def create_diagnostic(
    message: str,
    severity: DiagnosticSeverity = DiagnosticSeverity.Error,
    line: int = 0,
    character: int = 0,
    end_line: Optional[int] = None,
    end_character: Optional[int] = None,
    source: str = "axiomander"
) -> Diagnostic:
    """Create an LSP diagnostic."""
    if end_line is None:
        end_line = line
    if end_character is None:
        end_character = character + 1
    
    return Diagnostic(
        range=Range(
            start=Position(line=line, character=character),
            end=Position(line=end_line, character=end_character)
        ),
        message=message,
        severity=severity,
        source=source
    )


def is_component_file(file_path: Path) -> bool:
    """Check if a file is part of a component."""
    return (
        file_path.name in ["component.json", "logical.py", "implementation.py", "test.py"]
        and ".axiomander/components" in str(file_path)
    )


def get_component_uid_from_path(file_path: Path) -> Optional[str]:
    """Extract component UID from a file path."""
    parts = file_path.parts
    try:
        axiomander_idx = parts.index(".axiomander")
        components_idx = parts.index("components", axiomander_idx)
        if components_idx + 1 < len(parts):
            return parts[components_idx + 1]
    except (ValueError, IndexError):
        pass
    return None


def format_component_hover_text(component: Component) -> str:
    """Format component information for hover display."""
    lines = [
        f"**{component.name}** ({component.component_type.value})",
        f"UID: `{component.uid}`",
        ""
    ]
    
    if component.description:
        lines.extend([
            "**Description:**",
            component.description,
            ""
        ])
    
    if component.pre_contract:
        lines.extend([
            "**Precondition:**",
            component.pre_contract,
            ""
        ])
    
    if component.post_contract:
        lines.extend([
            "**Postcondition:**",
            component.post_contract,
            ""
        ])
    
    if component.invariant_contract:
        lines.extend([
            "**Invariant:**",
            component.invariant_contract,
            ""
        ])
    
    if component.dependencies:
        lines.extend([
            "**Dependencies:**",
            *[f"- {dep.import_name} ({dep.uid})" for dep in component.dependencies],
            ""
        ])
    
    if component.tags:
        lines.extend([
            "**Tags:**",
            ", ".join(component.tags),
            ""
        ])
    
    lines.extend([
        f"**Created:** {component.created_at}",
        f"**Updated:** {component.updated_at}"
    ])
    
    return "\n".join(lines)
