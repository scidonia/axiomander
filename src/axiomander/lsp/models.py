"""LSP-specific data models for Axiomander."""

from typing import List, Optional, Dict, Any
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from enum import Enum

from lsprotocol.types import Diagnostic, DiagnosticSeverity, Position, Range
from ..storage.models import Component, ComponentType


class ComponentDiagnosticType(str, Enum):
    """Types of component diagnostics."""
    MISSING_FILE = "missing_file"
    INVALID_JSON = "invalid_json"
    MISSING_METADATA = "missing_metadata"
    CONTRACT_ERROR = "contract_error"
    DEPENDENCY_ERROR = "dependency_error"
    CIRCULAR_DEPENDENCY = "circular_dependency"


@dataclass
class ComponentIndexEntry:
    """Index entry for a component with cached metadata."""
    
    uid: str
    name: str
    component_type: ComponentType
    file_path: Path
    metadata: Component
    files: Dict[str, Path]  # logical.py, implementation.py, test.py
    last_modified: datetime
    diagnostics: List[Diagnostic]
    dependencies: List[str]
    dependents: List[str]


@dataclass
class ComponentHoverInfo:
    """Information to display on hover for a component."""
    
    name: str
    component_type: ComponentType
    description: Optional[str]
    pre_contract: Optional[str]
    post_contract: Optional[str]
    invariant_contract: Optional[str]
    dependencies: List[str]
    file_path: str
    uid: str


@dataclass
class LSPProgress:
    """Progress tracking for long-running LSP operations."""
    
    token: str
    title: str
    message: Optional[str] = None
    percentage: Optional[int] = None
    cancellable: bool = False
