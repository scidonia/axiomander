"""Pydantic models for component storage system."""

from typing import List, Optional, Dict
from pydantic import BaseModel, Field
from enum import Enum
import uuid
from datetime import datetime


class ComponentType(str, Enum):
    """Type of component being stored."""
    FUNCTION = "function"
    CLASS = "class"
    MODULE = "module"


class ComponentLanguage(str, Enum):
    """Programming language of the component."""
    PYTHON = "python"
    # Future: TYPESCRIPT = "typescript", RUST = "rust", etc.


class ComponentDependency(BaseModel):
    """Reference to another component that this component depends on."""
    
    uid: str = Field(
        ...,
        description="Unique identifier of the dependency component"
    )
    
    import_name: str = Field(
        ...,
        description="Name used to import/reference this dependency in the current component's code"
    )
    
    dependency_type: ComponentType = Field(
        ...,
        description="Type of the dependency (function, class, or module)"
    )


class ContractStatus(BaseModel):
    """Status of contract implementation for a component."""
    
    has_preconditions: bool = Field(
        False,
        description="Whether preconditions have been implemented"
    )
    
    has_postconditions: bool = Field(
        False,
        description="Whether postconditions have been implemented"
    )
    
    has_invariants: bool = Field(
        False,
        description="Whether invariants have been implemented (for classes)"
    )


class Component(BaseModel):
    """
    Core component model representing a function, class, or module with contracts.
    
    Each component is stored in its own directory within .axiomander/components/
    and contains both metadata (this model) and associated code files.
    """
    
    uid: str = Field(
        default_factory=lambda: str(uuid.uuid4()),
        description="Unique identifier for this component"
    )
    
    name: str = Field(
        ...,
        description="Name of the component (function name, class name, or module name)"
    )
    
    component_type: ComponentType = Field(
        ...,
        description="Type of component (function, class, or module)"
    )
    
    language: ComponentLanguage = Field(
        ComponentLanguage.PYTHON,
        description="Programming language of the component"
    )
    
    language_suffix: str = Field(
        ".py",
        description="File extension for the programming language"
    )
    
    # Contract Information
    contract_status: ContractStatus = Field(
        default_factory=ContractStatus,
        description="Status of contract implementation"
    )
    
    pre_contract: Optional[str] = Field(
        None,
        description="String representation of the precondition contract meaning"
    )
    
    precondition: Optional[str] = Field(
        None,
        description="Name of the precondition function/decorator in the logical file"
    )
    
    post_contract: Optional[str] = Field(
        None,
        description="String representation of the postcondition contract meaning"
    )
    
    postcondition: Optional[str] = Field(
        None,
        description="Name of the postcondition function/decorator in the logical file"
    )
    
    invariant_contract: Optional[str] = Field(
        None,
        description="String representation of the invariant contract meaning (for classes)"
    )
    
    invariant: Optional[str] = Field(
        None,
        description="Name of the invariant function/decorator in the logical file"
    )
    
    # Dependencies
    dependencies: List[ComponentDependency] = Field(
        default_factory=list,
        description="List of components that this component depends on"
    )
    
    # Metadata
    description: Optional[str] = Field(
        None,
        description="Human-readable description of the component's purpose"
    )
    
    tags: List[str] = Field(
        default_factory=list,
        description="Tags for categorizing and searching components"
    )
    
    created_at: str = Field(
        default_factory=lambda: datetime.now().isoformat(),
        description="ISO timestamp when the component was created"
    )
    
    updated_at: str = Field(
        default_factory=lambda: datetime.now().isoformat(),
        description="ISO timestamp when the component was last updated"
    )
    
    # File paths (relative to component directory)
    logical_file: str = Field(
        "logical.py",
        description="Filename for the logical specification file"
    )
    
    implementation_file: str = Field(
        "implementation.py",
        description="Filename for the implementation file"
    )
    
    test_file: str = Field(
        "test.py",
        description="Filename for the test file that validates contracts against implementation"
    )


class ComponentGraph(BaseModel):
    """
    Global graph representation of component relationships.
    
    Stored in .axiomander/graph.json to provide a complete view of
    component dependencies and relationships.
    """
    
    nodes: Dict[str, str] = Field(
        default_factory=dict,
        description="Mapping of component UID to component name"
    )
    
    edges: List[Dict[str, str]] = Field(
        default_factory=list,
        description="List of dependency relationships as {from_uid, to_uid, relationship_type}"
    )
    
    updated_at: str = Field(
        default_factory=lambda: datetime.now().isoformat(),
        description="ISO timestamp when the graph was last updated"
    )


class AxiomanderConfig(BaseModel):
    """
    Configuration for the Axiomander system.
    
    Stored in .axiomander/config.json
    """
    
    version: str = Field(
        "1.0.0",
        description="Version of the Axiomander system"
    )
    
    project_root: str = Field(
        ...,
        description="Root directory of the project"
    )
    
    default_language: ComponentLanguage = Field(
        ComponentLanguage.PYTHON,
        description="Default programming language for new components"
    )
    
    auto_generate_uids: bool = Field(
        True,
        description="Whether to automatically generate UIDs for new components"
    )
