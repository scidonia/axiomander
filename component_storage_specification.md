# Axiomander Component Storage Specification

This document specifies the storage and management system for Axiomander components, focusing on the data models and file organization within the `.axiomander` directory structure.

## Overview

Components are individual objects that represent functions, classes, or modules with associated contracts. Each component is stored in its own directory within `.axiomander/components/` and contains both metadata and associated code files.

## Directory Structure

```
.axiomander/
├── components/
│   ├── {component_uid_1}/
│   │   ├── component.json
│   │   ├── logical.py
│   │   └── implementation.py
│   ├── {component_uid_2}/
│   │   ├── component.json
│   │   ├── logical.py
│   │   └── implementation.py
│   └── ...
├── graph.json
└── config.json
```

## Component Model

### Core Component Pydantic Model

```python
from typing import List, Optional, Dict, Any
from pydantic import BaseModel, Field
from enum import Enum
import uuid

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

    post_contract: Optional[str] = Field(
        None,
        description="String representation of the postcondition contract meaning"
    )

    invariant_contract: Optional[str] = Field(
        None,
        description="String representation of the invariant contract meaning (for classes)"
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
        ...,
        description="ISO timestamp when the component was created"
    )

    updated_at: str = Field(
        ...,
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
        ...,
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
```

## File Organization

### Component Directory Structure

Each component is stored in `.axiomander/components/{uid}/` containing:

1. **component.json**: Serialized Component model containing all metadata
2. **logical.py**: Contains the logical specification and contracts
3. **implementation.py**: Contains the actual implementation code

### Logical File Format

The `logical.py` file contains:
- Contract decorators and specifications
- Type hints and interfaces
- Documentation and examples
- Any logical constraints or relationships

### Implementation File Format

The `implementation.py` file contains:
- The actual executable code
- Implementation of the contracts
- Any helper functions or classes
- Import statements for dependencies

### Dependency Resolution

Dependencies are resolved by:
1. Looking up the dependency UID in the component graph
2. Loading the dependency's implementation file
3. Making the dependency available under the specified `import_name`

## Graph Management

The global graph (`graph.json`) maintains:
- **Nodes**: All component UIDs and their names
- **Edges**: Dependency relationships between components
- **Metadata**: Last update timestamp and version information

### Relationship Types

Edges in the graph can represent:
- `depends_on`: Component A uses/imports Component B
- `implements`: Component A implements interface/contract B
- `refines`: Component A is a refinement of Component B
- `tests`: Component A tests Component B

## Storage Operations

### Component Creation
1. Generate new UID
2. Create component directory
3. Write component.json with metadata
4. Create logical.py and implementation.py stubs
5. Update global graph

### Component Updates
1. Update component metadata in component.json
2. Update logical.py and/or implementation.py files
3. Update graph if dependencies changed
4. Update timestamps

### Dependency Management
1. Add dependency to component's dependencies list
2. Update component.json
3. Add edge to global graph
4. Validate no circular dependencies

## Validation Rules

1. **UID Uniqueness**: All component UIDs must be unique within the project
2. **Dependency Validity**: All dependency UIDs must reference existing components
3. **Circular Dependencies**: No circular dependency chains allowed
4. **File Consistency**: logical.py and implementation.py must be valid Python files
5. **Contract Consistency**: Contract status must match actual contract decorators in files

## Future Extensions

This specification is designed to support future enhancements:
- Multi-language support (TypeScript, Rust, etc.)
- Versioning of components
- Component templates and generators
- Distributed component repositories
- Component testing and validation frameworks
