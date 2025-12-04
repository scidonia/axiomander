# Axiomander Component Compiler Specification

This document specifies the component compiler system that transforms stored components into executable Python modules with proper dependency resolution and import management.

## Overview

The component compiler takes a set of components from the `.axiomander/components/` storage and generates a complete Python module structure under `src/{module_name}/` with all necessary files, imports, and dependency resolution.

## Compilation Process

### Input
- **Component Set**: A collection of component UIDs to compile together
- **Module Name**: The target module name for the generated code
- **Entry Point Component**: The main component that serves as the module's entry point

### Output Structure
```
src/
└── {module_name}/
    ├── __init__.py
    ├── main.py
    ├── {uniquified_component_name_1}.py
    ├── {uniquified_component_name_1}_logical.py
    ├── {uniquified_component_name_2}.py
    ├── {uniquified_component_name_2}_logical.py
    ├── {path_1}/
    │   ├── __init__.py
    │   ├── {uniquified_component_name_3}.py
    │   └── {uniquified_component_name_3}_logical.py
    └── ...
```

## File Generation Rules

### 1. Module Structure Generation

#### `src/{module_name}/__init__.py`
- Contains imports for all public components in the module
- Exposes the main entry point function/class
- Includes module-level docstring with component metadata
- Lists `__all__` with exported symbols

#### `src/{module_name}/main.py`
- Contains the entry point component's implementation
- Imports all direct dependencies from the same module
- Includes a `main()` function if the entry point is a function
- Includes `if __name__ == "__main__":` block for CLI execution

#### `src/{module_name}/{path}/{uniquified_component_name}.py`
- Begins with a comment containing the original component UID for tracking
- Contains the implementation code from the component's `implementation.py`
- Automatically imports the corresponding logical file at the beginning
- Imports all dependencies with proper symbol resolution
- Contains component metadata as module-level constants

#### `src/{module_name}/{path}/{uniquified_component_name}_logical.py`
- Begins with a comment containing the original component UID for tracking
- Contains the logical contracts from the component's `logical.py`
- Includes contract decorators, specifications, and validation logic
- Contains type hints and interface definitions

#### Path-based Directory Structure
- Components with a `path` designation are placed in subdirectories
- Each subdirectory contains its own `__init__.py` for proper Python module structure
- Path hierarchies create nested directory structures (e.g., `path/subpath/`)
- Root-level components (no path) are placed directly in the module directory

### 2. Name Uniquification

Components with conflicting names must be uniquified to prevent import collisions:

#### Uniquification Strategy
1. **Primary Name**: Use the component's original name if unique
2. **UID Suffix**: Append first 8 characters of UID if name conflicts exist
3. **Full UID**: Use full UID as last resort for extreme conflicts

#### Examples
- `calculate_sum` → `calculate_sum.py`
- `calculate_sum` (conflict) → `calculate_sum_a1b2c3d4.py`
- `calculate_sum` (extreme conflict) → `calculate_sum_a1b2c3d4_e5f6g7h8_i9j0k1l2.py`

### 3. Dependency Resolution

#### Transitive Dependency Collection
1. Start with the entry point component
2. Recursively collect all dependencies from the component graph
3. Include all transitive dependencies in the compilation set
4. Detect and report circular dependencies as compilation errors

#### Import Generation
For each component, generate imports based on its dependencies:

```python
# Component UID tracking comment
# axiomander:component:{component_uid}

# Automatic logical import
from .{uniquified_component_name}_logical import *

# Internal dependencies (within the same compiled module)
from .{uniquified_dependency_name} import {import_name}
from ..{path}.{uniquified_dependency_name} import {import_name}  # Cross-path dependencies

# External dependencies (from other modules or standard library)
import {external_module}
from {external_module} import {symbol}
```

#### Path-based Import Resolution
- Components in the same path import using relative imports (`.`)
- Components in different paths use relative imports with path navigation (`..path.module`)
- Root-level components import path-based components using relative imports (`.path.module`)
- Each path directory's `__init__.py` exports relevant symbols for easier importing

### 4. Contract Integration

#### Logical Contracts
- Extract contract decorators from `logical.py`
- Apply contracts to the implementation functions/classes
- Preserve contract metadata for runtime introspection

#### Contract Validation
- Include contract validation code in the compiled output
- Generate runtime assertions for preconditions and postconditions
- Include invariant checks for class-based components

## Compilation Modes

### 1. Development Mode
- Includes all contract validation and assertions
- Preserves component metadata and debugging information
- Generates verbose error messages with component context
- Includes test code integration points

### 2. Production Mode
- Optimizes contract validation (configurable)
- Strips debugging metadata to reduce size
- Generates optimized import statements
- Excludes test-related code

### 3. Library Mode
- Generates a reusable library structure
- Includes proper `__init__.py` exports
- Generates type stubs (`.pyi` files) for external consumption
- Includes documentation generation hooks

## Compiler Configuration

### Compilation Settings
```python
class CompilerConfig(BaseModel):
    """Configuration for the component compiler."""
    
    mode: CompilerMode = Field(
        CompilerMode.DEVELOPMENT,
        description="Compilation mode (development, production, library)"
    )
    
    target_directory: Path = Field(
        Path("src"),
        description="Target directory for generated code"
    )
    
    include_contracts: bool = Field(
        True,
        description="Whether to include contract validation in output"
    )
    
    include_tests: bool = Field(
        False,
        description="Whether to include test code in compilation"
    )
    
    optimize_imports: bool = Field(
        False,
        description="Whether to optimize and minimize import statements"
    )
    
    generate_type_stubs: bool = Field(
        False,
        description="Whether to generate .pyi type stub files"
    )
    
    preserve_metadata: bool = Field(
        True,
        description="Whether to preserve component metadata in output"
    )
```

## Error Handling

### Compilation Errors
1. **Circular Dependencies**: Detected during dependency resolution
2. **Missing Dependencies**: Referenced components not found in storage
3. **Name Conflicts**: Unresolvable naming conflicts after uniquification
4. **Invalid Contracts**: Malformed contract code in logical.py files
5. **Import Errors**: Invalid import statements in component dependencies

### Error Reporting
- Detailed error messages with component UID and name context
- Source location information (file, line number) when available
- Suggested fixes for common compilation issues
- Dependency graph visualization for circular dependency debugging

## Integration with Storage System

### Component Loading
- Load components and their metadata from `.axiomander/components/`
- Validate component consistency before compilation
- Use the component graph for dependency resolution
- Handle missing or corrupted component files gracefully
- Respect component `path` designations for directory placement

### Incremental Compilation
- Track component modification timestamps
- Only recompile changed components and their dependents
- Maintain compilation cache for unchanged components
- Support partial recompilation for large component sets

### Resync from Compiled Files
- Parse UID tracking comments to identify source components
- Extract implementation code from compiled files back to component storage
- Extract logical contracts from `_logical.py` files back to component storage
- Update component metadata and timestamps during resync
- Validate that changes don't break component dependencies
- Support selective resync of individual components or entire modules

## CLI Interface

### Compilation Commands
```bash
# Compile a specific component and its dependencies
axiomander compile {component_uid} --module-name {module_name}

# Compile multiple components into a single module
axiomander compile {uid1} {uid2} {uid3} --module-name {module_name}

# Compile with specific configuration
axiomander compile {component_uid} --module-name {module_name} --mode production

# Compile all components in the project
axiomander compile-all --output-dir dist/

# Resync changes from compiled files back to component storage
axiomander resync --module-name {module_name}

# Resync specific components only
axiomander resync {component_uid1} {component_uid2}

# Resync with validation and conflict resolution
axiomander resync --module-name {module_name} --validate --resolve-conflicts
```

### Compilation Options
- `--module-name`: Target module name for compilation
- `--mode`: Compilation mode (development, production, library)
- `--output-dir`: Override default output directory
- `--include-tests`: Include test code in compilation
- `--no-contracts`: Exclude contract validation from output
- `--optimize`: Enable import optimization and code minimization
- `--type-stubs`: Generate type stub files alongside code

### Resync Options
- `--validate`: Validate changes before applying to component storage
- `--resolve-conflicts`: Automatically resolve simple conflicts during resync
- `--dry-run`: Show what would be resynced without making changes
- `--force`: Force resync even if validation fails
- `--backup`: Create backup of component storage before resync

## Output Validation

### Generated Code Validation
1. **Syntax Validation**: Ensure all generated Python files are syntactically valid
2. **Import Validation**: Verify all import statements resolve correctly
3. **Contract Validation**: Ensure contract decorators are properly applied
4. **Type Validation**: Check type annotations and compatibility (if enabled)

### Runtime Testing
- Generate basic smoke tests for compiled modules
- Validate that all exported symbols are accessible
- Test contract enforcement in development mode
- Verify dependency injection and resolution

## Future Extensions

### Advanced Features
- **Multi-language Support**: Compile to TypeScript, Rust, or other target languages
- **Optimization Passes**: Dead code elimination, constant folding, inline expansion
- **Documentation Generation**: Automatic API documentation from contracts and metadata
- **Packaging Integration**: Generate setup.py, pyproject.toml, and distribution packages
- **IDE Integration**: Generate IDE-specific metadata for better development experience

### Performance Optimizations
- **Parallel Compilation**: Compile independent components in parallel
- **Caching Strategies**: Advanced caching for large projects with many components
- **Lazy Loading**: Generate code that supports lazy loading of dependencies
- **Bundle Optimization**: Minimize generated code size and import overhead
