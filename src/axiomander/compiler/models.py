"""Models for the component compiler system."""

from enum import Enum
from pathlib import Path
from typing import List, Optional, Set
from pydantic import BaseModel, Field


class CompilerMode(str, Enum):
    """Compilation modes for different use cases."""
    DEVELOPMENT = "development"
    PRODUCTION = "production"
    LIBRARY = "library"


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
        True,
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


class CompilationResult(BaseModel):
    """Result of a compilation operation."""
    
    success: bool = Field(
        ...,
        description="Whether the compilation was successful"
    )
    
    module_name: str = Field(
        ...,
        description="Name of the compiled module"
    )
    
    compiled_components: List[str] = Field(
        default_factory=list,
        description="List of component UIDs that were compiled"
    )
    
    generated_files: List[Path] = Field(
        default_factory=list,
        description="List of files that were generated"
    )
    
    errors: List[str] = Field(
        default_factory=list,
        description="List of compilation errors"
    )
    
    warnings: List[str] = Field(
        default_factory=list,
        description="List of compilation warnings"
    )


class ComponentMapping(BaseModel):
    """Mapping information for a compiled component."""
    
    uid: str = Field(
        ...,
        description="Original component UID"
    )
    
    original_name: str = Field(
        ...,
        description="Original component name"
    )
    
    uniquified_name: str = Field(
        ...,
        description="Uniquified name used in compilation"
    )
    
    path: Optional[str] = Field(
        None,
        description="Path within the module structure"
    )
    
    dependencies: Set[str] = Field(
        default_factory=set,
        description="Set of dependency component UIDs"
    )
