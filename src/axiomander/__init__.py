"""Axiomander - Design-by-Contract Agent System."""

__version__ = "0.1.0"

# Import main modules
from . import storage
from . import compiler
from . import exceptions

# Import contract decorators for easy access
from .contracts import precondition, postcondition, invariant

__all__ = [
    "storage",
    "compiler", 
    "exceptions",
    "precondition",
    "postcondition", 
    "invariant",
]
