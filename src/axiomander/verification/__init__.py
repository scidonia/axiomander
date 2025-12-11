"""
Verification module for Axiomander.

This module provides the main verification engine that coordinates
formal verification of Python functions using Z3.
"""

try:
    from .orchestrator import (
        VerificationOrchestrator,
        VerificationResult,
        create_orchestrator,
    )
    from .engine import (
        VerificationEngine,
        VerificationConfig,
        ProjectVerificationResult,
        create_engine,
    )

    __all__ = [
        "VerificationOrchestrator",
        "VerificationResult",
        "VerificationEngine",
        "VerificationConfig",
        "ProjectVerificationResult",
        "create_orchestrator",
        "create_engine",
    ]
except ImportError as e:
    # Graceful fallback if dependencies aren't available
    __all__ = []
