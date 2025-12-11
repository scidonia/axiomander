"""
Axiomander - Formal Verification for Python using Z3 SMT Solver.

This library provides verification capabilities for Python code through
Z3 integration, with live linting via Language Server Protocol.
"""

__version__ = "0.1.0"
__author__ = "Scidonia"
__email__ = "axiomander@scidonia.com"

# Core API will be available once dependencies are resolved
__all__ = ["verify_file", "start_lsp_server"]


def verify_file(file_path: str) -> None:
    """
    Verify assertions in a Python file.

    Args:
        file_path: Path to the Python file to verify
    """
    from .cli.commands import verify_file as _verify_file

    _verify_file(file_path)


def start_lsp_server(host: str = "localhost", port: int = 0) -> None:
    """
    Start the Axiomander LSP server.

    Args:
        host: Host to bind the server to
        port: Port to bind the server to (0 for auto-select)
    """
    from .lsp.server import AxiomanderLSPServer

    server = AxiomanderLSPServer()
    server.start_server(host, port)
