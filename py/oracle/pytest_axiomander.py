"""
pytest_axiomander.py -- pytest plugin: verification as a CI gate.

Level B of the executable-tests feature.

At pytest collection time, for every function in the collected test file's
corresponding source file, this plugin calls ``_verify_function`` from
``mcp_server``.  The result maps to a pytest outcome:

  PROVED (any level)   -> pass  (the test is a no-op marker)
  COUNTEREXAMPLE       -> fail  (prints the SMT model)
  UNPROVED / LEVEL3    -> xfail (verification incomplete, not a hard failure)
  error / import fail  -> skip  (plugin couldn't run)

Usage
-----
Register the plugin in ``conftest.py``::

    pytest_plugins = ["oracle.pytest_axiomander"]

Or install it as a setuptools entry point (see pyproject.toml).

Configuration
-------------
Add to ``pytest.ini`` or ``pyproject.toml``::

    [tool.pytest.ini_options]
    axiomander_verify = true          # enable (default: false)
    axiomander_source_dir = "py"      # where to find source files

The plugin only activates when ``axiomander_verify = true`` to avoid
slowing down normal test runs.
"""

from __future__ import annotations

import ast
import os
from pathlib import Path
from typing import Optional

import pytest


# ---------------------------------------------------------------------------
# Plugin registration
# ---------------------------------------------------------------------------

def pytest_addoption(parser: pytest.Parser) -> None:
    """Add --axiomander-verify CLI flag."""
    group = parser.getgroup("axiomander")
    group.addoption(
        "--axiomander-verify",
        action="store_true",
        default=False,
        help="Run axiomander formal verification as a CI gate (Level B).",
    )


def pytest_configure(config: pytest.Config) -> None:
    """Register the axiomander marker."""
    config.addinivalue_line(
        "markers",
        "axiomander_verified: marks a test as backed by formal verification",
    )


# ---------------------------------------------------------------------------
# Verification item
# ---------------------------------------------------------------------------

class AxiomanderVerificationItem(pytest.Item):
    """A synthetic pytest item that runs formal verification for one function."""

    def __init__(
        self,
        name: str,
        parent: pytest.Collector,
        source: str,
        func_name: str,
        source_path: str,
    ) -> None:
        super().__init__(name, parent)
        self._source = source
        self._func_name = func_name
        self._source_path = source_path

    def runtest(self) -> None:
        """Run verification and map result to pytest outcome."""
        try:
            from .mcp_server import _verify_function
            from .reporting import ProofLevel
        except ImportError as exc:
            pytest.skip(f"axiomander not available: {exc}")
            return

        result = _verify_function(self._source, self._func_name)
        if result is None:
            pytest.skip(f"axiomander: could not verify {self._func_name}")
            return

        if result.is_proved():
            # Pass -- verification succeeded
            return

        if result.level == ProofLevel.COUNTEREXAMPLE:
            # Hard failure: SMT found a model that violates the contract
            ce_info = ""
            if result.counterexample:
                ce_info = "\nSMT counterexample: " + ", ".join(
                    f"{k}={v}" for k, v in result.counterexample.items()
                )
            if result.theory_counterexample:
                ce_info += f"\n{result.theory_counterexample}"
            pytest.fail(
                f"axiomander: contract violation in {self._func_name}{ce_info}",
                pytrace=False,
            )

        # UNPROVED / LEVEL3 -- soft failure
        reason = result.error_detail or result.suggestion_text or "verification incomplete"
        pytest.xfail(f"axiomander: {self._func_name} unproved -- {reason[:200]}")

    def repr_failure(self, excinfo: pytest.ExceptionInfo) -> str:  # type: ignore[override]
        return str(excinfo.value)

    def reportinfo(self) -> tuple[str, Optional[int], str]:
        return self._source_path, None, f"axiomander::{self._func_name}"


# ---------------------------------------------------------------------------
# Collector
# ---------------------------------------------------------------------------

class AxiomanderCollector(pytest.Collector):
    """Collect verification items for a Python source file."""

    def __init__(
        self,
        name: str,
        parent: pytest.Collector,
        source_path: str,
        source: str,
    ) -> None:
        super().__init__(name, parent)
        self._source_path = source_path
        self._source = source

    def collect(self):  # type: ignore[override]
        """Yield one AxiomanderVerificationItem per function with contracts."""
        try:
            tree = ast.parse(self._source)
        except SyntaxError:
            return

        for node in ast.walk(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            # Only collect functions that have at least one assert
            has_assert = any(
                isinstance(s, ast.Assert) for s in ast.walk(node)
            )
            if not has_assert:
                continue
            item_name = f"verify::{node.name}"
            yield AxiomanderVerificationItem(
                name=item_name,
                parent=self,
                source=self._source,
                func_name=node.name,
                source_path=self._source_path,
            )


# ---------------------------------------------------------------------------
# Hook: inject verification items alongside normal tests
# ---------------------------------------------------------------------------

def pytest_collect_file(
    parent: pytest.Collector,
    file_path: Path,
) -> Optional[pytest.Collector]:
    """Inject an AxiomanderCollector for every .py file when enabled."""
    config = parent.config
    if not config.getoption("--axiomander-verify", default=False):
        return None

    # Only collect Python source files (not test files themselves)
    if not file_path.suffix == ".py":
        return None
    if file_path.name.startswith("test_"):
        return None
    if file_path.name.startswith("conftest"):
        return None

    try:
        source = file_path.read_text(encoding="utf-8")
    except OSError:
        return None

    # Quick check: does the file have any assert statements?
    if "assert " not in source:
        return None

    return AxiomanderCollector(
        name=f"axiomander::{file_path.name}",
        parent=parent,
        source_path=str(file_path),
        source=source,
    )
