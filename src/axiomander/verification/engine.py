"""
Main Verification Engine for Axiomander

This module provides the high-level verification engine that integrates
with the orchestrator to perform formal verification of Python code.
"""

import logging
from typing import List, Dict, Any, Union, Optional
from pathlib import Path
from dataclasses import dataclass

from .orchestrator import (
    VerificationOrchestrator,
    VerificationResult,
    create_orchestrator,
)


logger = logging.getLogger(__name__)


@dataclass
class VerificationConfig:
    """Configuration for the verification engine."""

    timeout_seconds: int = 30
    max_assertions: int = 100
    enable_weakest_preconditions: bool = True
    enable_counterexamples: bool = True
    verbose: bool = False


@dataclass
class ProjectVerificationResult:
    """Results of verifying an entire project."""

    total_functions: int
    verified_functions: int
    failed_functions: int
    error_functions: int
    function_results: List[VerificationResult]
    total_execution_time: float

    @property
    def success_rate(self) -> float:
        """Calculate the verification success rate."""
        if self.total_functions == 0:
            return 1.0
        return self.verified_functions / self.total_functions


class VerificationEngine:
    """
    High-level verification engine for Axiomander.

    This engine coordinates formal verification of Python functions
    and provides comprehensive reporting of results.
    """

    def __init__(self, config: Optional[VerificationConfig] = None):
        self.config = config or VerificationConfig()
        self.orchestrator = create_orchestrator()

        # Setup logging based on config
        if self.config.verbose:
            logging.basicConfig(level=logging.DEBUG)
        else:
            logging.basicConfig(level=logging.INFO)

    def verify_file(self, file_path: Union[str, Path]) -> List[VerificationResult]:
        """
        Verify all functions in a single file.

        Args:
            file_path: Path to Python file to verify

        Returns:
            List of verification results for each function
        """
        logger.info(f"Starting verification of {file_path}")

        try:
            results = self.orchestrator.verify_file(file_path)

            # Log summary
            verified_count = sum(
                1 for r in results if r.success and len(r.failed_assertions) == 0
            )
            failed_count = sum(1 for r in results if len(r.failed_assertions) > 0)
            error_count = sum(1 for r in results if len(r.errors) > 0)

            logger.info(
                f"Verification complete for {file_path}: {verified_count} verified, {failed_count} failed, {error_count} errors"
            )

            return results

        except Exception as e:
            logger.error(f"Verification failed for {file_path}: {e}")
            return []

    def verify_project(
        self, project_path: Union[str, Path], file_patterns: Optional[List[str]] = None
    ) -> ProjectVerificationResult:
        """
        Verify all Python files in a project.

        Args:
            project_path: Root path of the project
            file_patterns: List of glob patterns for files to include (default: ["**/*.py"])

        Returns:
            Comprehensive verification results for the project
        """
        import time
        from glob import glob

        start_time = time.time()
        project_path = Path(project_path)

        if file_patterns is None:
            file_patterns = ["**/*.py"]

        logger.info(f"Starting project verification: {project_path}")

        # Find all Python files matching patterns
        all_files = set()
        for pattern in file_patterns:
            pattern_path = project_path / pattern
            matched_files = glob(str(pattern_path), recursive=True)
            all_files.update(Path(f) for f in matched_files)

        # Filter out files to exclude (e.g., test files, __pycache__)
        python_files = [
            f
            for f in all_files
            if f.suffix == ".py"
            and "__pycache__" not in str(f)
            and "/.git/" not in str(f)
        ]

        logger.info(f"Found {len(python_files)} Python files to verify")

        all_results = []
        verified_functions = 0
        failed_functions = 0
        error_functions = 0

        # Verify each file
        for file_path in python_files:
            try:
                file_results = self.verify_file(file_path)
                all_results.extend(file_results)

                # Count results
                for result in file_results:
                    if result.success and len(result.failed_assertions) == 0:
                        verified_functions += 1
                    elif len(result.failed_assertions) > 0:
                        failed_functions += 1
                    if len(result.errors) > 0:
                        error_functions += 1

            except Exception as e:
                logger.error(f"Failed to verify {file_path}: {e}")
                error_functions += 1

        total_time = time.time() - start_time

        project_result = ProjectVerificationResult(
            total_functions=len(all_results),
            verified_functions=verified_functions,
            failed_functions=failed_functions,
            error_functions=error_functions,
            function_results=all_results,
            total_execution_time=total_time,
        )

        logger.info(
            f"Project verification complete: {project_result.success_rate:.1%} success rate "
            f"({verified_functions}/{len(all_results)} functions verified)"
        )

        return project_result

    def verify_source_code(
        self, source_code: str, file_path: str = "<string>"
    ) -> List[VerificationResult]:
        """
        Verify functions in source code string.

        Args:
            source_code: Python source code to verify
            file_path: Optional file path for error reporting

        Returns:
            List of verification results
        """
        logger.info(f"Verifying source code from {file_path}")

        try:
            results = self.orchestrator.verify_source(source_code, file_path)

            verified_count = sum(
                1 for r in results if r.success and len(r.failed_assertions) == 0
            )
            failed_count = sum(1 for r in results if len(r.failed_assertions) > 0)
            error_count = sum(1 for r in results if len(r.errors) > 0)

            logger.info(
                f"Source verification complete: {verified_count} verified, {failed_count} failed, {error_count} errors"
            )

            return results

        except Exception as e:
            logger.error(f"Source verification failed: {e}")
            return []

    def print_results(
        self, results: Union[List[VerificationResult], ProjectVerificationResult]
    ):
        """
        Print verification results in a human-readable format.

        Args:
            results: Verification results to print
        """
        if isinstance(results, ProjectVerificationResult):
            self._print_project_results(results)
        else:
            self._print_function_results(results)

    def _print_function_results(self, results: List[VerificationResult]):
        """Print results for a list of function verifications."""
        print(f"\n=== Verification Results ({len(results)} functions) ===")

        for result in results:
            status = (
                "✓" if result.success and len(result.failed_assertions) == 0 else "✗"
            )
            print(f"\n{status} {result.function_name} ({result.file_path})")
            print(f"   Execution time: {result.execution_time:.3f}s")

            if result.verified_assertions:
                print(f"   ✓ Verified assertions ({len(result.verified_assertions)}):")
                for assertion in result.verified_assertions:
                    print(f"     - {assertion}")

            if result.failed_assertions:
                print(f"   ✗ Failed assertions ({len(result.failed_assertions)}):")
                for assertion in result.failed_assertions:
                    print(f"     - {assertion}")

            if result.counterexamples:
                print(f"   ⚠ Counterexamples ({len(result.counterexamples)}):")
                for ce in result.counterexamples:
                    print(f"     - {ce['assertion']}")
                    print(f"       Counterexample: {ce['counterexample']}")

            if result.errors:
                print(f"   ❌ Errors ({len(result.errors)}):")
                for error in result.errors:
                    print(f"     - {error}")

    def _print_project_results(self, result: ProjectVerificationResult):
        """Print results for a project verification."""
        print(f"\n=== Project Verification Results ===")
        print(f"Total functions: {result.total_functions}")
        print(f"Verified: {result.verified_functions} ({result.success_rate:.1%})")
        print(f"Failed: {result.failed_functions}")
        print(f"Errors: {result.error_functions}")
        print(f"Total execution time: {result.total_execution_time:.3f}s")

        if result.function_results:
            print(f"\n--- Individual Function Results ---")
            self._print_function_results(result.function_results)


def create_engine(config: Optional[VerificationConfig] = None) -> VerificationEngine:
    """Factory function to create a verification engine."""
    return VerificationEngine(config)
