"""
Command-line interface for axiomander.
"""

import sys
import json
import argparse
from pathlib import Path
from typing import Optional, List


def main():
    """Main CLI entry point."""
    print("Axiomander - Formal Verification for Python")
    print("=" * 40)

    if len(sys.argv) < 2:
        print_help()
        return

    command = sys.argv[1]

    if command == "verify":
        handle_verify_command(sys.argv[2:])

    elif command == "test-pipeline":
        handle_test_pipeline_command(sys.argv[2:])

    elif command == "verify-project":
        handle_verify_project_command(sys.argv[2:])

    elif command == "lsp":
        start_lsp_server()

    elif command == "help" or command == "--help" or command == "-h":
        print_help()

    else:
        print(f"Unknown command: {command}")
        print_help()


def print_help():
    """Print help message."""
    print("""
Usage: axiomander <command> [options]

Commands:
  verify <file.py>              Verify assertions in a Python file
  verify-project <path>         Verify all Python files in a project
  test-pipeline [options]       Test the Z3 verification pipeline
  lsp                          Start LSP server for editor integration
  help                         Show this help message

Options for verify:
  --verbose                    Enable detailed output
  --json                       Output results in JSON format
  --timeout <seconds>          Set verification timeout (default: 30)

Options for verify-project:
  --pattern <glob>             File pattern to match (default: **/*.py)
  --exclude <glob>             Files to exclude (can be repeated)
  --json                       Output results in JSON format

Options for test-pipeline:
  --run-examples              Run on built-in examples
  --test-simple               Test simple verification scenarios
  --test-complex              Test complex verification scenarios

Examples:
  axiomander verify my_code.py
  axiomander verify my_code.py --verbose --json
  axiomander verify-project ./src --pattern "*.py" --exclude "*test*.py"
  axiomander test-pipeline --run-examples
  axiomander lsp

For more information, visit: https://github.com/Scidonia/axiomander
""")


def handle_verify_command(args: List[str]):
    """Handle the verify command with arguments."""
    if not args:
        print("Usage: axiomander verify <file.py> [options]")
        return

    parser = argparse.ArgumentParser(prog="axiomander verify", add_help=False)
    parser.add_argument("file", help="Python file to verify")
    parser.add_argument("--verbose", action="store_true", help="Enable detailed output")
    parser.add_argument(
        "--json", action="store_true", help="Output results in JSON format"
    )
    parser.add_argument(
        "--timeout", type=int, default=30, help="Verification timeout in seconds"
    )
    parser.add_argument(
        "--dump-z3", type=str, help="Dump Z3 constraints to specified file"
    )

    try:
        parsed_args = parser.parse_args(args)
        verify_file_with_z3(
            parsed_args.file,
            parsed_args.verbose,
            parsed_args.json,
            parsed_args.timeout,
            parsed_args.dump_z3,
        )
    except SystemExit:
        print(
            "Usage: axiomander verify <file.py> [--verbose] [--json] [--timeout <seconds>]"
        )


def handle_verify_project_command(args: List[str]):
    """Handle the verify-project command with arguments."""
    if not args:
        print("Usage: axiomander verify-project <path> [options]")
        return

    parser = argparse.ArgumentParser(prog="axiomander verify-project", add_help=False)
    parser.add_argument("path", help="Project root path to verify")
    parser.add_argument(
        "--pattern", action="append", help="File pattern to match (can be repeated)"
    )
    parser.add_argument(
        "--exclude", action="append", help="Files to exclude (can be repeated)"
    )
    parser.add_argument(
        "--json", action="store_true", help="Output results in JSON format"
    )

    try:
        parsed_args = parser.parse_args(args)
        verify_project_with_z3(
            parsed_args.path,
            parsed_args.pattern or ["**/*.py"],
            parsed_args.exclude or [],
            parsed_args.json,
        )
    except SystemExit:
        print(
            "Usage: axiomander verify-project <path> [--pattern <glob>] [--exclude <glob>] [--json]"
        )


def handle_test_pipeline_command(args: List[str]):
    """Handle the test-pipeline command with arguments."""
    parser = argparse.ArgumentParser(prog="axiomander test-pipeline", add_help=False)
    parser.add_argument(
        "--run-examples", action="store_true", help="Run on built-in examples"
    )
    parser.add_argument(
        "--test-simple", action="store_true", help="Test simple verification scenarios"
    )
    parser.add_argument(
        "--test-complex",
        action="store_true",
        help="Test complex verification scenarios",
    )

    try:
        parsed_args = parser.parse_args(args)
        test_verification_pipeline(
            parsed_args.run_examples, parsed_args.test_simple, parsed_args.test_complex
        )
    except SystemExit:
        print(
            "Usage: axiomander test-pipeline [--run-examples] [--test-simple] [--test-complex]"
        )


def verify_file_with_z3(
    file_path: str,
    verbose: bool = False,
    json_output: bool = False,
    timeout: int = 30,
    dump_z3: Optional[str] = None,
):
    """Verify assertions in a Python file using Z3."""
    path = Path(file_path)

    if not path.exists():
        print(f"Error: File not found: {file_path}")
        return

    if not path.suffix == ".py":
        print(f"Error: Expected Python file (.py), got: {file_path}")
        return

    if not json_output:
        print(f"Verifying: {file_path}")

    try:
        # Import and use the verification orchestrator directly
        import sys
        import os

        # Add the src directory to the Python path temporarily
        current_dir = os.path.dirname(os.path.abspath(__file__))
        project_root = os.path.dirname(os.path.dirname(os.path.dirname(current_dir)))
        src_path = os.path.join(project_root, "src")

        if src_path not in sys.path:
            sys.path.insert(0, src_path)

        # Now import the orchestrator
        from axiomander.verification.orchestrator import VerificationOrchestrator

        orchestrator = VerificationOrchestrator()
        results = orchestrator.verify_file(file_path)

        # Dump Z3 constraints if requested
        if dump_z3:
            if dump_z3.endswith(".smt2"):
                orchestrator.dump_z3_constraints(dump_z3)
                print(f"Z3 constraints dumped to: {dump_z3}")
            else:
                print("Error: --dump-z3 file must have .smt2 extension")
                return

        if json_output:
            output_json_results(results)
        else:
            print_orchestrator_results(results)
            print_verification_summary(results)

    except ImportError as e:
        if verbose:
            print(f"Z3 verification not available: {e}")
        print("Falling back to basic analysis...")
        verify_file_basic(file_path)
    except Exception as e:
        if json_output:
            print(json.dumps({"error": str(e)}))
        else:
            print(f"✗ Verification failed: {e}")


def verify_project_with_z3(
    project_path: str,
    patterns: List[str],
    excludes: List[str],
    json_output: bool = False,
):
    """Verify all Python files in a project using Z3."""
    path = Path(project_path)

    if not path.exists():
        print(f"Error: Path not found: {project_path}")
        return

    if not json_output:
        print(f"Verifying project: {project_path}")

    try:
        from ..verification import create_engine, VerificationConfig

        config = VerificationConfig(verbose=False)
        engine = create_engine(config)

        # Use the engine's built-in project verification
        project_result = engine.verify_project(project_path, patterns)

        if json_output:
            output_json_project_results(project_result)
        else:
            engine.print_results(project_result)

    except ImportError as e:
        print(f"Z3 verification not available: {e}")
        print("Project verification requires Z3 dependencies")
    except Exception as e:
        if json_output:
            print(json.dumps({"error": str(e)}))
        else:
            print(f"✗ Project verification failed: {e}")


def test_verification_pipeline(
    run_examples: bool = False, test_simple: bool = False, test_complex: bool = False
):
    """Test the verification pipeline with various scenarios."""
    print("Testing Z3 Verification Pipeline")
    print("=" * 35)

    try:
        from ..verification import create_engine, VerificationConfig

        # If no specific tests requested, run all
        if not any([run_examples, test_simple, test_complex]):
            run_examples = test_simple = test_complex = True

        config = VerificationConfig(verbose=True)
        engine = create_engine(config)

        if test_simple:
            print("\n--- Testing Simple Scenarios ---")
            test_simple_scenarios(engine)

        if test_complex:
            print("\n--- Testing Complex Scenarios ---")
            test_complex_scenarios(engine)

        if run_examples:
            print("\n--- Testing Built-in Examples ---")
            test_builtin_examples(engine)

        print("\n✓ Pipeline testing completed")

    except ImportError as e:
        print(f"✗ Z3 verification not available: {e}")
        print("Install dependencies with: pip install z3-solver")
    except Exception as e:
        print(f"✗ Pipeline testing failed: {e}")


def test_simple_scenarios(engine):
    """Test simple verification scenarios."""
    simple_test_cases = [
        (
            "Trivial assertion",
            """
def test_trivial(x: int) -> int:
    assert True
    return x
""",
        ),
        (
            "Basic arithmetic",
            """
def add_positive(x: int, y: int) -> int:
    assert x > 0
    assert y > 0
    result = x + y
    assert result > x
    return result
""",
        ),
        (
            "Absolute value",
            """
def abs_value(x: int) -> int:
    if x >= 0:
        result = x
    else:
        result = -x
    assert result >= 0
    return result
""",
        ),
    ]

    for name, code in simple_test_cases:
        print(f"\nTesting: {name}")
        try:
            results = engine.verify_source_code(
                code, f"test_{name.lower().replace(' ', '_')}.py"
            )
            if results:
                verified = sum(1 for r in results if r.success)
                total = len(results)
                print(f"  ✓ {verified}/{total} functions verified")
            else:
                print("  ⚠ No results (parsing may have failed)")
        except Exception as e:
            print(f"  ✗ Failed: {e}")


def test_complex_scenarios(engine):
    """Test complex verification scenarios."""
    complex_test_cases = [
        (
            "Factorial with invariants",
            """
def factorial(n: int) -> int:
    assert n >= 0
    result = 1
    i = 1
    while i <= n:
        assert result >= 1
        result = result * i
        i = i + 1
    assert result >= 1
    return result
""",
        ),
        (
            "GCD algorithm",
            """
def gcd(a: int, b: int) -> int:
    assert a > 0 and b > 0
    while b != 0:
        temp = b
        b = a % b
        a = temp
    assert a > 0
    return a
""",
        ),
    ]

    for name, code in complex_test_cases:
        print(f"\nTesting: {name}")
        try:
            results = engine.verify_source_code(
                code, f"test_{name.lower().replace(' ', '_')}.py"
            )
            if results:
                verified = sum(
                    1 for r in results if r.success and not r.failed_assertions
                )
                failed = sum(1 for r in results if r.failed_assertions)
                total = len(results)
                print(f"  ✓ {verified} verified, ✗ {failed} failed, {total} total")
            else:
                print("  ⚠ No results")
        except Exception as e:
            print(f"  ✗ Failed: {e}")


def test_builtin_examples(engine):
    """Test built-in example files."""
    example_files = [
        "src/example/absolute_value.py",
        "src/example/absolute_value_logical.py",
    ]

    for example_file in example_files:
        path = Path(example_file)
        if path.exists():
            print(f"\nTesting: {path}")
            try:
                results = engine.verify_file(path)
                if results:
                    verified = sum(
                        1 for r in results if r.success and not r.failed_assertions
                    )
                    total = len(results)
                    print(f"  ✓ {verified}/{total} functions processed")
                else:
                    print("  ⚠ No results")
            except Exception as e:
                print(f"  ✗ Failed: {e}")
        else:
            print(f"\nExample not found: {path}")


def verify_file_basic(file_path: str):
    """Basic file verification without Z3 (fallback)."""
    path = Path(file_path)

    try:
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        import ast

        tree = ast.parse(content, filename=str(path))

        # Count assertions
        assertion_count = len(
            [node for node in ast.walk(tree) if isinstance(node, ast.Assert)]
        )

        print(f"✓ Syntax valid")
        print(f"✓ Found {assertion_count} assertion(s)")
        print("⚠ Z3 verification engine not available")

    except SyntaxError as e:
        print(f"✗ Syntax error: {e}")
    except Exception as e:
        print(f"✗ Error: {e}")


def output_json_results(results):
    """Output verification results in JSON format."""
    json_results = []
    for result in results:
        json_results.append(
            {
                "function_name": result.function_name,
                "file_path": result.file_path,
                "success": result.success,
                "verified_assertions": result.verified_assertions,
                "failed_assertions": result.failed_assertions,
                "counterexamples": result.counterexamples,
                "errors": result.errors,
                "execution_time": result.execution_time,
            }
        )
    print(json.dumps(json_results, indent=2))


def output_json_project_results(project_result):
    """Output project verification results in JSON format."""
    json_result = {
        "total_functions": project_result.total_functions,
        "verified_functions": project_result.verified_functions,
        "failed_functions": project_result.failed_functions,
        "error_functions": project_result.error_functions,
        "success_rate": project_result.success_rate,
        "total_execution_time": project_result.total_execution_time,
        "function_results": [
            {
                "function_name": r.function_name,
                "file_path": r.file_path,
                "success": r.success,
                "verified_assertions": r.verified_assertions,
                "failed_assertions": r.failed_assertions,
                "counterexamples": r.counterexamples,
                "errors": r.errors,
                "execution_time": r.execution_time,
            }
            for r in project_result.function_results
        ],
    }
    print(json.dumps(json_result, indent=2))


def print_orchestrator_results(results):
    """Print verification results from the orchestrator."""
    if not results:
        print("No functions found to verify.")
        return

    for result in results:
        print(f"\n--- Function: {result.function_name} ---")

        if result.errors:
            print("Errors:")
            for error in result.errors:
                print(f"  ✗ {error}")
            continue

        if result.verified_assertions:
            print("Verified assertions:")
            for assertion in result.verified_assertions:
                print(f"  ✓ {assertion}")

        if result.failed_assertions:
            print("Failed assertions:")
            for assertion in result.failed_assertions:
                print(f"  ✗ {assertion}")

        if result.counterexamples:
            print("Counterexamples:")
            for ce in result.counterexamples:
                print(f"  📝 {ce['assertion']}")
                if "counterexample" in ce:
                    for var, value in ce["counterexample"].items():
                        print(f"    {var} = {value}")

        print(f"Execution time: {result.execution_time:.3f}s")


def print_verification_summary(results):
    """Print a summary of verification results."""
    if not results:
        return

    total = len(results)
    verified = sum(1 for r in results if r.success and not r.failed_assertions)
    failed = sum(1 for r in results if r.failed_assertions)
    errors = sum(1 for r in results if r.errors)

    print(f"\n--- Summary ---")
    print(f"Total functions: {total}")
    print(f"Verified: {verified}")
    print(f"Failed assertions: {failed}")
    print(f"Errors: {errors}")
    if total > 0:
        success_rate = verified / total * 100
        print(f"Success rate: {success_rate:.1f}%")


def start_lsp_server():
    """Start the LSP server."""
    print("Starting Axiomander LSP server...")
    try:
        from ..lsp.server import main

        main()
    except ImportError as e:
        print(f"Error: LSP server dependencies not available: {e}")
        print("Install with: pip install axiomander[dev]")


if __name__ == "__main__":
    main()
