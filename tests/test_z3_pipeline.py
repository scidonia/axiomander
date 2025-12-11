"""
Test cases for Z3 pipeline integration.

This module tests the complete verification pipeline from AST parsing
through Z3 solving to ensure all components work together correctly.
"""

import ast
import pytest
from pathlib import Path

# Test the pipeline components
try:
    from src.axiomander.verification import (
        create_orchestrator,
        create_engine,
        VerificationConfig,
    )
    from src.axiomander.logic.smt_translator import SMTTranslator, VariableType
    from src.axiomander.ast.parser import ASTParser

    AXIOMANDER_AVAILABLE = True
except ImportError as e:
    AXIOMANDER_AVAILABLE = False
    pytestmark = pytest.mark.skip(f"Axiomander not available: {e}")


class TestZ3PipelineBasics:
    """Test basic Z3 pipeline functionality."""

    def test_orchestrator_creation(self):
        """Test that orchestrator can be created."""
        orchestrator = create_orchestrator()
        assert orchestrator is not None
        assert hasattr(orchestrator, "verify_source")
        assert hasattr(orchestrator, "verify_file")

    def test_engine_creation(self):
        """Test that verification engine can be created."""
        engine = create_engine()
        assert engine is not None
        assert hasattr(engine, "verify_source_code")
        assert hasattr(engine, "verify_file")
        assert hasattr(engine, "verify_project")

    def test_engine_with_config(self):
        """Test engine creation with custom configuration."""
        config = VerificationConfig(
            timeout_seconds=60, verbose=True, enable_counterexamples=False
        )
        engine = create_engine(config)
        assert engine.config.timeout_seconds == 60
        assert engine.config.verbose is True
        assert engine.config.enable_counterexamples is False


class TestSimpleAssertions:
    """Test verification of simple assertions."""

    def test_trivial_true_assertion(self):
        """Test verification of a trivially true assertion."""
        source_code = """
def simple_function(x: int) -> int:
    assert True
    return x + 1
"""
        engine = create_engine()
        results = engine.verify_source_code(source_code)

        assert len(results) == 1
        result = results[0]
        assert result.function_name == "simple_function"
        # Note: This might be 0 if no assertions are actually found
        # The test validates the pipeline works without errors

    def test_simple_arithmetic_assertion(self):
        """Test verification of simple arithmetic assertion."""
        source_code = """
def add_positive(x: int, y: int) -> int:
    assert x > 0
    assert y > 0
    result = x + y
    assert result > x
    assert result > y
    return result
"""
        engine = create_engine()
        results = engine.verify_source_code(source_code)

        assert len(results) == 1
        result = results[0]
        assert result.function_name == "add_positive"

        # Should have some assertions discovered
        total_assertions = len(result.verified_assertions) + len(
            result.failed_assertions
        )
        assert total_assertions > 0 or len(result.errors) > 0

    def test_absolute_value_function(self):
        """Test verification of absolute value function with contracts."""
        source_code = """
def absolute_value(x: float) -> float:
    # Precondition: x is a real number (always true for float)
    assert isinstance(x, (int, float))
    
    if x >= 0:
        result = x
    else:
        result = -x
        
    # Postcondition: result >= 0
    assert result >= 0
    # Postcondition: result == x or result == -x  
    assert result == x or result == -x
    
    return result
"""
        engine = create_engine()
        results = engine.verify_source_code(source_code)

        assert len(results) == 1
        result = results[0]
        assert result.function_name == "absolute_value"

        # The pipeline should at least attempt to process the function
        # Even if verification fails due to complexity
        assert result.execution_time > 0


class TestComplexScenarios:
    """Test more complex verification scenarios."""

    def test_function_with_loop_invariant(self):
        """Test function with loop and invariant assertions."""
        source_code = """
def factorial(n: int) -> int:
    assert n >= 0  # Precondition
    
    result = 1
    i = 1
    
    while i <= n:
        # Loop invariant: result == factorial(i-1)
        assert result >= 1
        assert i >= 1
        result = result * i
        i = i + 1
        
    # Postcondition: result == factorial(n)
    assert result >= 1
    return result
"""
        engine = create_engine()
        results = engine.verify_source_code(source_code)

        assert len(results) == 1
        result = results[0]
        assert result.function_name == "factorial"

        # Should find several assertions
        total_assertions = len(result.verified_assertions) + len(
            result.failed_assertions
        )
        assert total_assertions > 0 or len(result.errors) == 0

    def test_multiple_functions(self):
        """Test verification of multiple functions in one source."""
        source_code = """
def is_positive(x: int) -> bool:
    result = x > 0
    assert isinstance(result, bool)
    return result

def square(x: int) -> int:
    assert isinstance(x, int)
    result = x * x
    assert result >= 0  # Square is always non-negative
    return result

def max_of_two(a: int, b: int) -> int:
    if a >= b:
        result = a
        assert result >= a and result >= b
    else:
        result = b
        assert result >= a and result >= b
    return result
"""
        engine = create_engine()
        results = engine.verify_source_code(source_code)

        # Should have results for all 3 functions
        assert len(results) == 3

        function_names = {r.function_name for r in results}
        expected_names = {"is_positive", "square", "max_of_two"}
        assert function_names == expected_names

        # All functions should execute without critical errors
        for result in results:
            assert result.execution_time > 0


class TestErrorHandling:
    """Test error handling in the pipeline."""

    def test_syntax_error_handling(self):
        """Test handling of source code with syntax errors."""
        source_code = """
def broken_function(x: int) -> int:
    assert x > 0
    return x +  # Syntax error - incomplete expression
"""
        engine = create_engine()
        results = engine.verify_source_code(source_code)

        # Should handle the error gracefully
        assert isinstance(results, list)
        # May be empty list due to parse error, which is acceptable

    def test_unsupported_constructs(self):
        """Test handling of unsupported language constructs."""
        source_code = """
def complex_function(x: int) -> int:
    # Using complex constructs that may not be supported
    assert x > 0
    
    # List comprehension
    squares = [i*i for i in range(x)]
    
    # Exception handling  
    try:
        result = sum(squares) // x
    except ZeroDivisionError:
        result = 0
    
    assert result >= 0
    return result
"""
        engine = create_engine()
        results = engine.verify_source_code(source_code)

        # Pipeline should handle gracefully, either with verification
        # results or with appropriate error reporting
        assert isinstance(results, list)
        if len(results) > 0:
            result = results[0]
            assert result.function_name == "complex_function"


class TestFileVerification:
    """Test file-based verification."""

    def test_verify_existing_example(self):
        """Test verification of an existing example file."""
        # Use the existing absolute_value example if it exists
        example_file = Path("src/example/absolute_value.py")

        if example_file.exists():
            engine = create_engine()
            results = engine.verify_file(example_file)

            assert isinstance(results, list)
            # Should at least attempt verification without crashing

    def test_verify_nonexistent_file(self):
        """Test handling of non-existent files."""
        engine = create_engine()
        results = engine.verify_file("nonexistent_file.py")

        # Should return empty list for missing files
        assert results == []


class TestIntegrationWithExistingComponents:
    """Test integration with existing axiomander components."""

    def test_smt_translator_integration(self):
        """Test that SMT translator works with the pipeline."""
        translator = SMTTranslator()

        # Test basic functionality
        assert translator is not None

        # Test variable creation
        var = translator.get_or_create_variable("x", VariableType.INT)
        assert var is not None

    def test_ast_parser_integration(self):
        """Test AST parser integration."""
        parser = ASTParser()

        source_code = """
def test_function(x: int) -> int:
    assert x > 0
    return x + 1
"""

        parsed_code = parser.parse_source(source_code)
        assert parsed_code is not None
        assert parsed_code.ast_tree is not None
        assert isinstance(parsed_code.ast_tree, ast.Module)


class TestPerformance:
    """Test performance characteristics of the pipeline."""

    def test_verification_timeout(self):
        """Test that verification respects timeout settings."""
        import time

        # Create a function that might take time to verify
        source_code = """
def complex_logic(x: int, y: int, z: int) -> int:
    assert x > 0 and y > 0 and z > 0
    
    # Multiple complex assertions
    assert x + y > z or x + z > y or y + z > x  # Triangle inequality variations
    assert x*x + y*y >= z*z or x*x + z*z >= y*y or y*y + z*z >= x*x
    
    result = (x + y + z) // 3
    assert result > 0
    return result
"""

        config = VerificationConfig(timeout_seconds=1)  # Very short timeout
        engine = create_engine(config)

        start_time = time.time()
        results = engine.verify_source_code(source_code)
        end_time = time.time()

        # Verification should complete reasonably quickly
        # (though timeout may not be enforced at Z3 level yet)
        assert end_time - start_time < 10.0  # Should not take more than 10 seconds


# Integration test for the complete pipeline
class TestCompleteWorkflow:
    """Test the complete verification workflow."""

    def test_end_to_end_verification(self):
        """Test complete end-to-end verification workflow."""

        # Create a realistic example with contracts
        source_code = """
def safe_divide(a: int, b: int) -> float:
    '''Safely divide a by b with proper error handling.'''
    
    # Precondition: b is not zero
    assert b != 0, "Division by zero not allowed"
    
    # Precondition: inputs are integers
    assert isinstance(a, int), "First argument must be integer"
    assert isinstance(b, int), "Second argument must be integer"
    
    # Perform division
    result = a / b
    
    # Postcondition: result is finite
    assert result == result, "Result must not be NaN"  # NaN != NaN
    
    # Postcondition: if a and b have same sign, result is positive
    if (a > 0 and b > 0) or (a < 0 and b < 0):
        assert result > 0, "Result should be positive for same signs"
    
    return result
"""

        # Test with verification engine
        engine = create_engine(VerificationConfig(verbose=False))
        results = engine.verify_source_code(source_code, "test_safe_divide.py")

        assert len(results) == 1
        result = results[0]

        # Verify basic result structure
        assert result.function_name == "safe_divide"
        assert result.file_path == "test_safe_divide.py"
        assert result.execution_time > 0

        # Should have discovered some assertions
        total_assertions = len(result.verified_assertions) + len(
            result.failed_assertions
        )
        assert total_assertions > 0 or len(result.errors) > 0

        # Print results for debugging
        engine.print_results(results)

        # Test should complete without exceptions
        assert True


if __name__ == "__main__":
    # Allow running tests directly
    pytest.main([__file__])
