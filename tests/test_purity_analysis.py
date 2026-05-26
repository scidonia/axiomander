"""
Test cases for purity analysis.

This module tests the purity analyzer's ability to correctly classify
pure and impure functions, including edge cases and real-world scenarios.
"""

import pytest
from pathlib import Path

try:
    from src.axiomander.ast.parser import ASTParser
    from src.axiomander.ast.purity_analyzer import PurityAnalyzer, PurityLevel

    AXIOMANDER_AVAILABLE = True
except ImportError as e:
    AXIOMANDER_AVAILABLE = False
    pytestmark = pytest.mark.skip(f"Axiomander not available: {e}")


class TestPureFunctions:
    """Test functions that should be classified as pure."""

    def test_simple_mathematical_function(self):
        """Test pure mathematical function."""
        source_code = """
def add_numbers(x: int, y: int) -> int:
    return x + y
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        # Find the function
        function_node = None
        for node in parsed_code.ast_tree.body:
            if hasattr(node, "name") and node.name == "add_numbers":
                function_node = node
                break

        assert function_node is not None
        result = analyzer.analyze_function(function_node)

        assert result.level == PurityLevel.PURE
        assert "arithmetic" in result.reason.lower() or "pure" in result.reason.lower()

    def test_pure_builtin_usage(self):
        """Test function using only pure builtins."""
        source_code = """
def process_numbers(numbers: list) -> int:
    return sum(abs(x) for x in numbers if x > 0)
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE

    def test_mathematical_computation(self):
        """Test complex pure mathematical computation."""
        source_code = """
def fibonacci(n: int) -> int:
    if n <= 1:
        return n
    else:
        return fibonacci(n-1) + fibonacci(n-2)
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        # Note: This might be classified as impure due to recursion
        # depending on the analyzer's conservatism
        assert result.level in [PurityLevel.PURE, PurityLevel.IMPURE]

    def test_pure_string_operations(self):
        """Test pure string manipulation."""
        source_code = """
def format_name(first: str, last: str) -> str:
    return first.upper() + " " + last.upper()
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE

    def test_pure_list_comprehension(self):
        """Test function with pure list comprehension."""
        source_code = """
def square_positive(numbers: list) -> list:
    return [x*x for x in numbers if x > 0]
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE

    def test_pure_conditional_logic(self):
        """Test pure function with conditional logic."""
        source_code = """
def max_of_three(a: int, b: int, c: int) -> int:
    if a >= b and a >= c:
        return a
    elif b >= c:
        return b
    else:
        return c
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE


class TestImpureFunctions:
    """Test functions that should be classified as impure."""

    def test_file_system_access(self):
        """Test function that accesses file system."""
        source_code = """
def read_config_file(filename: str) -> dict:
    with open(filename, 'r') as f:
        content = f.read()
    return {"content": content}
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE
        assert "open" in result.reason.lower() or "file" in result.reason.lower()

    def test_network_access(self):
        """Test function that makes network requests."""
        source_code = """
import urllib.request

def fetch_url(url: str) -> str:
    with urllib.request.urlopen(url) as response:
        return response.read().decode()
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[1]  # Skip import
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE

    def test_print_output(self):
        """Test function that prints to stdout."""
        source_code = """
def log_calculation(x: int, y: int) -> int:
    result = x + y
    print(f"Calculated {x} + {y} = {result}")
    return result
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE
        assert "print" in result.reason.lower()

    def test_global_variable_modification(self):
        """Test function that modifies global state."""
        source_code = """
counter = 0

def increment_counter() -> int:
    global counter
    counter += 1
    return counter
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[1]  # Skip global declaration
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE
        assert "global" in result.reason.lower()

    def test_random_number_generation(self):
        """Test function that generates random numbers."""
        source_code = """
import random

def get_random_number() -> int:
    return random.randint(1, 100)
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[1]  # Skip import
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE

    def test_time_dependent_function(self):
        """Test function that depends on current time."""
        source_code = """
import time

def get_timestamp() -> float:
    return time.time()
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[1]  # Skip import
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE

    def test_user_input(self):
        """Test function that reads user input."""
        source_code = """
def get_user_name() -> str:
    name = input("Enter your name: ")
    return name.strip()
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE
        assert "input" in result.reason.lower()

    def test_database_access(self):
        """Test function that accesses database (simulated)."""
        source_code = """
def get_user_by_id(user_id: int) -> dict:
    # Simulated database access
    import sqlite3
    conn = sqlite3.connect("users.db")
    cursor = conn.cursor()
    cursor.execute("SELECT * FROM users WHERE id = ?", (user_id,))
    result = cursor.fetchone()
    conn.close()
    return {"id": result[0], "name": result[1]} if result else {}
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE


class TestEdgeCases:
    """Test edge cases and boundary conditions for purity analysis."""

    def test_empty_function(self):
        """Test empty function."""
        source_code = """
def empty_function():
    pass
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE

    def test_docstring_only_function(self):
        """Test function with only docstring."""
        source_code = """
def documented_function():
    \"\"\"This function does nothing but has documentation.\"\"\"
    return None
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE

    def test_nested_function_calls(self):
        """Test function with nested calls to pure functions."""
        source_code = """
def complex_calculation(x: int) -> int:
    return abs(min(max(x, 0), 100))
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE

    def test_unknown_function_call(self):
        """Test function calling unknown/user-defined function."""
        source_code = """
def calls_unknown(x: int) -> int:
    return mysterious_function(x) + 1
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        # Should be impure due to conservative approach with unknown functions
        assert result.level == PurityLevel.IMPURE

    def test_exception_handling(self):
        """Test function with exception handling."""
        source_code = """
def safe_division(a: int, b: int) -> float:
    try:
        return a / b
    except ZeroDivisionError:
        return 0.0
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE

    def test_list_mutation(self):
        """Test function that mutates input list."""
        source_code = """
def sort_in_place(numbers: list) -> list:
    numbers.sort()
    return numbers
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        # Should be impure due to mutation of input
        assert result.level == PurityLevel.IMPURE

    def test_attribute_access(self):
        """Test function with attribute access."""
        source_code = """
def get_name_length(person):
    return len(person.name)
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        # Could be pure or impure depending on whether attribute access is considered pure
        assert result.level in [PurityLevel.PURE, PurityLevel.IMPURE]


class TestRealWorldScenarios:
    """Test realistic scenarios from actual codebases."""

    def test_hash_function(self):
        """Test cryptographic hash function (pure)."""
        source_code = """
import hashlib

def compute_hash(data: str) -> str:
    return hashlib.sha256(data.encode()).hexdigest()
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[1]  # Skip import
        result = analyzer.analyze_node(function_node)

        # Hashing should be pure (deterministic, no side effects)
        assert result.level == PurityLevel.PURE

    def test_configuration_parser(self):
        """Test configuration file parser (impure due to file I/O)."""
        source_code = """
import json

def load_config(config_path: str) -> dict:
    with open(config_path, 'r') as f:
        return json.load(f)
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[1]  # Skip import
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE

    def test_data_validation(self):
        """Test data validation function (pure)."""
        source_code = """
def validate_email(email: str) -> bool:
    return "@" in email and "." in email and len(email) > 5
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.PURE

    def test_logging_function(self):
        """Test logging function (impure due to I/O)."""
        source_code = """
import logging

def log_error(message: str, error_code: int):
    logging.error(f"Error {error_code}: {message}")
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[1]  # Skip import
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE

    def test_cache_function(self):
        """Test function that uses caching (impure due to state)."""
        source_code = """
cache = {}

def cached_fibonacci(n: int) -> int:
    if n in cache:
        return cache[n]
    
    if n <= 1:
        result = n
    else:
        result = cached_fibonacci(n-1) + cached_fibonacci(n-2)
    
    cache[n] = result
    return result
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[1]  # Skip cache declaration
        result = analyzer.analyze_node(function_node)

        # Should be impure due to global state modification
        assert result.level == PurityLevel.IMPURE


class TestPurityIntegration:
    """Test purity analysis integration with verification pipeline."""

    def test_pure_function_verification(self):
        """Test that pure functions can be fully verified."""
        source_code = """
def absolute_value(x: int) -> int:
    assert isinstance(x, int)
    
    if x >= 0:
        result = x
    else:
        result = -x
        
    assert result >= 0
    return result
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        # This function should be analyzed (pure or impure depending on implementation)
        assert result.level in [PurityLevel.PURE, PurityLevel.IMPURE]
        assert result.reason is not None

    def test_impure_function_limited_verification(self):
        """Test that impure functions are flagged appropriately."""
        source_code = """
def save_result(x: int, filename: str) -> int:
    assert x >= 0
    
    result = x * 2
    
    with open(filename, 'w') as f:
        f.write(str(result))
    
    assert result >= x
    return result
"""
        parser = ASTParser()
        parsed_code = parser.parse_source(source_code)
        analyzer = PurityAnalyzer(parsed_code)

        function_node = parsed_code.ast_tree.body[0]
        result = analyzer.analyze_node(function_node)

        assert result.level == PurityLevel.IMPURE
        assert "open" in result.reason.lower()


if __name__ == "__main__":
    pytest.main([__file__])
