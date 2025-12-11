"""
Complex contract examples demonstrating advanced formal verification patterns.

This module contains functions with more sophisticated contracts involving:
- Conditional logic and multiple branches
- Mathematical properties and invariants
- Range constraints and boundary conditions
- Error handling with preconditions
"""


def conditional_max(a: int, b: int, c: int) -> int:
    """
    Returns the maximum of three integers using conditional logic.

    Demonstrates verification of branching control flow.
    """
    # Preconditions: all inputs are valid integers (automatic)
    assert a is not None
    assert b is not None
    assert c is not None

    if a >= b and a >= c:
        result = a
    elif b >= c:
        result = b
    else:
        result = c

    # Postconditions: result is the maximum
    assert result >= a
    assert result >= b
    assert result >= c
    # At least one input equals the result
    assert result == a or result == b or result == c

    return result


def fibonacci_iterative(n: int) -> int:
    """
    Computes Fibonacci number iteratively with contracts.

    Demonstrates verification of iterative algorithms and mathematical properties.
    """
    # Preconditions
    assert n >= 0
    assert n <= 20  # Keep it small for tractable verification

    if n <= 1:
        result = n
    else:
        prev, curr = 0, 1
        for i in range(2, n + 1):
            next_fib = prev + curr
            prev, curr = curr, next_fib
        result = curr

    # Postconditions: basic properties of Fibonacci numbers
    assert result >= 0  # Fibonacci numbers are non-negative

    if n == 0:
        assert result == 0
    elif n == 1:
        assert result == 1
    else:
        assert result > 0  # Positive for n > 0

    return result


def safe_division(numerator: int, denominator: int) -> float:
    """
    Performs division with error checking and contracts.

    Demonstrates verification with error conditions and floating-point results.
    """
    # Preconditions
    assert denominator != 0  # Division by zero guard
    assert numerator >= -1000 and numerator <= 1000  # Reasonable bounds
    assert denominator >= -1000 and denominator <= 1000  # Reasonable bounds

    result = numerator / denominator

    # Postconditions
    if denominator > 0:
        if numerator >= 0:
            assert result >= 0
        else:
            assert result <= 0
    else:  # denominator < 0
        if numerator >= 0:
            assert result <= 0
        else:
            assert result >= 0

    # Magnitude relationships
    if abs(numerator) >= abs(denominator):
        assert abs(result) >= 1.0

    return result


def factorial_with_contracts(n: int) -> int:
    """
    Computes factorial with comprehensive contracts.

    Demonstrates verification of mathematical functions with strong invariants.
    """
    # Preconditions
    assert n >= 0
    assert n <= 10  # Keep small for verification tractability

    if n == 0 or n == 1:
        result = 1
    else:
        result = 1
        for i in range(1, n + 1):
            result = result * i

    # Postconditions: mathematical properties of factorial
    assert result >= 1  # Factorial is always positive

    if n == 0:
        assert result == 1
    elif n == 1:
        assert result == 1
    elif n == 2:
        assert result == 2
    elif n == 3:
        assert result == 6

    # Growth property: n! >= n for n >= 1
    if n >= 1:
        assert result >= n

    return result


def clamp_value(value: int, min_val: int, max_val: int) -> int:
    """
    Clamps a value within specified bounds.

    Demonstrates verification of range constraints and boundary conditions.
    """
    # Preconditions
    assert min_val <= max_val  # Valid range
    assert min_val >= -100 and min_val <= 100  # Reasonable bounds
    assert max_val >= -100 and max_val <= 100  # Reasonable bounds
    assert value >= -1000 and value <= 1000  # Input bounds

    if value < min_val:
        result = min_val
    elif value > max_val:
        result = max_val
    else:
        result = value

    # Postconditions
    assert result >= min_val  # Result is within bounds
    assert result <= max_val

    # Relationship to input
    if min_val <= value <= max_val:
        assert result == value  # No clamping needed

    return result


def euclidean_gcd(a: int, b: int) -> int:
    """
    Computes GCD using Euclidean algorithm with contracts.

    Demonstrates verification of classic algorithms with loop invariants.
    """
    # Preconditions
    assert a > 0
    assert b > 0
    assert a <= 100 and b <= 100  # Keep bounded for verification

    # Make copies to preserve originals for postcondition checking
    x, y = a, b

    while y != 0:
        remainder = x % y
        x, y = y, remainder

    result = x

    # Postconditions
    assert result > 0  # GCD is always positive
    assert result <= a  # GCD can't be larger than inputs
    assert result <= b

    # GCD divides both inputs
    assert a % result == 0
    assert b % result == 0

    return result


def triangle_type(a: int, b: int, c: int) -> str:
    """
    Determines triangle type based on side lengths.

    Demonstrates verification with string results and multiple conditions.
    """
    # Preconditions: valid triangle sides
    assert a > 0 and b > 0 and c > 0  # Positive lengths
    assert a + b > c  # Triangle inequality
    assert a + c > b
    assert b + c > a
    assert a <= 100 and b <= 100 and c <= 100  # Reasonable bounds

    # Determine triangle type
    if a == b == c:
        result = "equilateral"
    elif a == b or b == c or a == c:
        result = "isosceles"
    else:
        result = "scalene"

    # Postconditions: verify the classification is correct
    if result == "equilateral":
        assert a == b and b == c  # All sides equal
    elif result == "isosceles":
        assert (
            (a == b and a != c) or (b == c and b != a) or (a == c and a != b)
        )  # Exactly two sides equal
    else:  # scalene
        assert a != b and b != c and a != c  # All sides different

    return result
