"""
Mathematical Functions with Contracts

This example demonstrates mathematical functions with proper preconditions
and postconditions for Z3 verification.

Usage:
  python -m src.axiomander.cli.commands verify src/example/mathematical_contracts.py
"""


def absolute_value(x: int) -> int:
    """Absolute value with mathematical properties."""
    # Precondition: accept any integer
    assert isinstance(x, int), "Input must be an integer"

    if x >= 0:
        result = x
    else:
        result = -x

    # Postconditions: mathematical properties
    assert result >= 0, "Absolute value is always non-negative"
    assert result == x or result == -x, "Result is either x or -x"

    return result


def max_of_two(a: int, b: int) -> int:
    """Maximum function with logical contracts."""
    # Preconditions
    assert isinstance(a, int), "First argument must be integer"
    assert isinstance(b, int), "Second argument must be integer"

    if a >= b:
        result = a
    else:
        result = b

    # Postconditions
    assert result >= a and result >= b, "Result >= both inputs"
    assert result == a or result == b, "Result is one of the inputs"

    return result


def simple_factorial(n: int) -> int:
    """Factorial for small numbers with explicit bounds."""
    # Preconditions
    assert isinstance(n, int), "Input must be integer"
    assert n >= 0, "Factorial undefined for negative numbers"
    assert n <= 5, "Limited to small numbers"

    if n <= 1:
        result = 1
    else:
        result = 1
        i = 2
        while i <= n:
            assert result >= 1, "Factorial grows positively"
            result = result * i
            i = i + 1

    # Postconditions
    assert result >= 1, "Factorial is at least 1"

    return result


def sum_positive_numbers(numbers: list) -> int:
    """Sum only positive numbers from a list."""
    # Preconditions
    assert isinstance(numbers, list), "Input must be a list"

    total = 0
    for num in numbers:
        if isinstance(num, int) and num > 0:
            assert total >= 0, "Running total stays non-negative"
            total = total + num

    # Postconditions
    assert total >= 0, "Sum of positive numbers is non-negative"

    return total


def main_computation():
    """Main function that uses multiple mathematical functions."""
    # Test absolute value
    abs_result = absolute_value(-5)
    assert abs_result == 5, "abs(-5) should be 5"

    # Test maximum
    max_result = max_of_two(3, 7)
    assert max_result == 7, "max(3, 7) should be 7"

    # Test factorial
    fact_result = simple_factorial(4)
    assert fact_result == 24, "4! should be 24"

    # Test sum
    test_list = [1, -2, 3, 4, -1, 2]
    sum_result = sum_positive_numbers(test_list)
    assert sum_result == 10, "Sum of positive numbers should be 10"

    return True


if __name__ == "__main__":
    success = main_computation()
    print("Mathematical contracts example completed!")
