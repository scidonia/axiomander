"""
Wrong Contract Examples for Z3 Verification Testing

This module contains functions with deliberately incorrect preconditions,
postconditions, and implementations to demonstrate how the verification
system detects various types of errors.

These examples are designed to FAIL verification to show:
1. Wrong preconditions (too restrictive or too permissive)
2. Wrong postconditions (incorrect guarantees)
3. Wrong implementations (bugs in the code)

Usage:
  axiomander verify examples/wrong_contracts.py --verbose
"""


def wrong_precondition_too_restrictive(x: int) -> int:
    """
    Function with unnecessarily restrictive precondition.

    The implementation works for all positive integers, but the
    precondition requires x > 100, which is too restrictive.
    """
    # WRONG: Precondition is too restrictive
    assert x > 100, "This should work for any x > 0, not just x > 100"

    # Implementation that actually works for any positive x
    if x > 0:
        result = x * 2
    else:
        result = 0

    # Postcondition is correct
    assert result >= 0, "Result should be non-negative"
    return result


def wrong_precondition_too_permissive(x: int) -> int:
    """
    Function with precondition that's too permissive.

    The implementation will fail for negative numbers, but the
    precondition allows them.
    """
    # WRONG: Precondition allows negative numbers but implementation doesn't handle them
    assert isinstance(x, int), "Should also require x >= 0"

    # Implementation that fails for negative numbers
    result = x * x  # This is fine
    result = result // x  # This will give wrong result for negative x!

    # Postcondition expects positive result
    assert result > 0, "Result should be positive (but fails for negative x)"
    return result


def wrong_postcondition_too_weak(a: int, b: int) -> int:
    """
    Function with postcondition that's too weak.

    The function computes max(a, b) but the postcondition
    only checks that result >= 0, missing the actual max property.
    """
    # Precondition is correct
    assert a >= 0 and b >= 0, "Inputs must be non-negative"

    # Implementation is correct
    if a >= b:
        result = a
    else:
        result = b

    # WRONG: Postcondition is too weak - should verify max property
    assert result >= 0, (
        "Should also check result >= a and result >= b and (result == a or result == b)"
    )
    return result


def wrong_postcondition_too_strong(x: int) -> int:
    """
    Function with postcondition that's too strong.

    The function adds 1 to input, but postcondition claims
    the result is always > input + 10, which is impossible.
    """
    # Precondition is correct
    assert x >= 0, "Input must be non-negative"

    # Implementation is correct
    result = x + 1

    # WRONG: Postcondition is impossible to satisfy
    assert result > x + 10, "This is impossible! We only added 1, not 10+"
    return result


def wrong_postcondition_contradictory(x: int) -> int:
    """
    Function with contradictory postconditions.

    The postconditions contradict each other.
    """
    # Precondition is correct
    assert x > 0, "Input must be positive"

    # Implementation is correct
    result = x * 2

    # WRONG: These postconditions contradict each other
    assert result > x, "Result is greater than input (correct)"
    assert result < x, "Result is less than input (contradicts the above!)"
    return result


def wrong_implementation_off_by_one(n: int) -> int:
    """
    Function with correct contracts but wrong implementation.

    Should compute n!, but has an off-by-one error.
    """
    # Precondition is correct
    assert n >= 0, "Factorial undefined for negative numbers"
    assert n <= 5, "Keep small for verification"

    # WRONG: Implementation has off-by-one error
    if n <= 1:
        result = 1  # This is correct
    else:
        result = 1
        # BUG: Should be range(1, n + 1), but we use range(1, n)
        for i in range(1, n):  # Missing the last multiplication!
            result = result * i

    # Postconditions are correct but will fail due to implementation bug
    assert result >= 1, "Factorial is at least 1"
    if n == 2:
        assert result == 2, "2! should be 2 (but implementation gives 1)"
    elif n == 3:
        assert result == 6, "3! should be 6 (but implementation gives 2)"
    elif n == 4:
        assert result == 24, "4! should be 24 (but implementation gives 6)"

    return result


def wrong_implementation_wrong_logic(a: int, b: int, c: int) -> int:
    """
    Function with correct contracts but completely wrong implementation.

    Should find minimum of three numbers, but implements maximum instead.
    """
    # Preconditions are correct
    assert a >= 0 and b >= 0 and c >= 0, "All inputs must be non-negative"
    assert a <= 100 and b <= 100 and c <= 100, "Keep inputs bounded"

    # WRONG: Implementation finds MAX instead of MIN
    if a >= b and a >= c:
        result = a
    elif b >= c:
        result = b
    else:
        result = c

    # Postconditions are for MINIMUM but implementation does MAXIMUM
    assert result <= a and result <= b and result <= c, "Result should be <= all inputs"
    assert result == a or result == b or result == c, (
        "Result should be one of the inputs"
    )

    return result


def wrong_implementation_infinite_loop_risk(n: int) -> int:
    """
    Function with implementation that risks infinite loop.

    Correct contracts, but buggy loop implementation.
    """
    # Precondition is correct
    assert n > 0, "Input must be positive"
    assert n <= 10, "Keep small to avoid infinite loops"

    # WRONG: Implementation has infinite loop risk
    result = n
    counter = 0

    # BUG: This loop condition might never terminate
    while result > 1:
        result = result - 1
        # BUG: Forgot to increment counter, or wrong termination condition
        if counter > 100:  # Safety valve, but shouldn't be needed
            break
        # counter += 1  # BUG: This line is missing!

    # Postcondition expects reasonable behavior
    assert result == 1, "Should decrement to 1"
    return result


def wrong_implementation_division_by_zero(x: int, y: int) -> float:
    """
    Function that doesn't properly handle division by zero.

    Precondition allows y=0, but implementation will crash.
    """
    # WRONG: Precondition should require y != 0
    assert x >= 0, "First input must be non-negative"
    assert y >= 0, "Second input must be non-negative"  # Should be y > 0!

    # WRONG: Implementation doesn't handle y=0 case
    result = x / y  # Will crash if y=0!

    # Postcondition is reasonable but won't be reached if y=0
    assert result >= 0, "Result should be non-negative"
    return result


def wrong_implementation_type_error(items: list) -> int:
    """
    Function with type handling bug.

    Claims to handle mixed types but implementation assumes all integers.
    """
    # Precondition allows mixed types
    assert isinstance(items, list), "Input must be a list"
    assert len(items) > 0, "List must not be empty"

    # WRONG: Implementation assumes all items are integers
    total = 0
    for item in items:
        # BUG: This will crash if item is not a number
        total = total + item  # No type checking!

    # Postcondition is reasonable
    assert isinstance(total, int), "Total should be an integer"
    return total


# Test functions that demonstrate the errors
def test_wrong_examples():
    """Test function that shows how the wrong examples fail."""
    try:
        # This will fail verification due to wrong precondition
        result1 = wrong_precondition_too_restrictive(
            50
        )  # Should work but precondition forbids it
    except AssertionError as e:
        print(f"Expected failure: {e}")

    try:
        # This will fail due to wrong implementation
        result2 = wrong_implementation_off_by_one(3)  # Will compute 2 instead of 6
    except AssertionError as e:
        print(f"Expected failure: {e}")

    try:
        # This will fail due to contradictory postconditions
        result3 = wrong_postcondition_contradictory(5)
    except AssertionError as e:
        print(f"Expected failure: {e}")


if __name__ == "__main__":
    print("Testing wrong contract examples...")
    test_wrong_examples()
    print("Wrong contract examples completed!")
