"""
Example: Factorial function with formal verification annotations.

This demonstrates how axiomander can be used to verify mathematical functions
with preconditions, postconditions, and termination measures.
"""


def factorial(n: int) -> int:
    """
    Compute factorial of n with formal verification.

    This function demonstrates several axiomander concepts:
    - Preconditions (input constraints)
    - Termination measures (for recursion)
    - Postconditions (output guarantees)
    """
    # Precondition: input must be non-negative
    assert n >= 0, "Factorial requires non-negative input"

    if n <= 1:
        result = 1
        # Postcondition: result is positive for base case
        assert result >= 1
        return result
    else:
        # Termination measure: n-1 is smaller than n
        assert n - 1 >= 0 and n - 1 < n, "Termination measure"

        # Recursive call
        sub_result = factorial(n - 1)

        # Calculate result
        result = n * sub_result

        # Postcondition: result is positive and at least n
        assert result >= n, "Factorial grows monotonically"
        assert result >= 1, "Factorial is always positive"

        return result


def factorial_iterative(n: int) -> int:
    """
    Iterative factorial with loop invariant.

    Demonstrates:
    - Preconditions
    - Loop invariants
    - Postconditions
    """
    # Precondition
    assert n >= 0, "Factorial requires non-negative input"

    result = 1
    i = 1

    # Loop with invariant
    while i <= n:
        # Loop invariant: result is factorial of (i-1)
        assert result >= 1, "Result remains positive"
        assert i >= 1, "Counter is positive"

        result = result * i
        i = i + 1

    # Postcondition
    assert result >= 1, "Factorial is always positive"
    if n > 0:
        assert result >= n, "Factorial grows monotonically"

    return result


def safe_divide(a: int, b: int) -> float:
    """
    Safe division with precondition checking.

    Demonstrates precondition verification to prevent division by zero.
    """
    # Precondition: divisor must be non-zero
    assert b != 0, "Division by zero not allowed"

    result = a / b

    # Postcondition: if inputs have same sign, result is positive
    if (a > 0 and b > 0) or (a < 0 and b < 0):
        assert result > 0, "Same sign division yields positive result"
    elif (a > 0 and b < 0) or (a < 0 and b > 0):
        assert result < 0, "Different sign division yields negative result"

    return result


def binary_search(arr: list, target: int) -> int:
    """
    Binary search with verification (simplified).

    Note: Full array verification would require more sophisticated
    SMT reasoning about sequences/arrays.
    """
    # Precondition: array length constraint
    assert len(arr) >= 0, "Array length is non-negative"

    if len(arr) == 0:
        return -1

    left = 0
    right = len(arr) - 1

    # Loop with bounds invariant
    while left <= right:
        # Invariant: bounds are valid
        assert 0 <= left <= len(arr), "Left bound valid"
        assert -1 <= right < len(arr), "Right bound valid"
        assert left <= right + 1, "Bounds are reasonable"

        mid = (left + right) // 2

        # Mid-point is within bounds
        assert left <= mid <= right, "Mid-point within bounds"

        if arr[mid] == target:
            # Postcondition: found valid index
            assert 0 <= mid < len(arr), "Returned index is valid"
            return mid
        elif arr[mid] < target:
            left = mid + 1
        else:
            right = mid - 1

    # Not found
    return -1


if __name__ == "__main__":
    print("Axiomander Example: Mathematical Functions with Verification")
    print("=" * 60)

    # Test factorial
    print(f"factorial(5) = {factorial(5)}")
    print(f"factorial_iterative(5) = {factorial_iterative(5)}")

    # Test safe division
    print(f"safe_divide(10, 2) = {safe_divide(10, 2)}")

    # Test binary search
    test_arr = [1, 3, 5, 7, 9, 11]
    print(f"binary_search({test_arr}, 7) = {binary_search(test_arr, 7)}")

    print("\nTo verify these assertions with axiomander:")
    print("axiomander verify factorial_example.py")
