"""
WPC Conditional Testing Examples

This file contains two well-crafted conditional examples specifically designed
to test Weakest Precondition Calculation (WPC) on conditional statements.

These examples are designed to:
1. Successfully verify with the current Z3 verification pipeline
2. Demonstrate how WPC handles different execution paths
3. Show path-dependent postconditions and invariants

The examples progress from simple to more complex conditional logic.

Usage:
  axiomander verify examples/wpc_conditional_tests.py --verbose
"""


def wpc_simple_conditional(x: int) -> int:
    """
    WPC Test #1: Simple conditional with path-dependent postconditions

    This tests basic WPC calculation where:
    - The result depends on a simple condition (x >= 0)
    - Each path has different but verifiable behavior
    - Postconditions are carefully crafted to be provable

    WPC Challenge: The system must calculate the weakest precondition
    that ensures both paths satisfy their respective postconditions.
    """
    # Preconditions - keep simple for reliable verification
    assert x >= -10 and x <= 10, "x must be in bounded range"

    if x >= 0:
        # Path 1: Non-negative case - return doubled value
        result = x * 2
    else:
        # Path 2: Negative case - return absolute value
        result = -x

    # Postconditions that should verify for both paths
    assert result >= 0, "Result is always non-negative"

    # Path-specific postconditions (these test WPC path handling)
    if x >= 0:
        assert result == x * 2, "Non-negative: result = x * 2"
        assert result >= x, "Non-negative: result ≥ x (since x ≥ 0)"
    else:
        assert result == -x, "Negative: result = -x (absolute value)"
        assert result > 0, "Negative: result > 0 (since x < 0)"

    return result


def wpc_nested_conditional(a: int, b: int) -> int:
    """
    WPC Test #2: Nested conditionals with multiple execution paths

    This tests more complex WPC calculation where:
    - There are four distinct execution paths (2x2 nested conditions)
    - Each path has its own computation and constraints
    - The system must verify properties that hold across all paths

    WPC Challenge: The system must handle the combinatorial explosion
    of paths while maintaining correctness guarantees.
    """
    # Preconditions - bounded inputs for reliable verification
    assert a >= -5 and a <= 5, "a must be bounded"
    assert b >= -5 and b <= 5, "b must be bounded"

    if a > 0:
        if b > 0:
            # Path 1: Both positive - add them
            result = a + b
        else:
            # Path 2: a positive, b non-positive - use a
            result = a
    else:
        if b > 0:
            # Path 3: a non-positive, b positive - use b
            result = b
        else:
            # Path 4: Both non-positive - use 0
            result = 0

    # Universal postconditions (must hold for all paths)
    assert result >= 0, "Result is always non-negative"
    assert result <= 10, "Result is always bounded above"

    # Path-specific verification (tests WPC path-dependent reasoning)
    if a > 0 and b > 0:
        assert result == a + b, "Path 1: sum of both positive values"
        assert result > 0, "Path 1: sum is positive"
    elif a > 0 and b <= 0:
        assert result == a, "Path 2: use positive a"
        assert result > 0, "Path 2: result is positive"
    elif a <= 0 and b > 0:
        assert result == b, "Path 3: use positive b"
        assert result > 0, "Path 3: result is positive"
    else:
        assert result == 0, "Path 4: both non-positive gives 0"
        assert result == 0, "Path 4: result is exactly 0"

    return result


if __name__ == "__main__":
    print("Testing WPC conditional examples...")

    # Test simple conditional with different values
    print("Testing wpc_simple_conditional:")
    test_values = [5, -3, 0, 1, -1]
    for val in test_values:
        result = wpc_simple_conditional(val)
        print(f"  wpc_simple_conditional({val}) = {result}")

    print("\nTesting wpc_nested_conditional:")
    # Test nested conditional with different combinations
    test_pairs = [(2, 3), (-1, 4), (1, -2), (-1, -1), (0, 0)]
    for a, b in test_pairs:
        result = wpc_nested_conditional(a, b)
        print(f"  wpc_nested_conditional({a}, {b}) = {result}")

    print("\nWPC conditional tests completed successfully!")
    print("These examples are designed to test weakest precondition")
    print("calculation on conditional statements with multiple execution paths.")
