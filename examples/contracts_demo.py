"""
Contract Demonstration for Z3 Verification

This module demonstrates how to write functions with proper preconditions,
postconditions, and invariants that can be verified using the Z3 pipeline.

Usage: axiomander verify src/example/contracts_demo.py
"""


def safe_sqrt_approximation(x: int) -> int:
    """
    Integer square root approximation using Newton's method.
    Demonstrates preconditions, postconditions, and loop invariants.
    """
    # Preconditions
    assert isinstance(x, int), "Input must be an integer"
    assert x >= 0, "Cannot compute square root of negative number"

    # Special cases
    if x == 0 or x == 1:
        return x

    # Newton's method for integer square root
    guess = x
    while True:
        # Loop invariant: guess > 0 and we're approaching sqrt(x)
        assert guess > 0, "Guess must remain positive"

        better_guess = (guess + x // guess) // 2

        if better_guess >= guess:
            break

        guess = better_guess

        # Loop invariant: guess is decreasing and bounded
        assert guess > 0, "Guess remains positive after update"

    result = guess

    # Postconditions
    assert result >= 0, "Square root result is non-negative"
    assert result * result <= x, "Result squared doesn't exceed input"
    assert (result + 1) * (result + 1) > x, "Result is the largest such integer"

    return result


def bounded_factorial(n: int) -> int:
    """
    Factorial with explicit bounds checking.
    Demonstrates range preconditions and growth postconditions.
    """
    # Preconditions
    assert isinstance(n, int), "Input must be an integer"
    assert n >= 0, "Factorial undefined for negative numbers"
    assert n <= 10, "Factorial limited to prevent overflow"

    if n <= 1:
        result = 1
    else:
        result = 1
        i = 2

        while i <= n:
            # Loop invariant: result = factorial(i-1)
            assert result >= 1, "Factorial is always positive"
            assert i >= 2, "Counter starts at 2"
            assert i <= n + 1, "Counter doesn't exceed bound"

            result = result * i
            i = i + 1

            # Post-increment invariant
            assert result >= i - 1, "Result grows with each iteration"

    # Postconditions
    assert result >= 1, "Factorial is at least 1"
    assert isinstance(result, int), "Result is integer"

    # Specific bounds based on input
    if n == 0 or n == 1:
        assert result == 1, "factorial(0) = factorial(1) = 1"
    elif n == 2:
        assert result == 2, "factorial(2) = 2"
    elif n == 3:
        assert result == 6, "factorial(3) = 6"
    elif n == 4:
        assert result == 24, "factorial(4) = 24"

    return result


def linear_search(arr: list, target: int) -> int:
    """
    Linear search with comprehensive contracts.
    Demonstrates list preconditions and search postconditions.
    """
    # Preconditions
    assert isinstance(arr, list), "First argument must be a list"
    assert isinstance(target, int), "Target must be an integer"
    assert all(isinstance(x, int) for x in arr), "All array elements must be integers"

    index = 0
    found_index = -1

    while index < len(arr):
        # Loop invariant: target not found in arr[0:index]
        assert index >= 0, "Index is non-negative"
        assert index < len(arr), "Index within bounds"
        assert found_index == -1, "Haven't found target yet"

        if arr[index] == target:
            found_index = index
            break

        index = index + 1

        # Post-increment invariant
        assert index <= len(arr), "Index doesn't exceed array length"

    result = found_index

    # Postconditions
    assert isinstance(result, int), "Result is an integer"
    assert result >= -1, "Result is -1 or valid index"
    assert result < len(arr), "If found, result is valid index"

    # Correctness properties
    if result == -1:
        # Target not found - verify it's not in the array
        assert target not in arr, "If result is -1, target shouldn't be in array"
    else:
        # Target found - verify correctness
        assert 0 <= result < len(arr), "Found index is valid"
        assert arr[result] == target, "Element at found index equals target"

    return result


def compute_average(numbers: list) -> float:
    """
    Average computation with input validation.
    Demonstrates aggregate operations and mathematical properties.
    """
    # Preconditions
    assert isinstance(numbers, list), "Input must be a list"
    assert len(numbers) > 0, "Cannot compute average of empty list"
    assert all(isinstance(x, (int, float)) for x in numbers), (
        "All elements must be numbers"
    )

    # Compute sum with invariant checking
    total = 0
    count = 0

    for num in numbers:
        # Loop invariant: total is sum of processed elements
        assert isinstance(total, (int, float)), "Total remains numeric"
        assert count >= 0, "Count is non-negative"
        assert count <= len(numbers), "Count doesn't exceed list length"

        total = total + num
        count = count + 1

        # Post-increment invariant
        assert count <= len(numbers), "Count within bounds"

    # Division step
    assert count == len(numbers), "Processed all elements"
    assert count > 0, "Count is positive for division"

    result = total / count

    # Postconditions
    assert isinstance(result, float), "Average is a float"

    # Mathematical properties
    if all(x >= 0 for x in numbers):
        assert result >= 0, "Average of non-negative numbers is non-negative"

    if len(numbers) == 1:
        assert result == numbers[0], "Average of single element is that element"

    # Bounds checking
    min_val = min(numbers)
    max_val = max(numbers)
    assert min_val <= result <= max_val, "Average is between min and max"

    return result


def fibonacci_iterative(n: int) -> int:
    """
    Fibonacci sequence with detailed contracts.
    Demonstrates sequence properties and mathematical relationships.
    """
    # Preconditions
    assert isinstance(n, int), "Input must be an integer"
    assert n >= 0, "Fibonacci undefined for negative indices"
    assert n <= 20, "Limited to prevent large numbers"

    if n == 0:
        return 0
    elif n == 1:
        return 1
    else:
        prev_prev = 0
        prev = 1

        for i in range(2, n + 1):
            # Loop invariant: prev_prev = fib(i-2), prev = fib(i-1)
            assert prev_prev >= 0, "Fibonacci numbers are non-negative"
            assert prev >= 0, "Fibonacci numbers are non-negative"
            assert prev >= prev_prev, "Fibonacci sequence is non-decreasing"
            assert i >= 2, "Loop starts from index 2"
            assert i <= n, "Loop index within bounds"

            current = prev + prev_prev
            prev_prev = prev
            prev = current

            # Post-update invariant
            assert current >= prev_prev, "New Fibonacci number >= previous"
            assert current == prev, "Current stored in prev for next iteration"

    result = prev

    # Postconditions
    assert result >= 0, "Fibonacci result is non-negative"
    assert isinstance(result, int), "Fibonacci result is integer"

    # Known Fibonacci values
    if n == 0:
        assert result == 0, "fib(0) = 0"
    elif n == 1:
        assert result == 1, "fib(1) = 1"
    elif n == 2:
        assert result == 1, "fib(2) = 1"
    elif n == 3:
        assert result == 2, "fib(3) = 2"
    elif n == 4:
        assert result == 3, "fib(4) = 3"
    elif n == 5:
        assert result == 5, "fib(5) = 5"

    return result


def validate_and_process(data: list) -> dict:
    """
    Data validation and processing function.
    Demonstrates complex contracts with multiple phases.
    """
    # Preconditions
    assert isinstance(data, list), "Input must be a list"
    assert len(data) > 0, "Cannot process empty data"

    # Phase 1: Validation
    valid_count = 0
    for item in data:
        if isinstance(item, int) and item >= 0:
            valid_count = valid_count + 1

    # Validation postcondition
    assert valid_count >= 0, "Valid count is non-negative"
    assert valid_count <= len(data), "Valid count doesn't exceed total"
    assert valid_count > 0, "Must have some valid data to process"

    # Phase 2: Processing
    total = 0
    processed_count = 0

    for item in data:
        if isinstance(item, int) and item >= 0:
            # Processing invariant
            assert isinstance(total, int), "Total remains integer"
            assert processed_count >= 0, "Processed count non-negative"

            total = total + item
            processed_count = processed_count + 1

            # Post-processing invariant
            assert total >= 0, "Total of non-negative numbers is non-negative"

    # Processing postcondition
    assert processed_count == valid_count, "Processed all valid items"
    assert total >= 0, "Total is non-negative"

    # Phase 3: Result construction
    if processed_count > 0:
        average = total / processed_count
    else:
        average = 0.0

    result = {"count": processed_count, "total": total, "average": average}

    # Final postconditions
    assert isinstance(result, dict), "Result is a dictionary"
    assert "count" in result, "Result contains count"
    assert "total" in result, "Result contains total"
    assert "average" in result, "Result contains average"

    assert result["count"] >= 0, "Count is non-negative"
    assert result["total"] >= 0, "Total is non-negative"
    assert result["average"] >= 0.0, "Average is non-negative"

    if result["count"] > 0:
        assert result["average"] == result["total"] / result["count"], (
            "Average computed correctly"
        )

    return result


def main():
    """
    Main function that exercises all contract examples.
    This function calls others to demonstrate the full contract system.
    """
    # Test safe_sqrt_approximation
    sqrt_result = safe_sqrt_approximation(16)
    assert sqrt_result == 4, "sqrt(16) should be 4"

    # Test bounded_factorial
    fact_result = bounded_factorial(5)
    assert fact_result == 120, "5! should be 120"

    # Test linear_search
    test_array = [3, 7, 1, 9, 4]
    search_result = linear_search(test_array, 7)
    assert search_result == 1, "Should find 7 at index 1"

    # Test compute_average
    test_numbers = [2, 4, 6, 8]
    avg_result = compute_average(test_numbers)
    assert avg_result == 5.0, "Average of [2,4,6,8] should be 5.0"

    # Test fibonacci_iterative
    fib_result = fibonacci_iterative(6)
    assert fib_result == 8, "6th Fibonacci number should be 8"

    # Test validate_and_process
    test_data = [1, -2, 3, "invalid", 4]
    process_result = validate_and_process(test_data)
    assert process_result["count"] == 3, "Should process 3 valid items"
    assert process_result["total"] == 8, "Sum should be 1+3+4=8"

    return True


if __name__ == "__main__":
    success = main()
    if success:
        print("✓ All contract examples executed successfully!")
    else:
        print("✗ Contract validation failed!")
