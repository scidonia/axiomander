def broken_function(x: int) -> int:
    """A function with a broken contract for testing."""
    # Precondition
    assert x > 0, "Input must be positive"

    result = x - 10

    # Postcondition (this should fail for small x)
    assert result > 0, "Result should be positive"  # This will fail for x <= 10
    return result
