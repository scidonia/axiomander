"""Test file to verify LSP diagnostics are working."""


def working_function(x: int) -> int:
    """This function should pass verification."""
    # Precondition
    assert x > 0, "Input must be positive"

    result = x + 1

    # Postcondition
    assert result > x, "Result must be greater than input"
    return result


def potentially_failing_function(x: int) -> int:
    """This function might have verification issues."""
    # This precondition might be too restrictive
    assert x > 100, "Input must be greater than 100"

    result = x - 50

    # This postcondition might fail for some inputs
    assert result > x, "Result must be greater than input"  # This will fail!
    return result
