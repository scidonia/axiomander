"""Implementation for absolute_value function."""

from typing import Union
from .logical import Number, absolute_value_precondition, absolute_value_postcondition
from axiomander.contracts import precondition, postcondition

@precondition("Input must be a real number", absolute_value_precondition)
@postcondition("Result is non-negative and equals absolute value of input", absolute_value_postcondition)
def absolute_value(x: Number) -> Number:
    """
    Calculate the absolute value of a number.

    The absolute value of a number is its distance from zero on the number line.
    For any real number x, |x| = x if x >= 0, and |x| = -x if x < 0.

    Args:
        x: A real number (int or float)

    Returns:
        The absolute value of x (always non-negative)

    Examples:
        >>> absolute_value(5)
        5
        >>> absolute_value(-3)
        3
        >>> absolute_value(0)
        0
        >>> absolute_value(-2.5)
        2.5
    """
    # Core logic: return x if non-negative, otherwise return -x
    if x >= 0:
        result = x
    else:
        result = -x

    return result
