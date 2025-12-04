"""Implementation for absolute_value function."""

from typing import Union
from .logical import is_real_number, is_absolute_value, Number

def absolute_value(x: Number) -> Number:
    """
    Calculate the absolute value of a number.
    
    The absolute value of a number is its distance from zero on the number line.
    For any real number x, |x| = x if x >= 0, and |x| = -x if x < 0.
    
    Args:
        x: A real number (int or float)
        
    Returns:
        The absolute value of x (always non-negative)
        
    Raises:
        TypeError: If x is not a real number
        
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
    # Precondition check
    if not is_real_number(x):
        raise TypeError(f"Input must be a real number, got {type(x).__name__}")
    
    # Core logic: return x if non-negative, otherwise return -x
    if x >= 0:
        result = x
    else:
        result = -x
    
    # Postcondition check
    assert is_absolute_value(x, result), f"Postcondition failed: {result} is not absolute value of {x}"
    
    return result
