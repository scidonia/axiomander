"""Logical specification for absolute_value function."""

from typing import Union

Number = Union[int, float]

def is_real_number(x: Number) -> bool:
    """
    Precondition: Check if input is a real number.
    
    Args:
        x: The input value to check
        
    Returns:
        True if x is a real number (int or float), False otherwise
    """
    return isinstance(x, (int, float)) and not isinstance(x, bool)

def is_absolute_value(x: Number, result: Number) -> bool:
    """
    Postcondition: Check if result is the absolute value of x.
    
    Args:
        x: The original input value
        result: The computed result
        
    Returns:
        True if result is the absolute value of x
    """
    return (
        isinstance(result, (int, float)) and
        not isinstance(result, bool) and
        result >= 0 and
        (result == x or result == -x)
    )
