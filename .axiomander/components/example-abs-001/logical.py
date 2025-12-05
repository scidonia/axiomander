"""Logical specification for absolute_value function."""

from typing import Union
from axiomander.contracts import (
    is_real_number,
    result_equals_abs_input,
    result_is_non_negative,
)

Number = Union[int, float]


# Define the specific predicate functions referenced in component.json
def absolute_value_precondition(*args, **kwargs) -> bool:
    """Precondition: Input must be a real number."""
    return is_real_number(*args, **kwargs)


def absolute_value_postcondition(result, *args, **kwargs) -> bool:
    """Postcondition: Result is non-negative and equals absolute value of input."""
    return result_is_non_negative(result, *args, **kwargs) and result_equals_abs_input(
        result, *args, **kwargs
    )
