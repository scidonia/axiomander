# axiomander:component:example-abs-001
# axiomander:module:example
# axiomander:uniquified_name:absolute_value
# axiomander:original_name:absolute_value
# axiomander:path:

"""Logical contracts for component: absolute_value
Calculate the absolute value of a number
Original UID: example-abs-001
"""

"""Logical specification for absolute_value function."""

from typing import Union
from axiomander.contracts import is_real_number, result_equals_abs_input

Number = Union[int, float]

# Define the specific predicate functions referenced in component.json
def absolute_value_precondition(*args, **kwargs) -> bool:
    """Precondition: Input must be a real number."""
    return is_real_number(*args, **kwargs)

def absolute_value_postcondition(result, *args, **kwargs) -> bool:
    """Postcondition: Result is non-negative and equals absolute value of input."""
    return result_equals_abs_input(result, *args, **kwargs)
