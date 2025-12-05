"""Logical specification for absolute_value function.

This file demonstrates the use of standard mathematical predicates
from the axiomander.contracts library instead of custom validation functions.
"""

from typing import Union

# Import standard predicates from contracts library
from axiomander.contracts import (
    is_real_number,
    result_is_non_negative,
    result_equals_abs_input,
    result_is_idempotent,
    absolute_value_contract
)

Number = Union[int, float]

# The predicates are now provided by the contracts library
# No need to redefine them here - they're imported above

# For reference, the complete absolute value contract can be applied as:
# @absolute_value_contract
# def absolute_value(x: Number) -> Number:
#     # implementation
