"""Contract decorators for design-by-contract programming."""

import os
import functools
from typing import Callable, Any, Union

from .exceptions import (
    PreconditionViolationError,
    PostconditionViolationError,
    InvariantViolationError,
)

# Contract checking can be disabled by setting AXIOMANDER_DISABLE_CONTRACTS=1
CONTRACTS_ENABLED = os.getenv("AXIOMANDER_DISABLE_CONTRACTS", "0") != "1"

# Type aliases
Number = Union[int, float]


# =============================================================================
# STANDARD MATHEMATICAL PREDICATES
# =============================================================================


# Precondition predicates (check input arguments)
def is_real_number(*args, **kwargs) -> bool:
    """Check if first argument is a real number."""
    if not args:
        return False
    x = args[0]
    return isinstance(x, (int, float)) and not isinstance(x, bool)


def is_positive(*args, **kwargs) -> bool:
    """Check if first argument is positive."""
    if not args:
        return False
    x = args[0]
    return isinstance(x, (int, float)) and x > 0


def is_non_negative(*args, **kwargs) -> bool:
    """Check if first argument is non-negative."""
    if not args:
        return False
    x = args[0]
    return isinstance(x, (int, float)) and x >= 0


def is_integer(*args, **kwargs) -> bool:
    """Check if first argument is an integer."""
    if not args:
        return False
    x = args[0]
    return isinstance(x, int) and not isinstance(x, bool)


# Postcondition predicates (check result and input arguments)
def result_is_non_negative(result, *args, **kwargs) -> bool:
    """Check if result is non-negative."""
    return isinstance(result, (int, float)) and result >= 0


def result_is_positive(result, *args, **kwargs) -> bool:
    """Check if result is positive."""
    return isinstance(result, (int, float)) and result > 0


def result_preserves_magnitude(result, *args, **kwargs) -> bool:
    """Check if result has same magnitude as first input."""
    if not args:
        return False
    x = args[0]
    return isinstance(result, (int, float)) and abs(result) == abs(x)


def result_equals_abs_input(result, *args, **kwargs) -> bool:
    """Check if result equals absolute value of first input."""
    if not args:
        return False
    x = args[0]
    return isinstance(result, (int, float)) and result == abs(x)


def result_is_idempotent(result, *args, **kwargs) -> bool:
    """Check if applying the operation again would yield same result."""
    if not args:
        return False
    x = args[0]
    # For absolute value: abs(abs(x)) == abs(x)
    return abs(result) == result


def result_type_matches_input(result, *args, **kwargs) -> bool:
    """Check if result type matches first input type."""
    if not args:
        return False
    x = args[0]
    return type(result) == type(x)


# Relationship predicates
def result_geq_input(result, *args, **kwargs) -> bool:
    """Check if result >= first input."""
    if not args:
        return False
    x = args[0]
    return isinstance(result, (int, float)) and result >= x


def result_leq_input(result, *args, **kwargs) -> bool:
    """Check if result <= first input."""
    if not args:
        return False
    x = args[0]
    return isinstance(result, (int, float)) and result <= x


# =============================================================================
# CORE CONTRACT DECORATORS
# =============================================================================


def precondition(contract_text: str, check_func: Callable):
    """Decorator for precondition contracts."""

    def decorator(func: Callable) -> Callable:
        if not CONTRACTS_ENABLED:
            return func

        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            if not check_func(*args, **kwargs):
                raise PreconditionViolationError(
                    func.__name__, contract_text, args, kwargs
                )
            return func(*args, **kwargs)

        # Add contract text as attribute for introspection
        wrapper.__precondition__ = contract_text
        return wrapper

    return decorator


def postcondition(contract_text: str, check_func: Callable):
    """Decorator for postcondition contracts."""

    def decorator(func: Callable) -> Callable:
        if not CONTRACTS_ENABLED:
            return func

        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            result = func(*args, **kwargs)
            if not check_func(result, *args, **kwargs):
                raise PostconditionViolationError(
                    func.__name__, contract_text, result, args, kwargs
                )
            return result

        # Add contract text as attribute for introspection
        wrapper.__postcondition__ = contract_text
        return wrapper

    return decorator


def invariant(contract_text: str, check_func: Callable):
    """Decorator for class invariant contracts."""

    def decorator(cls):
        if not CONTRACTS_ENABLED:
            return cls

        # Store original __init__ and methods
        original_init = cls.__init__

        def check_invariant(self):
            if not check_func(self):
                raise InvariantViolationError(cls.__name__, contract_text, self)

        def new_init(self, *args, **kwargs):
            original_init(self, *args, **kwargs)
            check_invariant(self)

        cls.__init__ = new_init
        cls.__check_invariant__ = check_invariant
        cls.__invariant__ = contract_text

        return cls

    return decorator


# =============================================================================
# COMPOSABLE MATHEMATICAL DECORATORS
# =============================================================================


def requires_real_number(func: Callable) -> Callable:
    """Require first argument to be a real number."""
    return precondition("Input must be a real number", is_real_number)(func)


def requires_positive(func: Callable) -> Callable:
    """Require first argument to be positive."""
    return precondition("Input must be positive", is_positive)(func)


def requires_non_negative(func: Callable) -> Callable:
    """Require first argument to be non-negative."""
    return precondition("Input must be non-negative", is_non_negative)(func)


def ensures_non_negative_result(func: Callable) -> Callable:
    """Ensure result is non-negative."""
    return postcondition("Result must be non-negative", result_is_non_negative)(func)


def ensures_positive_result(func: Callable) -> Callable:
    """Ensure result is positive."""
    return postcondition("Result must be positive", result_is_positive)(func)


def ensures_magnitude_preserved(func: Callable) -> Callable:
    """Ensure result has same magnitude as input."""
    return postcondition(
        "Result preserves input magnitude", result_preserves_magnitude
    )(func)


def ensures_absolute_value(func: Callable) -> Callable:
    """Ensure result equals absolute value of input."""
    return postcondition(
        "Result equals absolute value of input", result_equals_abs_input
    )(func)


def ensures_idempotent(func: Callable) -> Callable:
    """Ensure operation is idempotent."""
    return postcondition("Operation is idempotent", result_is_idempotent)(func)


def ensures_type_preserved(func: Callable) -> Callable:
    """Ensure result type matches input type."""
    return postcondition("Result type matches input type", result_type_matches_input)(
        func
    )


# =============================================================================
# COMBINED MATHEMATICAL CONTRACTS
# =============================================================================


def absolute_value_contract(func: Callable) -> Callable:
    """Complete contract for absolute value function."""
    func = requires_real_number(func)
    func = ensures_non_negative_result(func)
    func = ensures_absolute_value(func)
    func = ensures_idempotent(func)
    return func


def square_root_contract(func: Callable) -> Callable:
    """Complete contract for square root function."""
    func = requires_non_negative(func)
    func = ensures_non_negative_result(func)
    return func


def logarithm_contract(func: Callable) -> Callable:
    """Complete contract for logarithm function."""
    func = requires_positive(func)
    return func
