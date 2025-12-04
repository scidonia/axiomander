"""Contract decorators for design-by-contract programming."""

import os
import functools
from typing import Callable, Any

from .exceptions import (
    PreconditionViolationError,
    PostconditionViolationError,
    InvariantViolationError,
)

# Contract checking can be disabled by setting AXIOMANDER_DISABLE_CONTRACTS=1
CONTRACTS_ENABLED = os.getenv('AXIOMANDER_DISABLE_CONTRACTS', '0') != '1'


def precondition(contract_text: str, check_func: Callable):
    """Decorator for precondition contracts."""
    def decorator(func: Callable) -> Callable:
        if not CONTRACTS_ENABLED:
            return func
        
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            if not check_func(*args, **kwargs):
                raise PreconditionViolationError(func.__name__, contract_text, args, kwargs)
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
                raise PostconditionViolationError(func.__name__, contract_text, result, args, kwargs)
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
