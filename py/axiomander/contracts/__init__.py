"""
Hoare-logic contract decorators for Python.

Usage:

    @requires(lambda a, b: a > 0 and b > 0)
    @ensures(lambda a, b, result: result > a and result > b)
    def add(a: int, b: int) -> int:
        return a + b

    @invariant(lambda i, acc: acc == i * (i + 1) // 2)
    def sum_to(n: int) -> int:
        acc = 0
        for i in range(n + 1):
            acc += i
        return acc
"""

from typing import Any, Callable


def requires(predicate: Callable[..., bool]) -> Callable:
    """Decorator: attach a precondition to a function.

    The predicate receives the same arguments as the function.
    """
    def decorator(func: Callable) -> Callable:
        if not hasattr(func, "_contracts"):
            func._contracts = {"requires": [], "ensures": [], "invariants": []}
        func._contracts["requires"].append(predicate)
        return func
    return decorator


def ensures(predicate: Callable[..., bool]) -> Callable:
    """Decorator: attach a postcondition to a function.

    The predicate receives args + keyword argument `result`.
    """
    def decorator(func: Callable) -> Callable:
        if not hasattr(func, "_contracts"):
            func._contracts = {"requires": [], "ensures": [], "invariants": []}
        func._contracts["ensures"].append(predicate)
        return func
    return decorator


def invariant(predicate: Callable[..., bool]) -> Callable:
    """Decorator: attach a loop invariant.

    Used on for/while loops.
    """
    def decorator(func: Callable) -> Callable:
        if not hasattr(func, "_contracts"):
            func._contracts = {"requires": [], "ensures": [], "invariants": []}
        func._contracts["invariants"].append(predicate)
        return func
    return decorator


def get_contracts(func: Callable) -> dict[str, list[Callable]]:
    """Retrieve all contracts attached to a function."""
    return getattr(func, "_contracts", {"requires": [], "ensures": [], "invariants": []})
