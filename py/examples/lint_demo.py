"""
Demo file for contract linter.
Each function demonstrates a different classification pattern.
"""

def add(a: int, b: int) -> int:
    assert True                          # precondition
    result = a + b
    assert result == a + b               # postcondition
    return result


def max_of_two(a: int, b: int) -> int:
    assert a >= 0                        # precondition
    assert b >= 0                        # also precondition
    if a >= b:
        return a
    else:
        return b


def sum_to(n: int) -> int:
    assert n >= 0                        # precondition
    acc = 0
    i = 0
    while i < n:
        assert acc == i * (i + 1) // 2   # loop invariant
        assert i <= n                     # also invariant
        i = i + 1
        acc = acc + i
    assert acc == n * (n + 1) // 2       # postcondition
    return acc


def invalid_contract(x: int) -> int:
    assert open("/etc/passwd")           # impure — file I/O
    return 0


def unsupported_contract(items: list) -> bool:
    assert [x for x in items if x > 0]   # list comprehension
    return True
