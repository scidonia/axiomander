"""
Example Python programs annotated with Hoare-logic contracts.

Each function demonstrates a specific proof obligation pattern.
Run the WP transformer on these to generate Coq proof goals.
"""

from axiomander.contracts import requires, ensures, invariant


# ─── Example 1: Simple arithmetic ──────────────────────────────────

@requires(lambda a, b: True)
@ensures(lambda a, b, result: result == a + b)
def add(a: int, b: int) -> int:
    return a + b


# ─── Example 2: Precondition on input ──────────────────────────────

@requires(lambda n: n >= 0)
@ensures(lambda n, result: result >= 0)
def abs_val(n: int) -> int:
    if n >= 0:
        return n
    else:
        return -n


# ─── Example 3: Multiple preconditions, single postcondition ───────

@requires(lambda a: a >= 0)
@requires(lambda b: b >= 0)
@ensures(lambda a, b, result: result >= a and result >= b)
def max_of_two(a: int, b: int) -> int:
    if a >= b:
        return a
    else:
        return b


# ─── Example 4: Loop with invariant (sum 1..n) ─────────────────────

@requires(lambda n: n >= 0)
@ensures(lambda n, result: result == n * (n + 1) // 2)
def sum_to(n: int) -> int:
    acc = 0
    i = 0
    # INV: acc == i * (i + 1) // 2 and i <= n
    while i < n:
        i = i + 1
        acc = acc + i
    return acc


# ─── Example 5: Swap two variables (pure version) ──────────────────

@requires(lambda x, y: True)
@ensures(lambda x, y, result: result == (y, x))
def swap(x: int, y: int) -> tuple[int, int]:
    return (y, x)
