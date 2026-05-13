from py.contracts import requires, ensures


# ─── add ───
@requires(lambda a, b: True)
@ensures(lambda a, b, result: result == a + b)
def add(a: int, b: int) -> int:
    return a + b


# ─── max_of_two ───
@requires(lambda a: a >= 0)
@requires(lambda b: b >= 0)
@ensures(lambda a, b, result: result >= a and result >= b)
def max_of_two(a: int, b: int) -> int:
    if a >= b:
        return a
    else:
        return b
