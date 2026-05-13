def sum_to(n):
    assert n >= 0
    acc = 0
    i = 0
    while i < n:
        assert acc == i * (i + 1) // 2
        assert i <= n
        i = i + 1
        acc = acc + i
    assert acc == n * (n + 1) // 2
    assert i == n
    return acc

def add(a, b):
    assert True
    result = a + b
    assert result == a + b
    return result

def max_of_two(a, b):
    assert a >= 0
    assert b >= 0
    if a >= b:
        result = a
    else:
        result = b
    assert result >= a
    assert result >= b
    return result

def clamp(val, lo, hi):
    assert lo <= hi
    if val < lo:
        result = lo
    elif val > hi:
        result = hi
    else:
        result = val
    assert lo <= result <= hi
    return result
