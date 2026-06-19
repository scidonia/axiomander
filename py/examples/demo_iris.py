def transfer(balance: int, amount: int) -> int:
    assert balance >= 0
    assert amount >= 0
    assert amount <= balance
    new_balance = balance - amount
    result = new_balance
    assert result >= 0
    return result


def broken(x: int) -> int:
    assert x >= 0
    result = x + 1
    assert result == 2
    return result
