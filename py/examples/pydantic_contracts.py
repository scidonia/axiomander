"""
Demonstrates contracts with Pydantic-style object constraints.

Patterns shown:
  1. Type checking:  assert isinstance(obj, ClassName)
  2. Field relations: assert obj.total == obj.subtotal + obj.tax
  3. Value ranges:    assert obj.subtotal >= 0
"""


class Order:
    """Order with derived total field. The invariant is:
       total == subtotal + tax (always holds)"""
    subtotal: int
    tax: int
    total: int


def apply_discount(order: Order, discount_pct: int) -> int:
    """Apply a discount percentage to an order total.
    
    Precondition: order is well-formed (total = subtotal + tax, values non-negative)
    Postcondition: result <= original total
    """
    assert isinstance(order, Order)                              # type guard
    assert order.total == order.subtotal + order.tax              # field relation
    assert order.subtotal >= 0                                    # value constraint
    assert order.tax >= 0                                         # value constraint
    assert 0 <= discount_pct <= 100                              # range check

    discount = order.total * discount_pct // 100
    result = order.total - discount

    assert result <= order.total                                  # postcondition
    assert result >= 0                                            # postcondition (no negative totals from discounts)
    return result


class Account:
    """Account with balance that must never go negative."""
    balance: int
    overdraft_limit: int


def withdraw(account: Account, amount: int) -> int:
    """Withdraw money from an account.
    
    Precondition: amount >= 0, account has sufficient balance/overdraft
    Postcondition: balance decreases by amount, result == new balance
    """
    assert isinstance(account, Account)                          # type guard
    assert amount >= 0                                            # amount is non-negative
    assert account.balance + account.overdraft_limit >= amount    # sufficient funds

    account.balance = account.balance - amount
    result = account.balance

    assert account.balance == result                              # postcondition
    assert account.balance == (account.balance + amount) - amount  # balance decreased correctly
    return result


class Rectangle:
    """Rectangle with area constraint."""
    width: int
    height: int
    area: int


def scale(rect: Rectangle, factor: int) -> int:
    """Scale a rectangle's dimensions by a factor.
    
    Precondition: area == width * height, factor > 0
    Postcondition: new area == (width * factor) * (height * factor)
    """
    assert isinstance(rect, Rectangle)                           # type guard
    assert rect.area == rect.width * rect.height                  # field relation (invariant)
    assert factor > 0                                             # positivity

    rect.width = rect.width * factor
    rect.height = rect.height * factor
    rect.area = rect.width * rect.height

    assert rect.area == rect.width * rect.height                  # invariant preserved
    return rect.area
