"""Ghost models for the fulfil_order domain.

Every identifier that appears in the contract docstring must be defined
here with its own docstring contract.  These are specification-only
(never executed), but their contracts tell the pipeline what types and
constraints the functions obey.

Usage:
    from axiomander.oracle.resources.ghost_models import Order
    # In a contract: requires Order.status(order_id) == "ready"
"""

from typing import Literal


class Order:
    """axomander:
        ghost: true
    """

    @staticmethod
    def status(order_id: int) -> str:
        """axomander:
            requires: order_id > 0
            ensures: result in {"ready", "fulfilled", "failed_recoverably", "fulfilment_pending"}
        """
        ...

    @staticmethod
    def items(order_id: int) -> list:
        """axomander:
            requires: order_id > 0
            ensures: len(result) >= 1
        """
        ...


class Payment:
    """axomander:
        ghost: true
    """

    @staticmethod
    def state(order_id: int) -> str:
        """axomander:
            requires: order_id > 0
            ensures: result in {"authorized", "captured", "capture_pending"}
        """
        ...

    @staticmethod
    def authorization(order_id: int) -> dict:
        """axomander:
            requires: order_id > 0
            owns: true
        """
        ...

    @staticmethod
    def capture(order_id: int) -> dict:
        """axomander:
            requires: order_id > 0
            may_modify: true
        """
        ...


class OrderQueue:
    """axomander:
        ghost: true
    """

    @staticmethod
    def contains(order_id: int) -> bool:
        """axomander:
            requires: order_id > 0
            ensures: result == True
        """
        ...

    @staticmethod
    def item(order_id: int) -> dict:
        """axomander:
            requires: order_id > 0
            owns: true
        """
        ...


class Inventory:
    """axomander:
        ghost: true
    """

    @staticmethod
    def can_reserve(items: list) -> bool:
        """axomander:
            requires: len(items) >= 1
            ensures: result == True
        """
        ...

    @staticmethod
    def reservation_rights(items: list) -> dict:
        """axomander:
            requires: len(items) >= 1
            owns: true
        """
        ...

    @staticmethod
    def reserved_for(order_id: int, items: list) -> bool:
        """axomander:
            requires: order_id > 0; len(items) >= 1
        """
        ...

    @staticmethod
    def stock_totals(except_items: list | None = None) -> dict:
        """axomander:
            ghost: true
        """
        ...


class EventBus:
    """axomander:
        ghost: true
    """

    emitted: list[dict] = []

    @staticmethod
    def topic(name: str) -> dict:
        """axomander:
            ghost: true
        """
        ...
