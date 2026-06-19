"""fulfil_order — exactly-once order fulfilment.

Strong contract from "Strong Contracts for AI-Written Python."
This is the FULL docstring contract.  It does NOT verify yet; it serves
as the target specification.  The assert-based Phase 3 version in
phase3_assert.py is the currently-verifiable subset.

DO NOT MODIFY THIS CONTRACT WITHOUT PERMISSION.
"""

from typing import Literal
from dataclasses import dataclass


# -- Domain types (placeholders) -------------------------------------------

OrderId = int
WorkerId = int

@dataclass
class FulfilmentResult:
    status: Literal["fulfilled", "failed_recoverably"]


# Pseudo-APIs — these would be real domain objects in production
class OrderQueue:
    @staticmethod
    def contains(order_id: OrderId) -> bool: ...

    @staticmethod
    def item(order_id: OrderId) -> dict: ...

class Orders:
    @staticmethod
    def row(order_id: OrderId) -> dict: ...

    @staticmethod
    def rows(*, except_id: OrderId | None = None) -> list[dict]: ...

class Payment:
    @staticmethod
    def authorization(order_id: OrderId) -> dict: ...

    @staticmethod
    def capture(order_id: OrderId) -> dict: ...

class Inventory:
    @staticmethod
    def can_reserve(items: list) -> bool: ...

    @staticmethod
    def reservation_rights(items: list) -> dict: ...

    @staticmethod
    def reservations(*, for_order: OrderId) -> dict: ...

    @staticmethod
    def stock_totals(*, except_items: list | None = None) -> dict: ...

class EventBus:
    @staticmethod
    def topic(name: str) -> dict: ...
    emitted: list[dict] = []


# -- The contract ---------------------------------------------------------

def fulfil_order(order_id: OrderId, worker_id: WorkerId) -> FulfilmentResult:
    """
    axiomander:
        requires OrderQueue.contains(order_id)
        requires Order(order_id).status == "ready"
        requires Payment(order_id).state == "authorized"
        requires Inventory.can_reserve(Order(order_id).items)

        owns queue_item:  OrderQueue.item(order_id)
        owns order_row:   Orders.row(order_id)
        owns payment_auth: Payment.authorization(order_id)
        owns stock:       Inventory.reservation_rights(Order(order_id).items)

        frame:
            may_modify Orders.row(order_id)
            may_modify OrderQueue.item(order_id)
            may_modify Inventory.reservations(for_order=order_id)
            may_modify Payment.capture(order_id)
            may_emit EventBus.topic("orders.fulfilled")
            must_not_modify Orders.rows(except=order_id)
            must_not_modify Inventory.stock_totals(except=Order(order_id).items)
            must_not_emit EventBus.topic(except="orders.fulfilled")

        ensures result.status in {"fulfilled", "failed_recoverably"}

        ensures result.status == "fulfilled" ->
            Orders.row(order_id).status == "fulfilled"
            and Payment(order_id).state == "captured"
            and Inventory.reserved_for(order_id, Order(order_id).items)
            and OrderQueue.item(order_id).state == "completed"
            and exists e in EventBus.emitted:
                e.topic == "orders.fulfilled"
                and e.payload.order_id == order_id
                and e.payload.worker_id == worker_id

        ensures result.status == "failed_recoverably" ->
            Orders.row(order_id).status in {"ready", "fulfilment_pending"}
            and Payment(order_id).state in {"authorized", "capture_pending"}
            and OrderQueue.item(order_id).state in {"ready", "retry"}
            and no_lost_inventory(Order(order_id))

        ensures exactly_once_domain_effect(order_id):
            forall histories h:
                count(successful_fulfilments(h, order_id)) <= 1

        preserves GlobalInvariant.accounting_consistency
        preserves GlobalInvariant.inventory_nonnegative
        preserves GlobalInvariant.queue_order_correspondence
    """
    raise NotImplementedError("contract-only — no implementation verified yet")
