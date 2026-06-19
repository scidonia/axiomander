"""External order/payment/inventory database -- the THEORY layer.

This module is the *external system* that `fulfil_order` calls into.  It is
a real, runnable Python fixture (an in-memory store) AND the carrier of the
verification THEORY: each operation that axiomander reasons about declares
its atomic-access guarantee in an `axiomander:` docstring block.

The implementation reads/writes through these operations; the verifier does
NOT look inside them -- they are opaque calls whose behaviour is exactly
their declared contract.  The guarantees are:

  - Atomic read-after-write       (db_get after db_put returns the value)
  - Idempotent payment capture    (capture twice == capture once)
  - Compare-and-set on status     (CAS: the exactly-once linearization point)

The runnable store below lets the same file double as a pytest fixture: the
contracts are what axiomander proves against; the bodies are what actually
executes.  The two must agree -- the body is the reference implementation
that the contract abstracts.

State is modelled with IntEnums (the Pydantic idiom for enum-typed fields).
Axiomander resolves enum members to their integer encodings, so the contract
language stays in Z arithmetic while the source code reads symbolically.
"""

from enum import IntEnum


# -- State enums (Pydantic-style IntEnum) ----------------------------------

class OrderStatus(IntEnum):
    READY = 0       # order ready to fulfil
    PENDING = 1     # fulfilment in progress (crash-recovery state)
    DONE = 2        # fulfilled (terminal success)


class PaymentState(IntEnum):
    AUTHORIZED = 0  # payment authorized, not captured
    PENDING = 1     # capture in progress
    CAPTURED = 2    # payment captured (terminal)


class QueueState(IntEnum):
    READY = 0       # queued, ready
    RETRY = 1       # transient failure, retry
    DONE = 2        # completed


# -- Runnable in-memory store (the reference implementation) ---------------

class _Store:
    """In-memory key-value store with per-key atomic operations.

    This is the concrete model the theory abstracts.  Each method's
    behaviour matches the axiomander: contract on the corresponding stub.
    """

    def __init__(self) -> None:
        self.order_status: dict[int, int] = {}
        self.payment_state: dict[int, int] = {}
        self.queue_state: dict[int, int] = {}
        self.reserved: dict[int, bool] = {}
        self.events: list[dict] = []

    def seed(self, order_id: int) -> None:
        self.order_status[order_id] = OrderStatus.READY
        self.payment_state[order_id] = PaymentState.AUTHORIZED
        self.queue_state[order_id] = QueueState.READY
        self.reserved[order_id] = False


# A single process-wide store for the fixture.
DB = _Store()


# -- Theory stubs: order status -------------------------------------------

def db_get_order_status(order_id: int) -> int:
    """
    axiomander:
        requires:
            order_id > 0
        ensures:
            result >= OrderStatus.READY
            result <= OrderStatus.DONE
        reads:
            order_status
    """
    return DB.order_status[order_id]


def db_set_order_status(order_id: int, new_status: int) -> int:
    """Atomic write of the order status.  Returns the value written, so the
    caller can rely on read-after-write WITHOUT a second round trip.

    axiomander:
        requires:
            order_id > 0
            new_status >= OrderStatus.READY
            new_status <= OrderStatus.DONE
        ensures:
            result == new_status
        writes:
            order_status
    """
    DB.order_status[order_id] = new_status
    return new_status


def cas_order_status(order_id: int, expect: int, new_status: int) -> int:
    """Compare-and-set the order status atomically.

    This is the EXACTLY-ONCE linearization point: the status moves from
    [expect] to [new_status] atomically, and the return value reports
    whether THIS caller performed the transition (1) or lost the race (0).
    At most one caller can observe result == 1 for a given (expect->new)
    transition, which is what bounds successful fulfilments to <= 1.

    axiomander:
        requires:
            order_id > 0
            expect >= OrderStatus.READY
            expect <= OrderStatus.DONE
            new_status >= OrderStatus.READY
            new_status <= OrderStatus.DONE
        ensures:
            result >= 0
            result <= 1
            implies(result == 1, db_get_order_status(order_id) == new_status)
            implies(result == 0, db_get_order_status(order_id) != new_status)
        writes:
            order_status
    """
    if DB.order_status.get(order_id) == expect:
        DB.order_status[order_id] = new_status
        return 1
    return 0


# -- Theory stubs: payment -------------------------------------------------

def db_get_payment_state(order_id: int) -> int:
    """
    axiomander:
        requires:
            order_id > 0
        ensures:
            result >= PaymentState.AUTHORIZED
            result <= PaymentState.CAPTURED
        reads:
            payment_state
    """
    return DB.payment_state[order_id]


def capture_payment(order_id: int) -> int:
    """Capture an authorized payment.  IDEMPOTENT: calling twice leaves the
    payment captured exactly as calling once -- the second call is a no-op
    that still reports success.  This is the at-most-once charge guarantee.

    axiomander:
        requires:
            order_id > 0
            db_get_payment_state(order_id) >= PaymentState.AUTHORIZED
        ensures:
            result == PaymentState.CAPTURED
            db_get_payment_state(order_id) == PaymentState.CAPTURED
        writes:
            payment_state
    """
    DB.payment_state[order_id] = PaymentState.CAPTURED
    return PaymentState.CAPTURED


# -- Theory stubs: queue ---------------------------------------------------

def db_get_queue_state(order_id: int) -> int:
    """
    axiomander:
        requires:
            order_id > 0
        ensures:
            result >= QueueState.READY
            result <= QueueState.DONE
        reads:
            queue_state
    """
    return DB.queue_state[order_id]


def db_set_queue_state(order_id: int, new_state: int) -> int:
    """
    axiomander:
        requires:
            order_id > 0
            new_state >= QueueState.READY
            new_state <= QueueState.DONE
        ensures:
            result == new_state
        writes:
            queue_state
    """
    DB.queue_state[order_id] = new_state
    return new_state


# -- Theory stubs: inventory ----------------------------------------------

def reserve_inventory(order_id: int) -> int:
    """Reserve the order's inventory.  Returns 1 on success, 0 if stock is
    insufficient.  On failure NO stock is consumed (no_lost_inventory).

    axiomander:
        requires:
            order_id > 0
        ensures:
            result >= 0
            result <= 1
        writes:
            reserved
    """
    DB.reserved[order_id] = True
    return 1


# -- Theory stubs: event bus ----------------------------------------------

def emit_fulfilled_event(order_id: int, worker_id: int) -> int:
    """Emit exactly one 'orders.fulfilled' event for this order.  Returns 1.

    axiomander:
        requires:
            order_id > 0
            worker_id > 0
        ensures:
            result == 1
        writes:
            events
    """
    DB.events.append({
        "topic": "orders.fulfilled",
        "order_id": order_id,
        "worker_id": worker_id,
    })
    return 1
