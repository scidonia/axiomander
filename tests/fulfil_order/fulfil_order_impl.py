"""fulfil_order -- the real implementation, verified against the DB theory.

This is THE implementation (and the test target).  It calls into the
external database theory (external_db.py); the verifier composes the DB
operations' declared guarantees to discharge fulfil_order's contract.

Decomposition (the specification graph):

    fulfil_order
      |-- do_reserve_inventory   -- reserve stock, no_lost_inventory on failure
      |-- do_capture_payment     -- idempotent capture (at-most-once charge)
      |-- do_commit_order        -- CAS status (exactly-once) + queue + emit

Each subcontract is verified independently against the DB theory, then
composed at the fulfil_order call site.

Result is modelled with an IntEnum (the Pydantic idiom).  Axiomander
resolves its members to their integer encodings, keeping the contract
language in Z arithmetic while the source reads symbolically.
"""

from enum import IntEnum

from external_db import (
    OrderStatus, PaymentState, QueueState,
    db_get_order_status, db_set_order_status, cas_order_status,
    db_get_payment_state, capture_payment,
    db_get_queue_state, db_set_queue_state,
    reserve_inventory, emit_fulfilled_event,
)


class Result(IntEnum):
    FAILED_RECOVERABLE = 0
    FULFILLED = 1


# -- Subcontract 1: reserve inventory -------------------------------------

def do_reserve_inventory(order_id: int) -> int:
    """Reserve the order's inventory.

    Returns 1 if reserved, 0 if stock insufficient.  On failure no stock is
    consumed -- this is the no_lost_inventory guarantee, inherited from the
    DB theory's reserve_inventory postcondition.

    axiomander:
        requires:
            order_id > 0
        ensures:
            result >= 0
            result <= 1
    """
    r = reserve_inventory(order_id)
    result = r
    return result


# -- Subcontract 2: capture payment ---------------------------------------

def do_capture_payment(order_id: int) -> int:
    """Capture the authorized payment (idempotent at the theory level).

    Postcondition: the payment state is PAY_CAPTURED (2) afterwards, and the
    result reports the captured state.  Because the DB capture is idempotent,
    re-invoking this is safe (no double charge).

    axiomander:
        requires:
            order_id > 0
            db_get_payment_state(order_id) >= PaymentState.AUTHORIZED
        ensures:
            result == PaymentState.CAPTURED
            db_get_payment_state(order_id) == PaymentState.CAPTURED
    """
    p = capture_payment(order_id)
    result = p
    return result


# -- Subcontract 3: commit order (the exactly-once point) -----------------

def do_commit_order(order_id: int, worker_id: int) -> int:
    """Commit the fulfilment: atomically move the order status from READY to
    DONE via compare-and-set, then complete the queue and emit the event.

    The CAS is the linearization point: result == 1 means THIS worker won the
    transition (and thus emitted the event); result == 0 means another worker
    already committed, so we must NOT double-emit.  This is what bounds
    successful fulfilments to at most one (exactly_once_domain_effect).

    axiomander:
        requires:
            order_id > 0
            worker_id > 0
        ensures:
            result >= 0
            result <= 1
            implies(result == 1, db_get_order_status(order_id) == OrderStatus.DONE)
    """
    won = cas_order_status(order_id, OrderStatus.READY, OrderStatus.DONE)
    if won == 1:
        q = db_set_queue_state(order_id, QueueState.DONE)
        e = emit_fulfilled_event(order_id, worker_id)
        result = 1
        return result
    result = 0
    return result


# -- Top-level: fulfil_order ----------------------------------------------

def fulfil_order(order_id: int, worker_id: int) -> int:
    """Fulfil a single order exactly once.

    Preconditions (the caller-supplied resources): the order is READY, the
    payment is AUTHORIZED.  Flow:

      1. reserve inventory  -- if it fails, fail recoverably (no lost stock)
      2. capture payment    -- idempotent, no double charge
      3. commit order       -- CAS READY->DONE; only the winner emits

    Returns RESULT_FULFILLED (1) if this worker fulfilled the order, or
    RESULT_FAILED_RECOVERABLE (0) if inventory was short or another worker
    won the commit race.  In the failed case the order remains recoverable
    (status not DONE, no event emitted by us).

    axiomander:
        requires:
            order_id > 0
            worker_id > 0
            db_get_order_status(order_id) == OrderStatus.READY
            db_get_payment_state(order_id) == PaymentState.AUTHORIZED
        ensures:
            result >= 0
            result <= 1
            implies(result == 1, db_get_order_status(order_id) == OrderStatus.DONE)
            implies(result == 1, db_get_payment_state(order_id) == PaymentState.CAPTURED)
    """
    reserved = do_reserve_inventory(order_id)
    if reserved == 0:
        result = 0
        assert result == 0
        return result

    captured = do_capture_payment(order_id)
    committed = do_commit_order(order_id, worker_id)
    result = committed
    assert result >= 0
    assert result <= 1
    return result
