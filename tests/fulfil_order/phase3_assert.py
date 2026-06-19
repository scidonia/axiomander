"""Phase 3: heap-cell subset of fulfil_order.

Strips the contract down to what the Iris backend can verify today:
- Heap cells for order/payment/queue state
- While-loop with symbolic bound
- String-value postconditions (via String.eqb)
- Multi-cell postcondition (⇑ result == "fulfilled" ∧ all cells updated)

This version uses ONLY assert statements — no docstring axiomander: block,
no ghost state, no frame conditions, no event bus.
"""

def fulfil_order_phase3(order_id: int, worker_id: int) -> str:
    # Preconditions: cell states
    assert order_id > 0
    assert worker_id > 0

    # Allocate heap cells (simulating Orders.row, Payment, OrderQueue)
    c_status = ref("ready")        # Orders.row(order_id).status
    c_payment = ref("authorized")  # Payment(order_id).state
    c_queue = ref("ready")         # OrderQueue.item(order_id).state

    # Main loop: process the order while it's in "ready" state
    while load(c_status) == "ready":
        # capture payment
        store(c_payment, "captured")
        # update order status
        store(c_status, "fulfilled")
        # mark queue completed
        store(c_queue, "completed")

    result = load(c_status)
    assert result == "fulfilled"
    assert load(c_payment) == "captured"
    assert load(c_queue) == "completed"
    return result
