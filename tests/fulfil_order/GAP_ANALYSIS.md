# fulfil_order Contract Gap Analysis

The full docstring contract is in `tests/fulfil_order/contract.py`.
This document maps every clause to its current verification status.

## Proven

| Clause | Test | Status |
|--------|------|--------|
| `result.status in {"fulfilled", "failed"}` | `test_set_membership_postcondition` | Verified |
| `result == "fulfilled"` (string post) | `test_string_postcondition` | Verified |
| String-guard while: `while load(c) == "ready": ...; store(c, "done")` | `test_string_guard_while_single_cell` | Verified |

## Partially Proven

| Clause | Test | Status |
|--------|------|--------|
| `requires OrderQueue.contains(order_id)` | `test_fulfil_order_composition` | Proves as opaque precondition call |
| `requires Order(order_id).status == "ready"` | `test_fulfil_order_composition` | Proves as enum-equality contract |
| `ensures result >= 0; result <= 1` (int post) | `test_fulfil_order_composition` | Proves for 3-leaf composition, but composition proof itself fails (needs frame lemmas) |
| `ensures result == PaymentState.CAPTURED` (enum post) | `test_fulfil_order_composition` (do_capture_payment) | Individual leaf proven |

## Not Proven — Requires Frame Lemmas

| Clause | Why |
|--------|-----|
| Composition of `do_reserve_inventory`, `do_capture_payment`, `do_commit_order` | Caller proof needs per-callee frame lemmas to prove each subcontract doesn't disturb the others' state |
| `frame: may_modify Orders.row(order_id)` | Frame condition declaration parsed but not enforced in proof |
| `frame: may_modify OrderQueue.item(order_id)` | Same |
| `frame: may_modify Inventory.reservations(for_order=order_id)` | Same |
| `frame: may_modify Payment.capture(order_id)` | Same |
| `frame: may_emit EventBus.topic("orders.fulfilled")` | Same |
| `frame: must_not_modify Orders.rows(except=order_id)` | Negative frame constraint; never checked |
| `frame: must_not_modify Inventory.stock_totals(except=...)` | Same |
| `frame: must_not_emit EventBus.topic(except="orders.fulfilled")` | Same |

## Not Proven — Requires New Features

| Clause | Feature Needed |
|--------|----------------|
| `owns queue_item: OrderQueue.item(order_id)` | Resource ownership tracking |
| `owns order_row: Orders.row(order_id)` | Resource ownership tracking |
| `owns payment_auth: Payment.authorization(order_id)` | Resource ownership tracking |
| `owns stock: Inventory.reservation_rights(...)` | Resource ownership tracking |
| `ensures result.status == "fulfilled" -> Orders.row(..).status == "fulfilled" and ...` | Implication in postcondition; already parsed by docstring_contracts but output shape not wired to WP |
| `ensures result.status == "failed_recoverably" -> ...` | Same |
| `exists e in EventBus.emitted: e.topic == "orders.fulfilled"` | Existential quantifier over event log |
| `no_lost_inventory(Order(order_id))` | Domain-specific predicate |
| `exactly_once_domain_effect(order_id)` | History model — needs event log ghost theory |
| `preserves GlobalInvariant.accounting_consistency` | Global invariants |
| `preserves GlobalInvariant.inventory_nonnegative` | Global invariants |
| `preserves GlobalInvariant.queue_order_correspondence` | Global invariants |

## Immediate Next Step

Frame lemmas unlock the composition proof and 9 of the 10 `frame:` clauses.
This is the single highest-leverage gap to close.
