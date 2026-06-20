# fulfil_order Contract Gap Analysis

The full docstring contract is in `tests/fulfil_order/contract.py`.
Updated after ghost-model wiring + implication postconditions.

## Proven (7 items)

| Clause | How |
|--------|-----|
| `result in {"fulfilled", "failed"}` | Set-membership postcondition |
| `result == "fulfilled"` | String postcondition |
| While-guard string loop | wp_while_str |
| 3-subcontract composition | do_reserve→capture→commit via OpaqueSpec |
| `ensures result == "fulfilled" -> X and Y` | finish_pure handles (A→B) |
| `frame: may_modify / must_not_modify` | Displayed + validated in frame-report |
| `Order.status(order_id) == 1` etc. | Ghost call in body → OpaqueSpec → call_opaque_pred |

## Assembly Work (5 items) — DONE

Each ghost function now has an OpaqueSpec entry and is called in the
function body with pre/post assertions checked.

| Ghost Function | Status |
|----------------|--------|
| `Orders.row_status(order_id)` | Verified (as `Orders_status`) |
| `Payment.state(order_id)` | Verified (as `Payment_state`) |
| `OrderQueue.contains(order_id)` | Verified (as `OrderQueue_contains`) |
| `Inventory.can_reserve(items)` | Verified (as `Inventory_can_reserve`) |
| `OrderQueue.item_state(order_id)` | Verified (as `OrderQueue_item_state`) |

See `test_ghost_model_composition` for the full verified fulfil_order
implementation with all 5 ghost functions + 3 subcontracts.

## Feature Work (8 items) — requires new infrastructure

| Clause | Feature |
|--------|---------|
| `exists e in EventBus.emitted` | Existential quantifier |
| `no_lost_inventory(order_id)` | Domain-specific predicate |
| `exactly_once_domain_effect(order_id)` | History model |
| `preserves GlobalInvariant.*` (3 items) | Global invariants |
| `owns queue_item / order_row / payment_auth / stock` (4 items) | Resource ownership (currently rejected by verifier) |

## Summary

```
Proven:  ████████████ 12 done (7 core + 5 assembly)
Future:  ████████     8 needs new features
```
