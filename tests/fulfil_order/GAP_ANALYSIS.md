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

## Assembly Work (5 items) — infrastructure exists, needs wiring

Each ghost function in ghost_models.py needs an OpaqueSpec entry in the table
with proper side/post_pred constraints, then called in the function body.

| Ghost Function | Needs |
|----------------|-------|
| `Orders.row_status(order_id)` | OpaqueSpec with string-kind result |
| `Payment.state(order_id)` | OpaqueSpec with int enum result |
| `OrderQueue.contains(order_id)` | OpaqueSpec with bool result |
| `Inventory.can_reserve(items)` | OpaqueSpec with bool result |
| `OrderQueue.item_state(order_id)` | OpaqueSpec with string-kind result |

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
Proven:  ██████████  7  done
Assembly:███████     5  needs OpaqueSpec entries
Future:  ████████████ 8  needs new features
```
