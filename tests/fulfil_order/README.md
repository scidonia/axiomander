# fulfil_order — Test Fixture

This directory is the verification test fixture for the `fulfil_order`
strong contract from "Strong Contracts for AI-Written Python."

## Files

| File | Purpose |
|---|---|
| `contract.py` | Full docstring contract (target, not yet verifiable) |
| `phase3_assert.py` | Phase 3 heap-cell subset (generates today) |
| `test_fulfil_order.py` | pytest suite tracking incremental progress |

## Running

```bash
cd /path/to/axiomander
eval $(opam env)
PYTHONPATH=py python3 -m pytest tests/fulfil_order/ -v
```

## Progress

| Test | Status | Blocker |
|---|---|---|
| `test_phase3_generates` | ✅ PASS | — |
| `test_phase3_compiles` | ❌ XFAIL | EqOp on LitString (binop_eval) |
| `test_set_membership_postcondition` | ❌ XFAIL | `∈` compilation in iris_prop |
| `test_string_postcondition` | ❌ XFAIL | LitString in RVal arm of postcondition |
| `test_multicell_while_loop` | ❌ XFAIL | wp_while_inv_gen (IPM pattern) |

## Contract Elements Tracker

```
requires OrderQueue.contains          □ Phase 5 (ghost state)
requires Order.status == "ready"      □ Phase 3 (LitString heap cell)
requires Payment.state == "authorized" □ Phase 3 (LitString heap cell)
requires Inventory.can_reserve        □ Phase 5 (ghost state)

owns queue_item                       □ Phase 5 (ghost state)
owns order_row                        □ Phase 3 (heap cell)
owns payment_auth                     □ Phase 3 (heap cell)
owns stock                            □ Phase 5 (ghost state)

frame may_modify                      □ Phase 4 (frame lemmas)
frame must_not_modify                 □ Phase 4 (frame lemmas)
frame may_emit / must_not_emit        □ Phase 5 (event log ghost)

ensures result.status in {...}        □ Phase 4 (set membership)
ensures result == "fulfilled" -> ...  □ Phase 3 (heap cells + implies)
ensures result == "failed" -> ...     □ Phase 3 (heap cells + implies)
ensures exactly_once_domain_effect    □ Phase 6 (history model)

preserves GlobalInvariant.*           □ Phase 5 (invariants)
```

□ = not yet built · ■ = in progress · ☑ = verified
