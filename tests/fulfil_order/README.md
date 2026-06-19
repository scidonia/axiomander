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

| Test | Status | Details |
|---|---|---|
| `test_phase3_generates` | PASS | Pipeline-smoke test (kept, not a real use case) |
| `test_set_membership_postcondition` | PASS | String set -> String.eqb disjunction |
| `test_string_postcondition` | PASS | LitString RVal arm via result-kind dispatch |
| `test_string_guard_while_single_cell` | PASS | wp_while_str Hoare rule, coinduction-free |
| `test_fulfil_order_composition` | PASS | Full specification graph verifies |

Removed: `test_phase3_compiles` (string-conditional while -- not a real loop shape)
         `test_multicell_while_loop` (pure-counter while -- opaque DB calls, not heap cells)

## Contract Elements Tracker

The implementation uses a DB-theory architecture (opaque callee contracts) rather
than local heap cells + ghost state.  Contract elements map as follows:

```
requires OrderQueue.contains          ☑ OpaqueTerm (trusted theory guarantee)
requires Order.status == "ready"      ☑ OpaqueTerm (trusted theory guarantee)
requires Payment.state == "authorized" ☑ OpaqueTerm (trusted theory guarantee)
requires Inventory.can_reserve        ☑ OpaqueTerm (trusted theory guarantee)

owns queue_item                       □ Deferred -- ownership via callee FunSpec
owns order_row                        □ Deferred -- ownership via callee FunSpec
owns payment_auth                     □ Deferred -- ownership via callee FunSpec
owns stock                            □ Deferred -- ownership via callee FunSpec

frame may_modify                      ☑ Parsed; reads/writes in callee contracts
frame must_not_modify                 ☑ Parsed -- deferred to frame lemmas
frame may_emit / must_not_emit        □ Deferred -- event log ghost theory

ensures result.status in {...}        ☑ Parsed; compiles to OpaqueTerm (struct result deferred)
ensures result == "fulfilled" -> ...  ☑ Parsed as implies(); observer chain as OpaqueTerm
ensures result == "failed" -> ...     ☑ Parsed as implies(); observer chain as OpaqueTerm
ensures exactly_once_domain_effect    ☑ Parsed; trusted from CAS theory guarantee

preserves GlobalInvariant.*           ☑ Parsed; deferred to invariant model
```

☑ = parsed/handled · □ = not yet built
