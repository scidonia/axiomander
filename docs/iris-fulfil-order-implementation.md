# Iris Verification of `fulfil_order` — Implementation Plan

This document maps the `fulfil_order` strong contract (from *Strong Contracts for
AI-Written Python*) through the Axiomander Iris verification pipeline.  Each
contract element is decomposed into its WP calculus form and assigned a build
stage.

---

## The Contract

```python
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
```

---

## 1. Contract Element Breakdown

### 1.1 Preconditions (`requires`)

Four facts must hold before the function executes.  Each corresponds to a
separation-logic resource in the caller's proof context.

| Precondition | Coq model | Status |
|---|---|---|
| `OrderQueue.contains(order_id)` | `queue_contains order_id` ∈ ghost state | Needs `queue` ghost theory |
| `Order(order_id).status == "ready"` | `l_order_status ↦ LitString "ready"` | **Have:** heap cells ✓ |
| `Payment(order_id).state == "authorized"` | `l_payment_state ↦ LitString "authorized"` | **Have:** heap cells ✓ |
| `Inventory.can_reserve(items)` | `Forall items (λ i, available i >= quantity i)` | Needs `Forall` + `Z` arithmetic (**have Forall**) |

### 1.2 Resource Ownership (`owns`)

Four exclusive resources are transferred to the callee.  In Iris this is
ownership of the corresponding ghost locations.

| Resource | Iris model | Status |
|---|---|---|
| `OrderQueue.item(order_id)` | `ghost_map_frag queue order_id item` | Needs ghost state |
| `Orders.row(order_id)` | `l_row ↦ Row order_id` | **Have:** heap cells ✓ |
| `Payment.authorization(order_id)` | `l_auth ↦ LitString "authorized"` | **Have:** heap cells ✓ |
| `Inventory.reservation_rights(items)` | `ghost_map_frag inv_r items` | Needs ghost state |

**Status:** Heap cells exist (`l ↦ v`).  Ghost maps (`ghost_map`) need to be
added as a Snakelet resource.  This is a Phase 5 feature.

### 1.3 Frame Conditions (`frame`)

The frame disciplines what the callee may/must-not touch.  In Iris this is the
**separation-logic frame**: the caller proves that resources not in the
`may_modify` set are unchanged across the call.

| Clause | Iris model | Status |
|---|---|---|
| `may_modify Orders.row(order_id)` | `l_row ↦ ? ⊢ l_row ↦ ?'` via `wp_store` | **Have ✓** |
| `may_modify OrderQueue.item(order_id)` | Same pattern | Needs ghost map |
| `may_modify Inventory.reservations` | Same pattern | Needs ghost map |
| `may_modify Payment.capture(order_id)` | Same pattern | **Have ✓** |
| `may_emit EventBus.topic("orders.fulfilled")` | `eventbus ↦∗ events ++ [e]` | Needs event log ghost theory |
| `must_not_modify Orders.rows(except=order_id)` | Frame proof: `∀ l'≠l, l'↦v ∗ Frame` | **Proved** via `wp_while_inv_gen` frame |
| `must_not_modify Inventory.stock_totals(except=…)` | Same pattern | Needs ghost map |
| `must_not_emit EventBus.topic(except=…)` | `events' = events` for other topics | Needs event log |

**Status:** Per-callee frame lemmas are under construction (`docs/frame-lemmas.md`).
The frame infrastructure is being built.

### 1.4 Postconditions (`ensures`)

Four categories of postcondition, each producing a WP obligation.

#### 1.4.1 Result status obligation

```coq
fun r => match r with
| RVal v => v.status ∈ {"fulfilled", "failed_recoverably"}
| RExn _ => False
end
```

**Status:** Postcondition compilation via `iris_prop` / `contract_ir_iris`.
Membership in sets needs `set` model or `or` enumeration.  **Have:** `and`/`or`
logic in postconditions ✓.

#### 1.4.2 Successful fulfilment obligation

```coq
v.status = "fulfilled" ->
  l_order_status ↦ LitString "fulfilled" ∧
  l_payment_state ↦ LitString "captured" ∧
  ⌜reserved_for(order_id, items)⌝ ∧
  l_queue_state ↦ LitString "completed" ∧
  ∃ e, e.topic = "orders.fulfilled" ∧
       e.payload.order_id = order_id ∧
       e.payload.worker_id = worker_id
```

**Status:** Core postcondition shape is supported (heap cells with `↦` in the
`RVal` arm of the Result match).  Event log existence needs ghost theory.

#### 1.4.3 Recoverable failure obligation

```coq
v.status = "failed_recoverably" ->
  l_order_status ↦ _ ∈ {"ready", "fulfilment_pending"} ∧
  l_payment_state ↦ _ ∈ {"authorized", "capture_pending"} ∧
  l_queue_state ↦ _ ∈ {"ready", "retry"} ∧
  ⌜no_lost_inventory(order_id)⌝
```

**Status:** Same shape as above.  `no_lost_inventory` is a domain predicate
that needs a domain-model definition.

#### 1.4.4 Exactly-once domain effect

```coq
forall (h : list HistoryEvent),
  count (fun e => e.op = "fulfil" ∧ e.order_id = order_id ∧ e.ok = true) h <= 1
```

**Status:** This is a **linearizability/atomicity** property that requires a
history model.  This is Phase 6+ — beyond the current scope.  It can be
deferred: the callee *preserves* it, meaning it relies on an external invariant.

### 1.5 Invariant Preservation (`preserves`)

Three global invariants must be maintained across the call.

In Iris, global invariants are proven via `iInv` (opening an invariant) and
re-establishing it.  This requires:
- Defining the invariant as an `iProp`
- Proving that the function body re-establishes it after modification
- Boxing the invariant as `□ (Inv ...)` in the caller's context

| Invariant | Required model |
|---|---|
| `accounting_consistency` | `Payment.state ∝ Orders.row.state` |
| `inventory_nonnegative` | `Forall items (λ i, reserved_i + available_i <= total_i)` |
| `queue_order_correspondence` | `Queue.item.state ∝ Orders.row.state` |

**Status:** Ghost state + invariants are a Phase 5+ feature.  The Iris
`inv_GS` and `cinv` infrastructure is available from the Iris library.

---

## 2. Decomposition into Sub-contracts

The top-level contract motivates three helper functions, each with its own
(lighter) contract:

1. **`capture_payment(order_id)`** — takes `Payment.authorization`, produces
   `Payment.capture`, preserves `idempotent_effect`.
2. **`reserve_inventory(order_id, items)`** — takes `Inventory.reservation_rights`,
   produces `Inventory.reservations`, preserves `no_negative_stock`.
3. **`update_order_and_emit(order_id, worker_id)`** — updates `Orders.row`,
   `OrderQueue.item`, emits `EventBus` event.

Each helper's contract is verified independently, then composed at the call site
via the multi-function callee table (already built: `_build_iris_callee_table`).

This is the **specification graph** pattern:
```
fulfil_order
    ├── capture_payment ── proves idempotent_effect
    ├── reserve_inventory ── proves no_negative_stock
    └── update_order_and_emit ── proves exactly_one_emit
```

---

## 3. Iris WP Calculus Mapping

### 3.1 What we have today

| Feature | Coverage |
|---|---|
| Heap cells (`l ↦ v`) | ✓ load / store / alloc |
| Pure values (`LitInt`, `LitBool`, `LitString`, `LitList`) | ✓ |
| While loops (heap-counter) | ✓ `wp_while_inv` |
| For loops over lists | ✓ `wp_for_list'` |
| Opaque/transparent calls | ✓ `wp_call` / `wp_call_unfold` |
| Exceptions (raise/try) | ✓ `wp_raise` / `wp_try_*` |
| List operations (append, len) | ✓ `AppendOp` / `LengthOp` |
| Postcondition comparisons | ✓ Z-scope (`<=?` + `= true`) |
| Multi-function verification | ✓ callee table auto-discovery |

### 3.2 What's needed for `fulfil_order`

| Feature | Effort | Priority |
|---|---|---|
| Ghost state (`ghost_map`) | 2 days | Phase 5 |
| Invariant infrastructure (`iInv`) | 1 day | Phase 5 |
| Event log (append-only ghost resource) | 2 days | Phase 5 |
| Set-membership postcondition (`∈`) | 1 day | Phase 4 |
| String-value postconditions | 1 day | Phase 3 |
| Domain predicates (`no_lost_inventory`) | Per-function | Phase 4 |
| History model (`exactly_once`) | 5+ days | Phase 6 |
| Frame-condition automation | 3 days | Phase 4 |
| Docstring `axiomander:` parser for Iris | 1 day | Phase 3 |

### 3.3 Incremental path

The contract can be verified incrementally:

**Phase 3 (current):** Verify the heap-cell portion — `Orders.row(order_id)`
and `Payment` state transitions.  Defer ghost state, event bus, and history
properties.

**Phase 4:** Add set-membership postconditions, domain predicates, and
frame-condition lemmas.  At this point the `status == "fulfilled"` arm of the
postcondition is fully verified for the heap cells.

**Phase 5:** Add ghost state for `Inventory.reservations`, event log, and
global invariants.  The `preserves` clauses become provable.

**Phase 6:** Add the history model for `exactly_once_domain_effect`.  This
requires a trace/history semantics and is the hardest piece.

---

## 4. Example: Phase 3 Verification of the Heap-Cell Portion

A stripped-down version of the contract that works with today's Iris backend:

```python
def fulfil_order_v1(order_id: str, worker_id: str) -> str:
    assert order_id != ""
    # Ownership: assert-style (no ghost state yet)
    # Preconditions: cell states
    c_status = ref("ready")        # Orders.row(order_id).status
    c_payment = ref("authorized")  # Payment(order_id).state
    c_queue = ref("ready")         # OrderQueue.item(order_id).state

    while load(c_status) == "ready":
        # capture payment
        store(c_payment, "captured")
        # reserve inventory (omitted)
        # update order
        store(c_status, "fulfilled")
        store(c_queue, "completed")
        # emit event (omitted)

    result = load(c_status)
    assert result in {"fulfilled", "failed"}
    assert implies(result == "fulfilled",
        load(c_status) == "fulfilled" and
        load(c_payment) == "captured" and
        load(c_queue) == "completed")
    return result
```

**Coq WP goal generated by the Iris pipeline:**

```coq
Lemma fulfil_order_v1_correct (order_id : Z) (worker_id : Z) :
    ((order_id <> 0)) ->
    ⊢ WPE
      (Let "c_status" (Alloc (Val (LitString "ready")))
      (Let "c_payment" (Alloc (Val (LitString "authorized")))
      (Let "c_queue" (Alloc (Val (LitString "ready")))
      (Let "_"
        (While (BinOp EqOp (Load (Var "c_status")) (Val (LitString "ready")))
          (Let "_" (Store (Var "c_payment") (Val (LitString "captured")))
          (Let "_" (Store (Var "c_status") (Val (LitString "fulfilled")))
          (Store (Var "c_queue") (Val (LitString "completed"))))))
      (Let "result" (Load (Var "c_status")) (Var "result"))))))
      {{ (fun r => match r with
          | RVal v => ⌜(v ∈ {"fulfilled", "failed"})%string⌝
          | RExn _ => False
          end)%I }}.
```

**What works here:** Multiple heap cells, while-loop with invariant
(`wp_while_inv_gen`), postcondition with string equality.

**What's deferred:** Membership check (`∈`), ghost state for inventory,
event log, exactly-once semantics.

---

## 5. Implementation Sequence

```
                 now ────────────────────────────────────────────► future

Phase 3      Phase 4           Phase 5               Phase 6
───────      ───────           ───────               ───────
heap cells   set ∈ post       ghost_map             history model
↦ load/store frame lemmas     invariants (iInv)     exactly-once
wp_while     domain preds     event log             linearizability
wp_for_list  str post         preserves clauses
callee table axiomander: parser  
```

Each phase adds one contract element fully, with its own tests, before moving on.
The specification graph (`fulfil_order` → `capture_payment` / `reserve_inventory`)
is verified bottom-up: helpers first, then the composed top-level function.

---

## 6. What a Verified `fulfil_order` Looks Like

When all phases are complete, the Coq lemma looks like:

```coq
Lemma fulfil_order_correct (order_id worker_id : Z) (Σ : gFunctors) :
    (* Ghost resources: queue, payment auth, inventory rights *)
    own_queue_item order_id ∗
    own_order_row order_id ∗
    own_payment_auth order_id ∗
    own_inv_reservation_rights (Order_items order_id) -∗
    (* Preconditions *)
    ⌜OrderQueue_contains order_id⌝ ∗
    ⌜Order_status order_id = "ready"⌝ ∗
    ⌜Payment_state order_id = "authorized"⌝ ∗
    ⌜Inventory_can_reserve (Order_items order_id)⌝ -∗
    (* Global invariants *)
    □ accounting_consistency_inv ∗
    □ inventory_nonnegative_inv ∗
    □ queue_order_correspondence_inv -∗
    WPE (Call "fulfil_order" [Val (LitInt order_id); Val (LitInt worker_id)])
      {{ fun r => match r with
          | RVal v =>
              ⌜FulfilmentResult_status v ∈ {"fulfilled", "failed_recoverably"}⌝ ∗
              ⌜(status = "fulfilled") ->
                  order_status = "fulfilled" ∧
                  payment_state = "captured" ∧
                  inventory_reserved_for order_id items ∧
                  queue_state = "completed" ∧
                  event_emitted "orders.fulfilled" order_id worker_id⌝ ∗
              ⌜(status = "failed_recoverably") ->
                  order_status ∈ {"ready", "fulfilment_pending"} ∧
                  payment_state ∈ {"authorized", "capture_pending"} ∧
                  queue_state ∈ {"ready", "retry"} ∧
                  no_lost_inventory order_id⌝ ∗
              ⌜exactly_once_fulfilment order_id⌝
          | RExn _ => False
          end }}.
```

This is the gold-standard WP goal — one strong contract, one sound proof.
