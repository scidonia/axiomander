# MCP Tool Transparency for Interactive Theorem Proving

## Goal

Make theorem-prover MCP tools semi-transparent in opencode so the agent and human can inspect proof activity, failures, and intermediate reasoning.

---

# Recommended Approach

## 1. Enable opencode tool details

Use:

```text
/details
```

This exposes tool-call activity that is otherwise hidden.

---

## 2. Require approval for proof tools

In `opencode.json`:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "permission": {
    "coq_*": "ask",
    "prove_*": "ask",
    "mymcp_*": "ask"
  }
}
```

This forces visible approval boundaries around theorem proving actions.

---

## 3. Return proof transcripts from tools

Do not return opaque JSON blobs.

Every theorem-prover tool should return:

- current goals
- proof script attempted
- prover output
- remaining obligations
- next suggested lemma

Example:

```text
Goal:
  forall xs, sorted (sort xs)

Script attempted:
  induction xs; simpl; auto.

Prover output:
  2 goals remaining

Missing lemma:
  insert_preserves_sorted
```

---

## 4. Emit incremental MCP logs

Use MCP log notifications during execution.

Example (Python):

```python
await ctx.session.send_log_message(
    level="info",
    data=f"Starting proof: {theorem_name}"
)
```

Log:

- theorem names
- tactics executed
- proof states
- SMT queries
- failures
- reconstruction attempts

---

## 5. Persist proof traces to disk

Write every proof attempt to:

```text
.proof-trace/
```

Example:

```text
.proof-trace/
  2026-05-20_insert_preserves_sorted.md
```

This is the canonical audit trail.

---

# Recommended Architecture

The MCP tool should behave like:

```text
LLM
  ↓
MCP Tool
  ↓
Proof Driver
  ↓
Coq / SMT / Iris
```

And expose:

- human-readable transcripts
- structured logs
- persistent trace files
- incremental proof state

rather than only final success/failure.

---

# Key Principle

Treat theorem proving as an observable dialogue, not a black-box RPC call.
