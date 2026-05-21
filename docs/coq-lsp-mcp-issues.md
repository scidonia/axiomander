# coq-lsp MCP Issues Report

## Summary

The coq-lsp MCP server provides structured goal inspection and tactic execution for
interactive Coq proof development.  Three tools are central:

- `coq_open_goals` — inspect current goals at a file position  
- `coq_try_tactic` — speculatively run a tactic and show new goals  
- `coq_insert_tactic` — insert a tactic into the file and re-sync  

## Issues Encountered

### 1. `coq_insert_tactic` replaces instead of inserting (CRITICAL)

**Observed:** When position is WITHIN a bullet scope, `coq_insert_tactic` replaces
the tactic at that position rather than inserting BEFORE it. Example:

```
File before:
  split.
  - unfold lget. split; [apply Ha | reflexivity].
  - intro r. intro Hr.

Insert "unfold Q_mid_1; cbn" at position (24, 10):
Result: "intro unfold Q_mid_1; cbn. r. intro Hr."
```

The new text REPLACED the character range starting at (24,10), mangling the bullet
structure.

**Expected:** Insert the tactic BEFORE the existing content at that position, preserving
all subsequent proof text.

**Workaround:** Write the full proof text as a single edit rather than inserting
tactics one at a time.

### 2. `coq_open_goals` position sensitivity (MODERATE)

**Observed:** The `position` argument is character-precise.  `After` mode at
`(23, 0)` (start of line) shows the state BEFORE `intro r.` executes, while
`(23, 10)` (after "intro r.") shows the state AFTER.  The line-start position
is ambiguous when multiple tactics are on adjacent lines with bullets.

**Example:**
```
23:   - intro r.
24:     intro Hr. split.
```

- `After (23, 0)` → shows state before split (2 subgoals)  
- `After (23, 10)` → shows implication goal after intro r  
- `After (24, 0)` → shows forall goal (NOT the post-split state)

The coq-lsp server is resolving (24, 0) to the start of the `-` bullet command
at line 23 rather than line 24.

**Expected:** `After` mode at `(line, column)` should consistently show the state
IMMEDIATELY AFTER executing the tactic at that exact position.

### 3. `coq_apply_edit` JSON escaping difficulty (MODERATE)

**Observed:** Multi-line `newText` with backslashes, percent signs, and quotes
causes JSON parsing failures.  The file was in the workspace but escaping `\n`,
`"`, and `%` characters was error-prone.

**Workaround:** Use `edit` tool (file-level replacement) for multi-line edits
and coq-lsp tools only for single-line tactics.

### 4. `coq_try_tactic` fails on bullet-nested proofs (MODERATE)

**Observed:** Running `coq_try_tactic` on a position inside a `-` bullet that
is itself nested produces "Syntax error: illegal begin of vernac."  This happens
because the tactic runner cannot establish a proof context at that position.

**Example:** After previous `coq_insert_tactic` added bullets into the file,
subsequent `coq_try_tactic` calls at positions within those bullets fail.

**Expected:** `coq_try_tactic` should work at any position within an open proof,
regardless of bullet nesting.

### 5. `coq_undo` count uncertainty (MINOR)

**Observed:** `coq_undo n=10` produced "undone 10 span(s), 13 remaining" but the
file state after undo was NOT what it was before the insertions.  The "span"
granularity doesn't clearly map to individual tactic commands.

**Expected:** `coq_undo n` should undo the last `n` tactic insertions, restoring
the file to its state before those insertions.

## What Works Well

- `coq_open_goals` in `After` mode with precise column positions
- `coq_check` for rapid file validation  
- `coq_try_tactic` on files that have NOT been modified by `coq_insert_tactic`
- The compact goal display with hypotheses

## Recommended Workflow

1. Write proofs using the `edit` tool for multi-line changes
2. Use `coq_check` to validate syntax
3. Use `coq_open_goals` with precise positions to inspect intermediate states
4. ONLY use `coq_try_tactic` on clean files (no prior `coq_insert_tactic` edits)
5. AVOID `coq_insert_tactic` — prefer `edit` for all file modifications
