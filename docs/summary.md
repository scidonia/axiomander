# Staged Proof Session Summary

## Goal
Per-CCall staged proofs to fix 5 failing CCall tests (target 110/110).

## Done
| Item | Location |
|------|----------|
| `wp_monotone` lemma | `coq/WpTactics.v` |
| `wp_seq_decompose` lemma | `coq/WpTactics.v` |
| Complete staged proof for `frame_two_calls` | `coq/StagedFinal.v` |
| coq-lsp MCP issues report | `docs/coq-lsp-mcp-issues.md` |
| Ghost-var bullet nesting fixed (`--`/`---`) | `py/oracle/mcp_server.py` |
| Test baseline preserved | 105/110 pass |

## Staged Proof Template (proven in StagedFinal.v)

### Q_mid (intermediate assertion)
Per CCall k, carries: `target_post /\ isVZ(s,target)=true /\ ⋀_v (asZ(s,v)=val_v /\ isVZ(s,v)=true)`

### Stage 1 lemma (from init_state)
```coq
intros params Hpre. wp_reduce. split.
  - unfold lget, upd, updZ; cbn. split; [apply Hpre | reflexivity].
  - intro r. intro Hr. split.
    + unfold Q1; cbn. unfold lget, upd, updZ; simpl. rewrite Hr. repeat split; reflexivity.
    + apply (wp_ccall_frame _ target nil r).
```

### Stage k>0 lemma (from arbitrary state with frame hyps)
```coq
intros params s Hpre. (intros Hv_asZ Hv_isVZ)* per frame var.
wp_reduce. split.
  - unfold asZ in Hdep_asZ. unfold lget. rewrite Hdep_asZ. split; [apply Hpre | assumption].
  - intro r. intro Hr. split.
    + unfold Qk; simpl. unfold lget, asZ in *. rewrite Hr. repeat split; reflexivity.
    + apply (wp_ccall_frame _ target nil r).
```

### Final assignment
```coq
simpl. unfold lget.
destruct (s "a2") as [za | | | | | | | | | |] eqn:Ea2; simpl;
  try (exfalso; simpl in Ha22_eq; lia).
destruct (s "b2") as [zb | | | | | | | | | |] eqn:Eb2; simpl;
  try (exfalso; simpl in Hb2_eq; lia).
simpl in Ha22_eq, Hb2_eq, Ha2_eq2, Hb2_eq2.
simpl. rewrite Ha22_eq, Hb2_eq, Ha2_eq2, Hb2_eq2. lia.
```

### Main proof chaining
```coq
apply (wp_seq_decompose c1 (CSeq c2 c3) (Q1 params) Q_final _).
{ apply stage_1_correct. assumption. }
{ intros s1 Hq. unfold Q1 in Hq. destruct Hq as [Ha2_eq [Ha2_v [Ha_eq ...]]].
  apply (wp_seq_decompose c2 c3 (Q2 params) Q_final _).
  { apply stage_2_correct with specific args. }
  { intros s2 Hq2. unfold Q2 in Hq2. destruct Hq2 as [...]. ... }
}
```

## Key Discoveries
1. Named binders `(H : P) -> Q` illegal in Coq arrow chains — must use bare `P -> Q`
2. Coq bullets: `-`/`+`/`*` are same depth, cannot nest (`--` required)
3. `unfold lget` in hyps needed for `rewrite` to match (coercion `s "v"` vs definition `lget s "v"`)
4. `simpl` not `cbn` for final assignment (no lget exclusion)
5. Non-VZ elimination: `exfalso; simpl in H; lia` in destruct `try` blocks (discriminate fails on Z)
6. `vm_compute` blows up goal; `simpl` is correct

## Generator Blocked On
Q_mid target conjunct must use caller-visible values (e.g., `a+1`), not callee-internal `asZ(s "x")+1`. Correct approach:
1. Look up callee's contract from `full_tree` AST
2. Extract postcondition RHS
3. Substitute formal params with actual args
4. Substitute `result` with target
This is AST manipulation, not string parsing. The `+1` hardcoding is wrong.

## coq-lsp MCP Issues (docs/coq-lsp-mcp-issues.md)
1. `coq_insert_tactic` replaces instead of inserting when inside bullets
2. `coq_try_tactic` fails with "illegal begin of vernac" after prior insertions
3. `coq_apply_edit` JSON escaping is error-prone
4. `coq_undo` span counting doesn't map cleanly to tactic count
5. Position sensitivity: character column matters for goal inspection

## Base Commit
7299752 - "Complete staged proof for frame_two_calls"
