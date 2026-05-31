# Per-Obligation Verification Architecture

## Goal
Replace monolithic `foo_correct` proofs with **per-obligation Coq theorems** (pre, post, frame-per-variable, CCall-stage). Each obligation gets its own tactic ladder, structured residual capture on failure, and obligation-level caching. LLM is reduced to patching a single small obligation, never a whole function.

## Phase 1 — `Obligation` Data Model (`py/oracle/obligations.py`)
Introduce a new module so nothing existing breaks. Define:

```python
@dataclass
class Obligation:
    id: str                     # "frame_two_calls.inc.frame_a"
    kind: Literal["pre", "post", "frame", "ccall_stage", "loop_inv", "loop_exit"]
    theorem_name: str           # Coq theorem identifier
    theorem_statement: str      # full "Theorem ... : ... ."
    proof_attempts: list[ProofAttempt]   # tactic ladder run
    status: ObligationStatus    # PROVED | RESIDUAL | COUNTEREXAMPLE
    residual: ResidualGoal | None
    dependencies: list[str]     # ids of other obligations relied on

@dataclass
class ProofAttempt:
    tactic: str                 # "wp_reduce", "lia", "apply inc_frame_a", "hammer"
    level: ProofLevel
    outcome: Literal["closed", "no_progress", "error"]
    elapsed_ms: float
    error: str | None

@dataclass
class ResidualGoal:
    hypotheses: list[str]       # printed hypothesis lines from coq-lsp
    goal: str                   # printed conclusion
    coq_fragment: str           # standalone .v that reproduces the goal
```

Map each `Obligation` 1:1 to a Coq `Theorem`/`Lemma`, never embedded inside a larger proof.

## Phase 2 — Obligation Generator for CCall Functions
New module `py/oracle/obligation_gen.py`. Input: `(func_node, imp_ir, contract_map, params, ghost_vars, pre_coq, post_coq)`. Output: `list[Obligation]`.

Generation rules:
1. **Pre obligation** — `Theorem {name}_pre : forall <params>, ({pre_coq}) -> wp <body_prefix> Q_1 (init_state)`. Only when the body starts with non-call setup.
2. **CCall-stage obligation per CCall** — `Theorem {name}_stage_{k} : forall <params> <intermediate_state>, <hyps_from_prev_stage> -> wp s_{k} (Q_{k}) state_{k}.`
3. **Frame obligation per (callee, frame_var)** — `Lemma {callee}_frame_{var}[_{target}] : forall (s : state) (r : Z), ~ In "{var}" ("{target}" :: {writes}) -> lget s "{var}" = lget (clobber (lupd s "{target}" (VZ r)) {writes}) "{var}".` (Fix the `writes_list` quoting bug here.) Multi-call callees get target-suffixed names; deduplicated by `(callee, var, target, writes)` tuple.
4. **Post obligation** — `Theorem {name}_post : forall <params>, <accumulated_Qs> -> ({post_coq})`. Single arithmetic/logical step at the end.
5. **Composition theorem** — `Theorem {name}_correct` constructed by `apply` chaining the above. This becomes mechanical; if any sub-`apply` fails, the failure is localized to one obligation id.

For non-CCall functions, fall through to the existing whole-function path (no regression).

## Phase 3 — Per-Obligation Tactic Ladder
New module `py/oracle/ladder.py`. For each obligation kind:

| Kind | Ladder |
|------|--------|
| `frame` | `intros s r H. apply (wp_ccall_frame s "<target>" <writes> r "<var>"). assumption.` |
| `pre` | `intros. wp_reduce. (split / repeat split). (assumption | lia | reflexivity).` |
| `ccall_stage` | `intros ... . wp_reduce. split.` then `[lia / assumption]` and `intro r; intro Hr; split; [cbn; repeat split; auto / apply (wp_ccall_frame ...)]` |
| `post` | `intros. repeat (match goal with H: _ /\ _ \|- _ => destruct H end). lia.` |
| `loop_inv` / `loop_exit` | existing VCG ladder, but emitted as a standalone theorem |

Each tactic is tried in isolation against a single-obligation `.v` file. On failure, capture goal + hypotheses via coq-lsp (`focus_proof` + `open_goals`) into a `ResidualGoal`.

## Phase 4 — Residual Capture & Artifacts
On obligation failure, write to `.axiomander/proofs/{func}/{obligation_id}/`:
- `theorem.v` — standalone theorem statement
- `tactics_tried.json` — ordered list of `ProofAttempt`
- `residual_goal.v` — preamble + theorem + `Proof.` + tactics that fired + `(* GOAL: ... *)`
- `hypotheses.txt` — pretty-printed hypothesis context
- `status.json` — `{kind, status, error, suggested_action}`

These artifacts replace the current "raw coqc stderr" failure capture.

## Phase 5 — Obligation-Level Cache
Extend `py/oracle/cache.py`:
- New `ObligationCacheEntry`: `(theorem_hash, deps_hash, tactic_ladder_hash) -> (status, proof_text)`.
- Key derivation: hash of theorem statement string + transitive callee-contract hashes + ladder version.
- Whole-function cache becomes a derived view: function is "proved" iff all its obligation ids are PROVED.

## Phase 6 — LLM Handoff (Single Obligation)
Modify `_try_llm_oracle`:
- Iterate the function's `RESIDUAL` obligations.
- For each, build a tiny preamble: `Require Imp Wp WpTactics.` + dependency lemmas only (the other proven obligations of this function).
- Pass the single-obligation theorem to `run_langgraph_oracle`. The LLM operates on a 5-line theorem instead of a 200-line monster proof.
- On success, write proof back as `Proof. <tactics>. Qed.`; on failure, save residual + suggested action.

This makes Phase 1's "recursion limit on `frame_two_calls`" disappear: each LLM call has at most one small frame or post obligation.

## Phase 7 — Report Integration (`reporting.py`)
- Extend `GoalStatus` with `obligations: list[ObligationStatus]`.
- `PipelineReport.mcp_output()` prints per-obligation status under each function, so users see exactly which step failed.
- `Action` classification per obligation:
  - `frame` fail → likely missing variable in `frame_vars` set → `ADD_LEMMA`
  - `post` fail with SMT counterexample → `PROPERTY_FALSE`
  - `ccall_stage` fail → `ADD_INVARIANT` or `STRENGTHEN_PRE`
  - `pre` fail → `ADD_PRECONDITION`

## Phase 8 — Wire-In & Migration
- Keep existing `_build_staged_proof` path as fallback (toggle by env var `AXIOMANDER_OBLIGATIONS=1`).
- Add `_verify_function` branch: if function has CCall and feature flag on, route to obligation pipeline.
- All other paths (Level 1 only, loops, pure functions) unchanged.

## Phase 9 — Tests
- New `py/tests/test_obligations.py`:
  - Generator: `frame_two_calls` -> N pre, M ccall_stage, K frame, 1 post obligations with stable ids.
  - Ladder: each obligation kind has at least one test where the deterministic ladder closes the goal.
  - Negative test: deliberately weaken precondition → expect `post` obligation `RESIDUAL` with non-empty `ResidualGoal`.
- Extend `test_pipeline.py`: assert `frame_two_calls`, `frame_old_equals_result`, `frame_triple_compose` reach PROVED through obligation path (regression target: 110/110).

## Phase 10 — Cleanup
- Once obligation path is green for the 5 CCall failures, default `AXIOMANDER_OBLIGATIONS=1`.
- Delete `_build_staged_proof`, `_gen_destruct_and_final_proof`, `_gen_final_assign_proof`, `_get_relevant_hyps_for_stage`, `_get_pre_hyp_name_for_stage` (~450 lines of dead code in `mcp_server.py`).
- Update `docs/frame-lemmas.md` to point at obligations as the canonical mechanism.

## Acceptance Criteria
1. `pytest py/tests/test_pipeline.py` ≥ 110/110.
2. `frame_two_calls` produces ≥ 6 standalone Coq theorems (1 pre, 2 ccall_stage, ≥2 frame, 1 post), each independently proved by Level 1 ladder; the composing `_correct` theorem is one `apply` chain.
3. A deliberately broken obligation produces a `ResidualGoal` artifact with non-empty hypotheses and goal text.
4. Cache hit on unchanged function returns in <50 ms with no Coq invocation.
5. LLM oracle invoked on a single-obligation residual never exceeds 30 recursion steps.

## Open Questions Deferred to Implementation
- Whether `_correct` is a `Theorem` proved by composing obligations or remains a `Definition` of "all obligations PROVED" tracked in Python.
- Exact format of `coq-lsp` residual extraction for hypothesis pretty-printing.
- Whether to make obligation ids stable across renames (using AST position hash) for cache reuse.
