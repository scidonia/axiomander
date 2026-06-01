# rocq-piler `focus_proof` False Completion on Admitted Goals

## Repro File

The precise repro file is included in this repository at:

```text
docs/rocq-piler-focus-admitted-repro.v
```

It was copied from the live failing file:

```text
/tmp/llm_rewrite_test.v
```

Relevant admitted targets in the repro file:

```text
ftc12_stage_2_correct
ftc12_post
ftc12_correct
```

## Bug Description

`rocq-piler focus_proof` gives a false "proof complete" signal on admitted generated obligations.

For the same file, `check_file` correctly reports admitted proof blocks:

```text
rocq-piler check_file docs/rocq-piler-focus-admitted-repro.v
```

Expected excerpt:

```text
3 admitted (138, 146, 156)
Lemma ftc12_stage_2_correct ... [Admitted]
Lemma ftc12_post ... [Admitted]
Theorem ftc12_correct ... [Admitted]
```

But focusing one of those admitted proofs:

```text
rocq-piler focus_proof file=docs/rocq-piler-focus-admitted-repro.v name=ftc12_stage_2_correct
```

returns output shaped like:

```text
goals: 0 at focus
(no goals at focus)

-- proof script ----------
  Proof.

-- admits (1) ----------
  error  L138:
    goal: (could not query)

next: Proof complete. Qed auto-applied.
```

These two results are contradictory:

- `check_file` says the theorem is admitted.
- `focus_proof` says the proof is complete / Qed can be auto-applied.
- `focus_proof` also reports `goal: (could not query)`, which should not be treated as proof completion.

## Expected Behavior

For an admitted theorem like:

```coq
Lemma ftc12_stage_2_correct : ...
Proof.
Admitted.
```

`focus_proof` should either:

- expose the open goal, or
- report clearly that the theorem is admitted / no focused proof state is available.

It should not emit:

```text
Proof complete. Qed auto-applied.
```

when the target remains admitted.

## Actual Behavior

`focus_proof` cannot query the goal:

```text
goal: (could not query)
```

but still emits a misleading completion signal:

```text
next: Proof complete. Qed auto-applied.
```

## Impact on Axiomander

Axiomander's stage-3 proof automation uses rocq-piler to drive an LLM proof loop.
This false-positive completion signal causes the LLM loop to misinterpret the proof state:

1. `check_file` reports admitted targets.
2. `focus_proof` on an admitted target reports "Proof complete".
3. The LLM trusts `focus_proof` and moves on or retries inconsistently.
4. `insert_tactic` may then fail or roll back with goal-query errors.
5. The loop repeats without making progress.

This blocks Axiomander from reliably repairing generated per-obligation proof files.

## Desired Fix

`focus_proof` should treat `goal: (could not query)` inside an admitted proof block as an error / unresolved state, not as completion.

A conservative behavior would be:

```text
Proof is admitted; goal could not be queried.
```

and no `Qed auto-applied` suggestion.
