# Dual Search: Simultaneous Proof and Refutation at Level 3

## The problem

SMT and interactive proof give asymmetric information on failure:

- **SMT** decides `unsat(phi)`. When *satisfiable*, the solver returns a
  **model** — a concrete witness showing the property is false. A failed SMT
  check is *informative*: you get a counterexample.
- **Interactive proof** produces a proof obligation `O`. When we *cannot
  prove* `O`, we learn almost nothing. The failure is ambiguous:
  1. `O` is true but hard (we need a better proof / a lemma), or
  2. `O` is **false** (the contract is wrong, or the code is buggy).

The current pipeline collapses both into `UNPROVED → retry_llm`. That is the
single least useful diagnostic we emit. A user staring at "could not prove"
has no idea whether to fix their code, fix their spec, or add a hint.

## The idea

At Level 3, **search for a proof of `O` and a proof of `~O` simultaneously.**
Three outcomes instead of two:

| Outcome | Meaning | What we return |
|---|---|---|
| Prove `O` | Contract holds | `VERIFIED` + proof term |
| Prove `~O` | Contract is **false** | `REFUTED` + counterexample + kernel-checked disproof |
| Neither (timeout) | Genuinely hard | `UNKNOWN` — *now* this honestly means "weak automation" |

By consistency, `O` and `~O` can never both be proved, so a refutation is a
genuine disproof, not a heuristic guess. And because the disproof is
kernel-checked, the counterexample is **sound** — unlike an SMT model, which
can be spurious if the SMT encoding diverges from the real semantics.

This directly closes the failure-classification gap in AGENTS.md
("distinguish 'bug' vs 'missing lemma' vs 'weak automation'"):

- `REFUTED` ⟹ bug or wrong spec (with a concrete witness)
- `UNKNOWN` ⟹ weak automation / missing lemma
- `VERIFIED` ⟹ correct

## Why this is cheap in Axiomander specifically

The decisive observation: **concrete counterexamples are trivially provable in
Coq by computation.**

A WP obligation, after stripping the WP layer, has the shape:

```
O  ≡  forall inputs, Pre(inputs) -> Post(eval(body, inputs))
```

The body is (essentially) deterministic, so `eval(body, ·)` is a function.
The negation is existential:

```
~O ≡  exists inputs, Pre(inputs) /\ ~Post(eval(body, inputs))
```

If we can *exhibit* concrete input values `c` with `Pre(c)` true and
`Post(eval(body, c))` false, the disproof is mechanical:

```coq
Lemma contract_false : ~ O.
Proof.
  intros H.
  specialize (H c).        (* instantiate at the witness *)
  compute in H.            (* Pre(c) reduces to True, Post(...) reduces to False *)
  discriminate.            (* True -> False is absurd *)
Qed.
```

Everything is closed and concrete, so `compute`/`vm_compute` reduces it and
the kernel checks the contradiction. **No search inside Coq is needed — the
search happens outside, the verification is by reduction.**

We already have every piece:

- **`snakelet_eval.py`** — a Python interpreter for SnakeletLang that mirrors
  the Coq semantics. Run candidate inputs concretely, fast, to *find* a
  counterexample before paying for any Coq.
- **`property_test_gen.py`** + Hypothesis — a refutation search engine that
  generates inputs satisfying the precondition and checks the postcondition.
- **`COUNTEREXAMPLE` status** — already in `reporting.py`; today only the SMT
  path populates it. Dual search extends it to the *whole* fragment.

## Architecture

```
Level 3 obligation  O = (forall inputs, Pre -> Post)
        │
        ├── PROVER lane ──────────────────────────────────────────┐
        │     LLM proposes a Coq script for O; kernel checks it.   │
        │                                                          │
        ├── REFUTER lane ─────────────────────────────────────────┤
        │     1. Generate candidate inputs satisfying Pre:         │
        │          a. property testing (Hypothesis strategies)     │
        │          b. SMT model, when O is in the SMT fragment      │
        │          c. LLM-guided input synthesis (hard fragment)    │
        │     2. Run each via snakelet_eval (concrete, fast).      │
        │     3. On first input where Post fails → witness c.       │
        │     4. Emit the disproof lemma; kernel checks by compute. │
        │                                                          │
        └── race: first lane to a kernel-checked result wins ──────┘
                 prover  → VERIFIED  (proof term)
                 refuter → REFUTED   (witness + disproof, kernel-checked)
                 both fail within budget → UNKNOWN
```

The two lanes are complementary, not redundant: the prover is strong when the
property is true; the refuter is strong (and fast) when it is false. Running
both means we never waste the full budget proving something that is false, and
we never waste it refuting something that is true.

## The LLM explanation loop — grounded, not hallucinated

When the refuter wins, we have a **kernel-checked disproof** plus a concrete
witness. Feed the LLM:

1. The witness inputs (`c`).
2. The execution trace from `snakelet_eval` (statement-by-statement state).
3. The expected vs. actual postcondition values.
4. The original contract.

Prompt: *"This contract is provably false. Here is a concrete input, the
execution trace, and the failing postcondition. Explain why — is it a bug in
the code, a wrong specification, or a missing precondition? Suggest the
minimal fix."*

The crucial property: the LLM is **explaining a verified fact**, not deciding
truth. It cannot hallucinate a non-existent failure, because the failure is
already kernel-certified. The LLM's only job is natural-language diagnosis and
fix suggestion. This is the safe, valuable use of an LLM in a verifier:
narration of machine-checked facts.

Example output:

```
REFUTED: classify_failure

  Counterexample:
    goal_name = "x", error = "type error", has_loop = True
  Trace:
    error_lower = "type error"
    branch 1 (has_loop and "inv"/"invariant"): false  ("inv" not in "type error")
    branch 6 ("type error"): result = 3
  Contract claims: result == 0   (from `implies(has_loop, result == 0)`)
  Actual:          result == 3

  Diagnosis: the contract's first clause is too strong. `has_loop` alone does
  not force result 0; the error must also mention "invariant". The clause
  should be `implies(has_loop and "invariant" in error.lower(), result == 0)`.
```

## Relationship to existing components

| Component | Role in dual search |
|---|---|
| `snakelet_eval.py` | Concrete evaluator — finds & validates witnesses cheaply |
| `property_test_gen.py` | Refuter input generator (Hypothesis strategies) |
| `theory_smt` / cvc4-z3 | One refuter source (SMT model) for the decidable fragment |
| LLM oracle | (a) prover lane; (b) input synthesis for hard refutations; (c) explanation |
| `reporting.py` COUNTEREXAMPLE | Result status, already present — extend population path |
| `capture_residual` | On UNKNOWN, still emit the residual goal for the prover |

## Soundness

- A `REFUTED` result is backed by a Coq term of type `~O` checked by the
  kernel. It is as trustworthy as a `VERIFIED` result. This is *strictly
  stronger* than an SMT counterexample, which is only as trustworthy as the
  SMT encoding's fidelity to the real semantics.
- The refuter's *search* (property testing, SMT model, LLM synthesis) is
  untrusted — it only *proposes* witnesses. The witness is then validated by
  `snakelet_eval` (fast filter) and finally certified by the kernel disproof
  (the real guarantee). A bad proposal simply fails to certify and is
  discarded.

## Implementation plan

### Step 1 — Disproof emitter

**New:** `refutation.py`

Given an obligation's contract IR, a return-variable name, and a witness
(concrete input values), emit:

```coq
Lemma <name>_refuted : ~ (<obligation>).
Proof. intros H. specialize (H <witness>). vm_compute in H. discriminate. Qed.
```

Validate with `coqc`. The witness comes from the refuter lane.

### Step 2 — Refuter lane

Wire `property_test_gen.py` to *return the first failing input* rather than
just pass/fail. Run candidates through `snakelet_eval` directly (no Coq) for
speed; only the surviving witness goes to Step 1.

### Step 3 — Race harness

At Level 3, launch prover and refuter concurrently with a shared deadline.
First kernel-checked result wins. Record which lane won.

### Step 4 — Explanation

On `REFUTED`, build the trace from `snakelet_eval` (extend it to log
per-statement state) and prompt the LLM for a diagnosis + minimal fix. Emit
under the existing `suggestion_text` / `counterexample` fields.

### Step 5 — Status & reporting

Populate `ProofLevel.COUNTEREXAMPLE` from the refuter (today only SMT does).
Map to `GoalOutcome.COUNTEREXAMPLE`. The MCP report shows the witness, trace,
and diagnosis.

## Priority

| Step | Impact | Effort |
|---|---|---|
| 1 — disproof emitter | High | Low (compute + discriminate is mechanical) |
| 2 — refuter lane (reuse property_test_gen + snakelet_eval) | High | Low–Medium |
| 3 — race harness | Medium | Low |
| 4 — grounded LLM explanation | Very high (UX) | Medium |
| 5 — reporting | Medium | Low |

## Why this matters

It turns the verifier's *worst* output ("could not prove, retry") into its
*most* valuable one ("this contract is false; here is the input that breaks
it; here is the fix"). And it does so **soundly** — the counterexample is
kernel-checked, the LLM only narrates. No comparator (Dafny, Nagini, Liquid
Haskell, F*) combines: full-fragment refutation (beyond SMT's decidable
reach), kernel-checked counterexamples, and LLM-narrated diagnosis. This is a
second genuine differentiator alongside the sound-LLM-prover tier.
