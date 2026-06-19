# iFS Submission Review and Recommendations

## Context

This review is written from the perspective of a supervisor whose goal is to maximize the probability of acceptance at **iFS (Integrated Formal Methods Symposium)**, the successor venue formed from the merger of FASE and iFM.

The current paper:

> *Specification Composition for LLM-Driven Python Verification: Why We Build on Iris*

contains promising ideas, but in its current form it reads more like a workshop position paper than a competitive iFS submission.

The core challenge is not technical correctness. The challenge is contribution framing.

---

# Executive Summary

Current assessment:

* Technical interest: High
* Relevance to iFS: High
* Clarity of motivation: Good
* Evaluation strength: Weak
* Novelty presentation: Unclear
* Acceptance probability (current): ~35–45%

Recommended direction:

Reframe the paper as an **experience report on migrating a verification architecture from an extensional flat-store model to Iris-based separation logic**.

Estimated acceptance probability after restructuring:

* ~65–80%

---

# What Works Well

## 1. The "we built framing manually" story

This is the strongest contribution in the paper.

The paper currently explains:

1. Flat-store WP backend.
2. Explicit clobber sets.
3. Generated frame lemmas.
4. WP explosion.
5. Automation brittleness.
6. Migration to Iris.
7. Native framing.

This is a concrete engineering lesson.

Formal methods reviewers immediately understand:

> If framing is important, trying to reconstruct it manually becomes painful.

This story is stronger than most of the language design material currently occupying the paper.

### Recommendation

Make this the central narrative.

The paper should revolve around:

> What we learned attempting modular verification without separation logic.

---

## 2. Contracts as the unit of composition

The paper correctly identifies three requirements:

* Modular verification
* Proof reuse
* Library stubbing

The observation that all three become instances of the same opaque-call mechanism is valuable.

This should be elevated from supporting material to a primary result.

### Recommendation

Explicitly argue:

> Opaque specifications provide a single abstraction boundary that simultaneously supports:
>
> * modular reasoning
> * proof caching
> * library stubbing

This is arguably the strongest conceptual contribution.

---

## 3. Hiding Iris from end users

The design goal:

> Users write Python contracts, not separation logic.

is interesting.

Most verification systems expose the logic directly.

Axiomander instead compiles contract syntax into iProp.

### Recommendation

Present this as:

> "Separation logic as an implementation detail."

rather than merely an engineering decision.

---

# Major Weaknesses

## 1. Insufficient evaluation

This is the largest risk to acceptance.

The paper claims:

* WP blowup existed.
* Automation became brittle.
* Iris solved the problem.

But it does not provide quantitative evidence.

Reviewers may respond:

> Of course separation logic fixes framing.
>
> What did we learn beyond that?

### Required Fix

Add measurements.

Even a small table would significantly strengthen the paper.

Example:

| Example              | Flat-store obligations | Iris obligations |
| -------------------- | ---------------------- | ---------------- |
| bump                 | 12                     | 3                |
| queue push           | 87                     | 8                |
| stubbed library call | 143                    | 11               |

or

| Example   | Flat backend proof size | Iris backend proof size |
| --------- | ----------------------- | ----------------------- |
| Example A | 220 lines               | 40 lines                |
| Example B | 480 lines               | 75 lines                |

Absolute values matter less than demonstrating a measurable effect.

---

## 2. Excessive space spent on language definition

Large portions of the paper are devoted to:

* Syntax
* Operational semantics
* WP rules

These are useful artifacts but not the most interesting aspect of the work.

### Reviewer Perspective

An iFS reviewer is more likely to care about:

> Why this architecture works

than

> The exact syntax of every expression form.

### Recommendation

Reduce:

* Grammar presentation
* Rule presentation

Expand:

* Experience
* Lessons learned
* Evaluation

---

## 3. Novelty claim is unclear

The paper repeatedly acknowledges:

* The separation logic is standard.
* The opaque call rule is standard.
* The ownership model is standard.

This honesty is appreciated.

However it leaves reviewers asking:

> What exactly is new?

### Recommendation

State a precise thesis.

Suggested thesis:

> The key abstractions required for LLM-driven verification—stubbing, proof reuse, modular verification, and incremental verification—can all be realised as instances of Iris framing and opaque specification boundaries.

This is a stronger and more defensible contribution.

---

## 4. The LLM story is under-evaluated

The paper references:

* LLM-generated code
* LLM-generated specifications
* Residual goals supplied to LLMs

However no evaluation of these claims is presented.

### Reviewer Risk

Formal methods reviewers:

> Why discuss LLMs at all?

LLM reviewers:

> Why is there no LLM evaluation?

The paper risks satisfying neither audience.

### Recommendation

Reduce emphasis on LLMs.

Position them as motivation.

Suggested framing:

> We require modular specification composition because our target workflow is LLM-assisted verification.

rather than:

> This is primarily an LLM paper.

---

## 5. Repeated emphasis on "0 Admitted"

Having a development free of Admitted is good.

However:

* It is expected.
* It is not a contribution.

### Recommendation

Mention it once.

Do not repeatedly return to it.

---

# Recommended Paper Structure

## Title

Current:

> Specification Composition for LLM-Driven Python Verification: Why We Build on Iris

Suggested:

> Lessons from Migrating a Python Verification Pipeline to Iris

Alternative:

> Specification Composition in an LLM-Assisted Verifier: An Experience Report with Iris

Alternative:

> From Flat Stores to Separation Logic: Lessons Building a Python Verifier

All three are stronger iFS titles.

---

## Section 1: Motivation

Introduce:

* Vericoding
* Modular verification
* Proof reuse
* Library stubbing

Explain why composition matters.

---

## Section 2: First Architecture

Describe:

* IMP backend
* Clobber operator
* Generated frame lemmas

Demonstrate where scaling problems appeared.

This should become the emotional centre of the paper.

---

## Section 3: Migration to Iris

Introduce:

* Resource ownership
* Opaque calls
* Framing

Keep formal detail concise.

---

## Section 4: Evaluation

Provide measurements.

This section is essential.

Potential metrics:

* Number of generated obligations
* Proof size
* Verification time
* Cache reuse
* Automation success rate

Even small-scale evidence is valuable.

---

## Section 5: Lessons Learned

Replace most of the current open-question section.

Suggested lessons:

### Lesson 1

Framing is the fundamental abstraction.

### Lesson 2

Opaque specifications unify:

* stubs
* modularity
* proof reuse

### Lesson 3

Incremental verification naturally follows contract boundaries.

### Lesson 4

Resource ownership becomes unavoidable when targeting realistic software.

### Lesson 5

Separation logic is easier to adopt than reconstruct.

---

# Suggested iFS Positioning

Do not position the paper as:

> A new separation logic.

Do not position the paper as:

> A new Iris theory.

Do not position the paper as:

> An LLM evaluation paper.

Instead position it as:

> An experience report showing that the abstractions required by modern AI-assisted verification are naturally provided by Iris, whereas reconstructing them over a traditional flat-store WP architecture leads to scalability and automation problems.

This is a message likely to resonate with the iFS audience.

---

# Final Recommendation

The strongest paper is not:

> "Here is Snakelet."

The strongest paper is:

> "We tried to build modular verification over a flat-store calculus, discovered that framing became the dominant engineering problem, migrated to Iris, and found that stubbing, proof reuse, modular reasoning, and ownership all collapsed into the same underlying abstraction."

That story is interesting, believable, and potentially publishable at iFS.
