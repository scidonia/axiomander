# Vericoding: Specification-Centric Software Development

## Vision

The central claim of vericoding is that AI changes the economics of software development.

Historically, implementation was expensive and verification was secondary. In an AI-assisted world, implementation becomes inexpensive while verification remains difficult. The scarce resource shifts from code production to specification production.

The consequence is a different development model:

Traditional:
Human -> Code -> Tests -> Confidence

Vericoding:
Human -> Specification -> AI -> Implementation -> Verification

Specification becomes the primary maintained artifact. Code becomes a derived artifact.

---

## Abstract

The rise of large language models has reduced the cost of generating implementations but has not reduced the cost of determining whether those implementations satisfy intent. Existing software engineering processes continue to treat source code as the primary maintained artifact, with specifications, tests, and proofs serving as secondary validation mechanisms. We argue for an alternative model, vericoding, in which specifications become the primary artifact and implementations become replaceable derivations. In this model, developers iteratively refine specifications, AI systems synthesize implementations and subsidiary specifications, and verification determines correctness. We present the architecture of this workflow, describe its realization in the Axiomander prototype, and evaluate its implications for composability, reuse, incremental verification, and human review effort. Our results suggest that AI-assisted software development may be more naturally understood as specification management than code authoring.

---

## 1. Introduction

AI has changed the economics of code generation.

Historically:

- Writing code was expensive.
- Verification was expensive.
- Humans were responsible for implementation.

Today:

- Writing code is comparatively cheap.
- Verification remains expensive.
- LLMs can generate implementations rapidly.

The bottleneck is no longer implementation effort.

The bottleneck is intent specification.

This paper explores the consequences of treating specifications as the primary maintained artifact.

---

## 2. The Traditional Model

Traditional software engineering is code-centric.

Human
↓
Code
↓
Tests
↓
Confidence

Properties:

- Code is the maintained artifact.
- Tests sample intended behaviour.
- Specifications are often informal.
- Trust is concentrated in code review.

This model evolved because humans were the code generators.

---

## 3. Vericoding

Vericoding inverts the traditional workflow.

Human
↓
Specification
↓
AI
↓
Implementation
↓
Verification

Core principles:

### Principle 1: Specification is the Control Surface

Developers steer the system by editing specifications.

### Principle 2: Code is a Derived Artifact

Implementations are disposable and replaceable.

### Principle 3: Correctness Requires Proof

Verification determines whether code satisfies intent.

### Principle 4: Failure Returns Structured Information

Verification failures produce residual obligations and counterexamples rather than vague criticism.

---

## 4. Specification Management

The central activity becomes specification management.

Developers spend their effort:

- refining contracts
- reviewing contracts
- decomposing specifications
- evolving requirements

rather than directly manipulating implementations.

This shifts engineering effort toward artifacts that are smaller, more declarative, and easier to review.

---

## 5. Compositional Scaling

Vericoding depends on compositional verification.

Contracts provide stable interfaces.

Proofs become reusable build artifacts.

Traditional build systems manage:

source -> object -> executable

Vericoding manages:

specification -> proof graph -> implementation

Verification becomes a build system for correctness.

---

## 6. The Heal Loop

Traditional AI coding often relies on repeated prompting.

Prompt
↓
Code
↓
"Try again"

Vericoding replaces this with structured repair.

Specification
↓
Code
↓
Verification
↓
Residual goal
↓
Repair

The verifier explains precisely why a proof failed.

The AI repairs against the failure rather than guessing again.

---

## 7. Evaluation Plan

### Case Study 1: Retrofitted Verification

Add contracts to an existing Python codebase.

Measure:

- contracts written
- proof obligations
- verification success

### Case Study 2: AI Synthesis from Specification

Generate implementations from specifications.

Measure:

- repair iterations
- proof success rates
- residual complexity

### Case Study 3: Maintenance Tasks

Change requirements and compare:

Traditional:
- edit code
- update tests

Vericoding:
- edit specification
- regenerate code
- reverify

Measure engineering effort and verification impact.

---

## 8. Human Factors

Questions of interest:

- What do engineers actually review?
- What artifacts remain stable?
- What artifacts churn?
- How much code must humans read?

Hypothesis:

Traditional development reviews large volumes of implementation.

Vericoding reviews comparatively small contract surfaces.

---

## 9. Limitations

Potential failure modes:

- incorrect specifications
- unsound assumptions
- unsupported language features
- proof-search failures
- verification scalability limits

Vericoding shifts effort.

It does not eliminate effort.

---

## 10. Conclusion

The central observation is economic rather than technical.

When implementation becomes inexpensive and verification remains expensive, specifications naturally become the primary maintained artifact.

Vericoding is a software engineering model built around this observation.

The long-term question is whether software development in the AI era is best understood as programming—or as specification management.
