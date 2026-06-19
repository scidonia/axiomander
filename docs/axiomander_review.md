# Review of Axiomander Slides

*Perspective: sceptical but fair reviewer with a CS background in
weakest preconditions and separation logic*

## Executive Summary

The central thesis is strong and technically plausible: LLMs are
optimistic generators, specifications should become the primary
engineering artifact, and formal verification can provide a
deterministic signal for whether generated code satisfies a
specification.

The presentation is at its strongest when discussing:

-   "Tests sample, proofs quantify."
-   Specification as the control surface.
-   The heal-loop driven by residual proof obligations.
-   Compositional reasoning via contracts and frame rules.

However, the deck currently overclaims relative to what it demonstrates.
Most of the concerns below are not fundamental flaws in the approach;
rather, they are places where a technically sophisticated audience will
push for more precision, clearer boundaries, and stronger evidence.

------------------------------------------------------------------------

## Major Strengths

### 1. Correct diagnosis of the LLM problem

The framing that LLMs optimize for apparent intent satisfaction rather
than correctness is compelling and broadly accurate.

The distinction between:

-   code that looks right,
-   code that passes a few tests,
-   code that satisfies a formally stated property,

is clearly communicated.

This is one of the strongest parts of the deck.

### 2. Good specification-centric framing

The slogan:

> Specification is the control surface. Code is a derived artifact.

is memorable and captures a genuine shift in workflow.

The idea that humans should maintain specifications while
implementations are regenerated underneath them is an interesting and
potentially powerful perspective.

### 3. Strong use of weakest preconditions

The WP story is familiar and credible to a formal methods audience.

The progression:

-   contracts
-   lowering
-   verification conditions
-   weakest preconditions
-   proof obligations

is coherent and technically grounded.

### 4. Emphasis on compositionality

The discussion of:

-   contracts,
-   frame conditions,
-   stubbing,
-   incremental verification,

shows awareness of what actually matters in scalable verification
systems.

Many presentations focus entirely on proving individual functions and
ignore engineering scalability. This deck does not make that mistake.

------------------------------------------------------------------------

## Major Concerns

### 1. "Strong specifications are a total statement of intent"

This is the biggest conceptual overstatement.

The deck contrasts:

-   tests as samples of intent
-   specifications as total statements of intent

A sceptical reviewer will immediately object.

Specifications are not intent itself.

Specifications can:

-   omit requirements,
-   encode incorrect assumptions,
-   accidentally overconstrain behaviour,
-   accidentally underconstrain behaviour,
-   become inconsistent with user expectations.

Proof only establishes:

> correctness with respect to the specification.

not:

> correctness with respect to human intent.

### Recommendation

Replace language like:

> A strong specification is a total statement of intent.

with:

> A strong specification makes intent explicit and mechanically
> checkable.

or

> Proof establishes correctness relative to a specification.

This is more precise and harder to attack.

------------------------------------------------------------------------

### 2. The Python story is underspecified

The deck repeatedly references "real Python", mutation, and aliasing.

However, later slides reveal that:

-   Python is lowered into an IMP-like intermediate language.
-   Only a verified subset is modeled.

This raises immediate questions:

-   Which Python features are supported?
-   Exceptions?
-   Objects?
-   Inheritance?
-   Dynamic dispatch?
-   Reflection?
-   Closures?
-   Generators?
-   Coroutines?
-   Metaclasses?
-   Imports?

A reviewer will want to know where the boundary lies.

### Recommendation

Add a dedicated slide:

## Supported Python Fragment

and explicitly state:

-   supported features,
-   unsupported features,
-   planned extensions.

This dramatically increases credibility.

------------------------------------------------------------------------

### 3. Generated sub-specifications are a potential loophole

The deck says the LLM may introduce helper functions and helper
contracts.

This is sensible.

However, reviewers will immediately ask:

> What prevents the LLM from introducing vacuous or unhelpful contracts?

For example:

-   contracts that merely restate implementation details,
-   contracts that expose internal structure,
-   contracts that weaken abstraction boundaries.

Verification ensures consistency.

Verification does not ensure usefulness.

### Recommendation

Explicitly discuss criteria for acceptable generated contracts:

-   abstraction quality,
-   usefulness to callers,
-   minimality,
-   information hiding.

Otherwise this looks like a place where complexity can be hidden.

------------------------------------------------------------------------

### 4. Stubs as axioms deserve a stronger warning

The treatment of stubbing is mostly correct.

However the deck currently understates the trust implications.

A single unsound stub can invalidate arbitrary downstream proofs.

A reviewer from the verification community will immediately ask:

> What exactly is inside the trusted computing base?

### Recommendation

Add explicit language:

> Verification is only as trustworthy as the trusted axioms and stubs.

and perhaps include:

-   trusted kernel,
-   trusted translation,
-   trusted stubs,
-   generated artifacts.

as a trust stack.

------------------------------------------------------------------------

### 5. Counterexamples are oversold

The deck implies that failures produce concrete counterexamples.

This is true for many SMT-dischargeable obligations.

It is not generally true for arbitrary higher-order proof failures.

In Rocq/Iris many failures simply leave an unprovable goal.

### Recommendation

Clarify:

> Decidable fragments may produce concrete counterexamples.
>
> More general proof obligations produce residual goals and hypotheses.

This is both accurate and still compelling.

------------------------------------------------------------------------

### 6. Soundness claims need tighter wording

The WP equivalence shown in the deck is standard.

However, the presentation sometimes sounds like it proves correctness of
Python itself.

In reality the claim is closer to:

> The translated program is sound with respect to the modeled semantics.

The trust argument depends on:

1.  correctness of the lowering,
2.  correctness of the IMP semantics,
3.  correctness of the WP calculus,
4.  correctness of Rocq,
5.  correctness of trusted axioms.

### Recommendation

Add a slide explicitly discussing:

## Trust Base

This is standard practice in verification systems and will pre-empt
reviewer criticism.

------------------------------------------------------------------------

## Evidence Gap

The deck needs more empirical evidence.

Several statements currently read like marketing claims:

-   "\~80% of goals"
-   "16+ self-verified functions"
-   cache performance claims
-   verification speed claims

Without context, reviewers cannot evaluate them.

### Recommendation

Provide:

-   benchmark suite,
-   number of functions,
-   obligation counts,
-   discharge rates,
-   verification times,
-   cache hit rates,
-   examples that fail.

Even a small table would substantially improve credibility.

------------------------------------------------------------------------

## Missing Slide: Threats to Validity

A particularly effective addition would be a slide titled:

## Threats to Validity

Including:

-   specification bugs,
-   unsound stubs,
-   unsupported Python features,
-   translation bugs,
-   proof engineering costs.

This paradoxically increases confidence because it demonstrates
awareness of the limitations.

------------------------------------------------------------------------

## Missing Slide: End-to-End Example

The deck describes the heal-loop conceptually but never fully
demonstrates it.

A reviewer would benefit from seeing:

1.  Human writes specification.
2.  LLM generates incorrect code.
3.  Verifier produces residual goal.
4.  Counterexample appears.
5.  LLM repairs code.
6.  Proof succeeds.

One complete example is worth several conceptual slides.

------------------------------------------------------------------------

## Overall Assessment

The underlying idea is promising and technically respectable.

The strongest contribution is not the use of Rocq, Iris, or weakest
preconditions individually. Rather, it is the proposed development
methodology:

-   human maintains specifications,
-   machine generates implementations,
-   verifier provides deterministic feedback,
-   repair operates on proof residuals instead of natural-language
    critique.

That is a compelling vision.

The primary weakness of the current presentation is not technical
unsoundness but rhetorical overreach. The deck occasionally slides from:

> verified against a specification

to

> verified intent

and from

> supported Python fragment

to

> real Python.

A formal methods audience will notice these jumps immediately.

If the claims are tightened, the trust assumptions made explicit, and a
small amount of empirical evidence added, the presentation becomes
substantially stronger and more defensible.
