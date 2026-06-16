# From Flat Stores to Separation Logic: Lessons Building a Python Verifier

**Experience report: migrating an LLM-assisted verifier to Iris**

Scidonia -- Axiomander

> Prose-only companion to `iris-workshop-paper.tex`. The LaTeX is authoritative;
> this file is kept for quick reading and diffing.

---

## Abstract

Axiomander is a verification pipeline for ordinary, decorator-free Python: a
human writes a strong specification, an LLM proposes the implementation and the
helper contracts needed to prove it, and the verifier returns a deterministic
verdict with a structured residual on failure. This experience report is about
the proof backend underneath that loop. We first built it the obvious way --
lowering Python to a small imperative language over a flat store -- and recovered
the locality that modular verification needs by *reconstructing the frame rule by
hand*: an explicit `clobber` operator and generated per-callee, per-variable
frame lemmas. It worked for tiny inputs and then stopped scaling:
weakest-precondition terms blew up, the compiled-Ltac automation grew brittle,
and whole classes of programs -- owned mutable fields, aliasing, anything heading
toward concurrency -- could not be expressed at all. We then rebuilt the backend
on Iris, where a callee's footprint is a separating resource and framing is the
separating conjunction. Our thesis, which the migration bore out, is that the
abstractions an LLM-driven verifier needs -- modular verification, proof reuse,
library stubbing, and incremental checking -- are all instances of one mechanism:
Iris framing behind opaque specification boundaries. We report what changed
quantitatively (framing obligations per call fell to zero; automatically
generated, machine-checked proofs replaced hand-decomposed ones) and
qualitatively (resource-bearing code became expressible at all), and distil the
lessons for others building automated, composition-heavy verifiers.

**Keywords:** separation logic, Iris, weakest preconditions, specification
composition, stubbing, frame rule, LLM-assisted proof, Python, experience report.

---

## 1. Motivation: vericoding needs composition

Axiomander's development model is a loop. The human writes a *strong
specification* -- a precondition/postcondition pair -- as the primary artifact.
An LLM proposes an implementation. The verifier reduces "does the code meet the
spec?" to a proof obligation and returns either a certificate or a *structured
residual* (the remaining goal with its hypotheses, plus a counterexample where one
exists). The LLM repairs against the residual, not the natural-language prompt,
and may introduce helper functions with their own contracts, checked the same
way. The LLM is the reason we need what follows, not the subject of this report:
the subject is the proof backend that makes the loop tractable.

For this loop to be usable on real codebases, three forms of composition must hold
simultaneously:

1. **Modular verification.** A caller must be provable from a callee's *contract*
   alone.
2. **Proof reuse under iteration.** Editing a body must not invalidate callers'
   proofs while the *contract* is unchanged: body changes invalidate local
   proofs; contract changes invalidate callers.
3. **Stubbing.** Unverified libraries must be replaceable by their declared
   behaviour; the trust boundary is the stub, written once.

All three are, at bottom, the **frame property**. The thesis of this report is
that these are not three problems but one, that an off-the-shelf separation logic
supplies it directly, and that the place we spent our effort -- and hit our limits
-- was reconstructing it over a flat store.

---

## 2. First architecture: framing by hand over a flat store

Our original backend lowers Python to a small imperative language IMP, with a
state that is a flat finite map from variable names to values (`VZ | VBool |
VUnit`, plus structural `VList | VTuple | VDict`, with mutation on a parallel heap
representation). The WP calculus is standard and proven sound in Rocq:

$$
\begin{aligned}
\mathrm{wp}(\mathsf{skip}, Q) &= Q,
&\mathrm{wp}(x := e, Q) &= Q[x \mapsto e], \\
\mathrm{wp}(c_1; c_2, Q) &= \mathrm{wp}(c_1, \mathrm{wp}(c_2, Q)),
&\mathrm{wp}(\mathsf{if}\ e\ c_1\ c_2, Q) &= (e \Rightarrow \mathrm{wp}(c_1,Q)) \wedge (\neg e \Rightarrow \mathrm{wp}(c_2,Q)).
\end{aligned}
$$

Calls are the interesting case. A call site `t := g(a)` is verified against `g`'s
contract using a `CCall` rule. To recover locality we model the callee's effect
with an explicit `clobber` operator that havocs the declared write set, and must
discharge, for *every* variable `v`:

$$
\forall v.\; v \notin (\textit{target} :: \textit{writes}) \Rightarrow
\mathrm{lget}\,s\,v = \mathrm{lget}\,(\mathrm{clobber}\,(\mathrm{lupd}\,s\,\textit{target}\,r)\,\textit{writes})\,v.
$$

This is the frame rule, encoded extensionally over a flat store. Three problems
follow. Two are about cost:

- **WP-term blowup.** Each successive call nests the full WP expansion inside the
  previous call's postcondition; the monolithic tactic stops closing it.
- **Brittle automation.** The single universally-quantified frame subgoal does not
  match cleanly in compiled Ltac (an `ls` coercion normalises away in the `.vo`).

The third is about **expressivity**, and is the one we underestimated: a flat
name-to-value store cannot model two references aliasing the same cell, cannot
transfer ownership of a mutable field across a call, and has no path to
concurrency. Whole *programs*, not just whole proofs, fall outside it.

Our mitigation for the cost problems was to generate, at the Python IR level, **one
frame lemma per (callee, preserved-variable) pair**:

```coq
(* g writes ["result"]; the caller's "a" is preserved across t := g(a) *)
Lemma g_frame_a : forall (s : state) (r : Z),
  ~ In "a" ("t" :: "result" :: nil) ->
  lget s "a" = lget (clobber (lupd s "t" (VZ r)) ("result" :: nil)) "a".
Proof. apply wp_ccall_frame. Qed.
```

The caller's proof replaces the monolithic `forall v` subgoal with a sequence of
`apply g_frame_a. apply g_frame_b. ...`. This restores tractability but is a
workaround: we are *reconstructing* the frame rule one variable at a time, and
reconstruction does nothing for the expressivity gap. The lesson: **if framing is
load-bearing, the assertion logic should be substructural.**

---

## 3. Migration to Iris

We rebuilt the backend on Iris. **Snakelet** is the intermediate language into
which Axiomander lowers Python; **SnakeletWp** is its weakest-precondition
calculus, defined inside the Iris program logic. The state is an Iris heap: a
mutable Python object field is a points-to assertion `l |-> v`, ownership is a
separating resource rather than an entry in a flat map, assertions are `iProp`.
Snakelet targets Python *in the large* -- ordinary control flow, exceptions,
calls, and the built-in containers lower directly, and only genuinely pathological
constructs (runtime metaprogramming, reflection) are gated. Its full term
language, semantics, and WP rules are in Appendix A; this section is about what the
move bought us.

### 3.1 Contracts compile to `iProp`, composed with the separating conjunction

Contracts remain ordinary Python -- plain `assert` statements or a verifier-only
`axiomander:` docstring. A shared `ContractLinter` parses them into a contract IR;
`contract_ir_iris` compiles that to `iProp`. Pure facts become the persistent
embedding `<P>`; resource facts become points-to assertions.

| Python contract fragment | `iProp` |
|---|---|
| `assert x >= 1` | `<x >= 1>` |
| `assert implies(A, B)` | `<A -> B>` |
| `assert all(x != i for i in range(0,10))` | `<forall i, 0 <= i < 10 -> x != i>` |
| `owns(box)` | `box.value |-> v` (a resource) |

The decisive choice is that **the default composition of clauses is the separating
conjunction `*`, not `/\`.** For the pure-integer fragment this costs nothing
(`<P> * <Q>` is `<P /\ Q>`), but the same rule already accounts for disjoint
resources. The `bump` example (owns + modifies) compiles to

```
{ box.value |-> n * <n >= 0> }  bump(box)  { r. box.value |-> n+1 * <r = n+1> }
```

with the user writing no `*`, `|->`, or tactics. This contract has *no flat-store
rendering*: `owns` denotes ownership of a mutable cell, which the name-to-value
store of Section 2 cannot express. Resource awareness is the first thing the
migration adds, before any question of proof size.

### 3.2 The frame rule is free, and so is composition

Because assertions are `iProp`, the structural frame rule holds without a side
condition: any `R` over a disjoint heap region is carried across `c` by `*`,
automatically. The entire `clobber`/`forall v not in writes` apparatus and the
per-callee per-variable frame-lemma generator simply disappear.

### 3.3 Opaque calls: one boundary, three jobs

Calls dispatch through a **contract table** (an Iris `FunCtx`). A *transparent*
call unfolds a first-party body; an *opaque* call consumes the callee's
precondition, receives its postcondition, and frames the rest:

$$
\frac{P_g * R \qquad \forall r.\ (Q_g * R) \vdash \mathrm{wp}\ K\ \{\Phi\}}
{\mathrm{wp}\ (\mathsf{call}\ g;\ K)\ \{\Phi\}}
$$

The single most useful thing we learned is that this one rule does three jobs at
once: **stubbing** (a library contract enters the `FunCtx`, body never required),
**modular verification** (a first-party callee re-declared opaque once its contract
is stable), and the **incremental-reuse boundary** (callers depend only on the
contract; the `FunCtx` entry's hash is the cache key). Three readings of one rule.

### 3.4 Separation logic as an implementation detail

The migration is confined to the proof backend. The `ContractLinter`, the SMT
export, the LLM oracle, and the incremental cache are backend-agnostic; the
contract IR diverges only at the final rendering step (`to_coq` vs.
`contract_ir_iris.iris_prop`). From the user's side nothing changes -- contracts
are decorator-free Python and `owns(...)` is the only new, optional vocabulary.
Iris is the substrate, not the interface.

### 3.5 Staged, syntax-directed proofs

SnakeletWp ships stage tactics -- `pure_step`, `case_bool`, `call_opaque`,
`call_transparent`, `finish_pure`, `call_opaque_pre` -- and the generator
(`iris_proof_gen`) emits one stage per IR node. A three-call chain becomes a flat,
machine-checked sequence such as `[call_opaque, pure_step, call_transparent,
pure_step, pure_step, call_opaque, finish_pure]`. Stages **fail independently**:
an undischarged precondition goes to SMT (UNSAT returns as `Axiom smt_ax_N`); a
pure postcondition `finish_pure` cannot close is an SMT candidate; beyond SMT the
named stage plus its goal state is what the LLM oracle receives. A failed attempt
yields a reusable artifact, not a dead end.

---

## 4. Evaluation

We compare the two backends on small functions from the repository. Two effects
matter, the second more than the first: how much framing the proof must do by
hand, and what can be expressed at all.

**Framing cost.** For the two-call `frame_two_calls` (two increments and a sum),
flat-store needs two explicit `wp_ccall_frame` applications and fourteen
preservation conjuncts threaded through intermediate postconditions (`Q1`: 6,
`Q2`: 8), hand-written because the monolithic tactic does not close it. In Iris
the frame rule carries untouched resources implicitly, so the count is *zero*,
independent of live variables or call count.

| function (calls) | flat-store framing | flat-store proof | Iris framing | Iris proof |
|---|---|---|---|---|
| 2-call chain | 2+14 | 29 | 0 | 11 |
| 3-call chain | --- | --- | 0 | 14 |
| owned-field `bump` | n/a | n/a | 0 | 15 |
| mutate-then-raise | n/a | n/a | 0 | 9 |

*framing* = explicit per-call frame steps + preservation conjuncts (`2+14` = 2
frame applications + 14 conjuncts); *proof* = non-blank `Proof`--`Qed` lines.
Flat-store proofs are hand-decomposed (the monolithic tactic does not scale past
one call); Iris proofs are generated and `coqc`-checked. `n/a` = not expressible
over a flat store; `---` = no scalable proof. The trend is the point: flat-store
framing grows with (calls x live variables), the Iris column is a flat zero, and
the 3-call Iris proof (14 lines) is *shorter* than the 2-call flat-store proof
(29 lines) despite doing more.

**Expressivity, not just efficiency.** The bottom two rows are the more important
result. `bump` mutates an owned field; `mutate-then-raise` mutates a cell then
raises, with the exceptional postcondition describing the heap as it stood at the
raise. Neither has a flat-store analogue -- the name-to-value store cannot express
ownership of a mutable cell, let alone ownership surviving an exception. The
migration did not merely make these proofs shorter; it made the corresponding
*programs verifiable for the first time*. The same extends to aliasing and to the
concurrency primitives the calculus already carries.

---

## 5. Discussion and related work

Axiomander's separation-logic interpretation of object fields and its opaque call
rule are textbook Iris; the novelty is in the *system context*, and the
contribution of this report is the experience of the migration rather than a new
metatheory. The combination is unusual: the assertion logic is never exposed to
the user, the obligations are generated and largely discharged by an LLM on
structured residual goals with Iris/Rocq as the trust kernel, and one opaque-call
rule serves as modular verification, incremental-reuse boundary, and library stub
at once. We offer Axiomander as a data point that Iris's framing and ownership
story is the right substrate for *automated*, composition-heavy verification.

---

## 6. Lessons learned

1. **Framing is the fundamental abstraction.** Every composition property reduced
   to it; building it by hand caused the WP blowup and the brittle automation.
2. **One boundary does many jobs.** Opaque specifications unify modular
   verification, proof reuse, and stubbing -- and the cache keys on the same
   contract hash.
3. **Incrementality follows contract boundaries.** "What must I re-prove?" has a
   syntactic answer once callers depend only on contracts.
4. **Ownership is an expressivity question, not only efficiency.** Real Python
   mutates shared objects and raises through them; a flat store cannot express
   that, so the substructural logic is what makes such code verifiable at all.
5. **Separation logic is easier to adopt than to reconstruct.** We spent more
   engineering faking the frame rule than inheriting it from Iris.

**Status.** Snakelet and SnakeletWp are complete and free of `Admitted` across the
rule set of Appendix A, including the exception-aware extension and its loop
rules; the staged generator, the end-to-end Python-to-Iris pipeline, the
contract-to-`iProp` compiler, and the SMT-axiom slot are in place, with tens of
Iris-specific tests passing alongside the mature flat-store backend. Remaining
work wires the exception calculus into the Python lowering and extends the
fragment to loop invariants over shared disjoint memory, in-place data-structure
mutation, and type-aware reasoning over strings/floats/`isinstance`/`None`.

**Open questions.** How far an object's footprint can be *inferred* from
`modifies` for an LLM-generated body before the user must annotate `owns(...)`;
and which Iris proof-mode presentation of a failed stage's residual makes the best
LLM prompt.

---

## Artifact pointers

Material developed in the Axiomander repository: the Iris migration plan and
current state; the Iris backend prototype (`bump`/`owns`, resource
classification); per-callee frame lemmas in the flat-store backend (Section 2);
the staged proof engineering notes; the incremental-verification cache design; and
the companion whitepaper and slides.

---

## Appendix A: The Snakelet calculus

Snakelet is an expression language in administrative-normal form: every operator
and call takes values or variables, evaluation order is made explicit by
`let`-binding and a per-item evaluation-context grammar. A store is a finite map
from locations to values; a mutable object field is a heap cell `l |-> v`. The
immutable containers (list, tuple, dict, set) are *structural* values, mirroring
Dafny's `seq` and F*'s `list`.

Two coordinated developments share this design. The core language carries float
literals, dictionary get/set, and the concurrency primitives `FAA`/`fork`; the
exception-aware extension shown here adds first-class exceptions and carries the
complete, machine-checked rule set. Following van Collem/de Vilhena/Krebbers (PLDI
2026), `raise v` on a value is a **stuck terminal** expression -- not itself a
value -- so an uncaught raise is the program's exceptional result. A program
terminates as `r ::= val v | exn s v`, and the WP postcondition ranges over `r`.

```text
v   ::= n | b | fl | s | l | () | exn s v               (int, bool, float, string, loc, unit, exception)
      | [v..] | (v..) | {v:v..} | {v..}                 (list, tuple, dict, set; immutable, structural)
op  ::= + | - | * | / | % | = | != | < | <= | > | >= | and | or | in | len | union | inter
e   ::= v | x | let x = e in e | op(e,e) | g(e..)
      | !e | e := e | ref e | if e then e else e
      | raise e | try e catch x => e
      | while e e | for x in e do e
K   ::= let x = [] in e | op([],v) | op(e,[]) | ![] | ref [] | [] := v | e := []
      | if [] then e else e | raise [] | try [] catch x => e | for x in [] do e
r   ::= val v | exn s v
```

Every context `K` is *neutral* except `try [] catch x => e`; `op(e,e)` evaluates
its right operand first.

**Operational semantics.** Reduction is small-step, factoring into *pure* steps
`e ~> e'` (no heap, deterministic) and *head* steps `(e,s) -> (e',s')` (heap and
calls), lifted under a context by `Ctx-P`/`Ctx-H`. The unwinding rule fires only
for neutral `K`, so a raise propagates through `let`, operators, and loads but is
caught by an enclosing `try`. Calls dispatch through `entries`: `FunSpec P Q`
(opaque, stuck unless `P`) or `FunDef x b` (transparent, substitute into body).

$$
\begin{aligned}
&\textbf{Pure}\ e \leadsto e':\\
&\quad \mathsf{let}\ x{=}v\ \mathsf{in}\ e \leadsto e[x{:=}v]\qquad op(v_1,v_2)\leadsto \mathrm{binop}(op,v_1,v_2)\\
&\quad \mathsf{if\ true\ then}\ e_1\ \mathsf{else}\ e_2\leadsto e_1\qquad \mathsf{if\ false\ then}\ e_1\ \mathsf{else}\ e_2\leadsto e_2\\
&\quad \mathsf{try}\ v\ \mathsf{catch}\ x{\Rightarrow}h\leadsto v\qquad \mathsf{try}\ (\mathsf{raise}\ v)\ \mathsf{catch}\ x{\Rightarrow}h\leadsto h[x{:=}v]\\
&\quad \mathrm{neutral}(K)\Rightarrow K[\mathsf{raise}\ v]\leadsto \mathsf{raise}\ v\\
&\quad \mathsf{while}\ e_1\ e_2\leadsto \mathsf{if}\ e_1\ \mathsf{then}\ (e_2;\mathsf{while}\ e_1\ e_2)\ \mathsf{else}\ ()\\
&\quad \mathsf{for}\ x\ \mathsf{in}\ []\ \mathsf{do}\ b\leadsto ()\qquad \mathsf{for}\ x\ \mathsf{in}\ (v{::}vs)\ \mathsf{do}\ b\leadsto b[x{:=}v];\mathsf{for}\ x\ \mathsf{in}\ vs\ \mathsf{do}\ b\\
&\textbf{Head}\ (e,\sigma)\to(e',\sigma'):\\
&\quad \sigma(l){=}v\Rightarrow (!l,\sigma)\to(v,\sigma)\qquad l\in\mathrm{dom}\,\sigma\Rightarrow (l{:=}v,\sigma)\to((),\sigma[l{\mapsto}v])\\
&\quad \sigma(l){=}\bot\Rightarrow (\mathsf{ref}\ v,\sigma)\to(l,\sigma[l{\mapsto}v])\\
&\quad \mathrm{entries}(g){=}\mathsf{FunSpec}\,P\,Q,\ P\,\vec v,\ Q\,\vec v\,v\Rightarrow (g(\vec v),\sigma)\to(v,\sigma)\\
&\quad \mathrm{entries}(g){=}\mathsf{FunDef}\,\vec x\,b,\ |\vec v|{=}|\vec x|\Rightarrow (g(\vec v),\sigma)\to(b[\vec x{:=}\vec v],\sigma)\\
&\textbf{Decompose:}\ e\leadsto e'\Rightarrow (K[e],\sigma)\to(K[e'],\sigma);\ \text{head steps lift likewise.}
\end{aligned}
$$

**Weakest preconditions.** The postcondition is `Phi : Result -> iProp`. It is the
guarded fixpoint of: if `e` is terminal then `Phi r` holds under a fancy update;
otherwise `e` is reducible and one step re-establishes the state interpretation
(the Iris `gen_heap` view) and the WP of the reduct. Composition goes through
`bindp`: `bindp K Phi (val v) = WPE K[v] {{Phi}}` and `bindp K Phi (exn s v) = Phi
(exn s v)`. The heap rules' exceptional arm describes the heap as it stood at the
raise. All rules below are machine-checked.

$$
\begin{aligned}
&\Phi(\mathsf{val}\,v)\vdash \mathrm{WPE}\ v\ \{\!\{\Phi\}\!\}\qquad \Phi(\mathsf{exn}\,s\,v)\vdash \mathrm{WPE}\ (\mathsf{raise}\,(\mathsf{exn}\,s\,v))\ \{\!\{\Phi\}\!\}\\
&\mathrm{WPE}\ e\ \{\!\{\Phi\}\!\}\ast(\forall r.\,\Phi\,r\,{-\!\ast}\,\Psi\,r)\vdash \mathrm{WPE}\ e\ \{\!\{\Psi\}\!\}\\
&\triangleright\,\mathrm{WPE}\ e[x{:=}v]\ \{\!\{\Phi\}\!\}\vdash \mathrm{WPE}\ (\mathsf{let}\ x{=}v\ \mathsf{in}\ e)\ \{\!\{\Phi\}\!\}\\
&\Phi(\mathsf{exn}\,s\,v)\vdash \mathrm{WPE}\ (\mathsf{let}\ x{=}\mathsf{raise}\,(\mathsf{exn}\,s\,v)\ \mathsf{in}\ e)\ \{\!\{\Phi\}\!\}\\
&\triangleright\,\mathrm{WPE}\ \mathrm{binop}(op,v_1,v_2)\ \{\!\{\Phi\}\!\}\vdash \mathrm{WPE}\ op(v_1,v_2)\ \{\!\{\Phi\}\!\}\\
&\triangleright\,\mathrm{WPE}\ e_1\ \{\!\{\Phi\}\!\}\vdash \mathrm{WPE}\ (\mathsf{if\ true\ then}\ e_1\ \mathsf{else}\ e_2)\ \{\!\{\Phi\}\!\}\quad(\text{dually, false}\to e_2)\\
&\triangleright\,\mathrm{WPE}\ v\ \{\!\{\Phi\}\!\}\vdash \mathrm{WPE}\ (\mathsf{try}\ v\ \mathsf{catch}\ x{\Rightarrow}h)\ \{\!\{\Phi\}\!\}\\
&\triangleright\,\mathrm{WPE}\ h[x{:=}v]\ \{\!\{\Phi\}\!\}\vdash \mathrm{WPE}\ (\mathsf{try}\,(\mathsf{raise}\ v)\,\mathsf{catch}\ x{\Rightarrow}h)\ \{\!\{\Phi\}\!\}\\
&\mathrm{neutral}(K):\ \mathrm{WPE}\ e\ \{\!\{\mathrm{bindp}\,K\,\Phi\}\!\}\vdash \mathrm{WPE}\ K[e]\ \{\!\{\Phi\}\!\}\\
&l\mapsto v\ast\triangleright(l\mapsto v\,{-\!\ast}\,\Phi(\mathsf{val}\,v))\vdash \mathrm{WPE}\ {!}l\ \{\!\{\Phi\}\!\}\\
&l\mapsto w\ast\triangleright(l\mapsto v\,{-\!\ast}\,\Phi(\mathsf{val}\,()))\vdash \mathrm{WPE}\ (l{:=}v)\ \{\!\{\Phi\}\!\}\\
&\triangleright(\forall l.\,l\mapsto v\,{-\!\ast}\,\Phi(\mathsf{val}\,l))\vdash \mathrm{WPE}\ (\mathsf{ref}\ v)\ \{\!\{\Phi\}\!\}\\
&\triangleright\,\Phi(\mathsf{val}\,())\vdash \mathrm{WPE}\ (\mathsf{for}\ x\ \mathsf{in}\ []\ \mathsf{do}\ b)\ \{\!\{\Phi\}\!\}\\
&\mathrm{entries}(g){=}\mathsf{FunSpec}\,P\,Q,\,P\,\vec v:\ \triangleright(\forall v.\,\ulcorner Q\,\vec v\,v\urcorner\,{-\!\ast}\,\Phi(\mathsf{val}\,v))\vdash \mathrm{WPE}\ g(\vec v)\ \{\!\{\Phi\}\!\}\\
&\mathrm{entries}(g){=}\mathsf{FunDef}\,\vec x\,b,\,|\vec v|{=}|\vec x|:\ \triangleright\,\mathrm{WPE}\ b[\vec x{:=}\vec v]\ \{\!\{\Phi\}\!\}\vdash \mathrm{WPE}\ g(\vec v)\ \{\!\{\Phi\}\!\}\\
&\textbf{While/ForCons:}\ \triangleright\,\mathrm{WPE}\ (\text{one-step unfolding})\ \{\!\{\Phi\}\!\}\vdash \mathrm{WPE}\ (\text{loop})\ \{\!\{\Phi\}\!\}
\end{aligned}
$$

On top of `ForCons` a structural fold rule carries a user invariant `P` over the
remaining list suffix and re-establishes it (or escapes through the exceptional
arm) at each element. Each rule has a matching stage tactic (Section 3.5):
`pure_step` fires Let/Op/IfT/IfF/TryV/TryC, `heap_load`/`store`/`alloc` the heap
rules, `call_opaque`/`call_transparent` the call rules, `raise_step`
Raise/Unwind, and `loop_unfold` the loop rules.
