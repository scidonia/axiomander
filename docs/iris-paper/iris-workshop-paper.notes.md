# Specification Composition for LLM-Driven Python Verification: Why We Build on Iris

**A short workshop paper for the Iris community**

Scidonia -- Axiomander

---

## Abstract

Axiomander is a verification pipeline that turns ordinary, decorator-free Python
into machine-checked proof obligations and discharges them through a ladder of
mechanical tactics, SMT, and an LLM proof oracle. Its purpose is *vericoding*: a
human iterates on a strong specification, an LLM derives the implementation (and
the helper specifications needed to prove it), and the verifier delivers a
deterministic verdict with a structured residual on failure. The viability of
this loop rests entirely on **specification composition** -- the ability to
verify a caller against a callee's *contract* rather than its body, to reuse
proofs across edits, and to stub unverified libraries by their declared
behaviour.

This paper argues that **separation logic, as realised by Iris, is the right
foundation for that composition**, and reports our experience replacing an
ad-hoc framing mechanism with a native Iris one. Our first backend lowered
Python to a small imperative language (IMP) over a flat store and recovered
locality through generated per-callee, per-variable *frame lemmas* over an
explicit `clobber` operator. That mechanism works but scales badly: it produces
WP-term blowup and brittle compiled-Ltac pattern matching, and it does not
extend to aliasing, ownership transfer, or concurrency. We describe a second
backend, **SnakeletLang/SnakeletWp**, an Iris language and weakest-precondition
calculus (currently 0 `Admitted`) in which a callee's footprint is a separating
resource, framing is the separating conjunction, and a *contract table* lets
calls be treated opaquely (as stubs) or transparently (unfolded). We give
Snakelet's full term language and weakest-precondition rule set, the
contract-to-`iProp` compilation, the opaque-call rule that underpins stubbing,
and a staged, syntax-directed proof generator whose stages fail independently
and feed residual goals to SMT and an LLM. We close with the open questions we
would most like the Iris community's input on.

**Keywords:** separation logic, Iris, weakest preconditions, specification
composition, stubbing, frame rule, LLM-assisted proof, Python.

---

## 1. The setting: vericoding needs composition

Axiomander's development model is a loop. The human writes a *strong
specification* -- a precondition/postcondition pair -- as the primary artifact.
An LLM proposes an implementation. The verifier reduces "does the code meet the
spec?" to a proof obligation and returns either a certificate or a *structured
residual* (the remaining goal with its hypotheses, plus a counterexample where
one exists). The LLM repairs against the residual, not against the original
natural-language prompt. Crucially, the LLM has freedom in *sub-specification*:
to prove an entry point it may introduce helper functions, each with its own
contract, which are checked the same way.

For this loop to be usable on real codebases, three forms of composition must
hold simultaneously:

1. **Modular verification.** A caller must be provable from a callee's
   *contract* alone. If proving `f` required unfolding the bodies of everything
   `f` transitively calls, neither proofs nor LLM prompts would scale.

2. **Proof reuse under iteration.** Editing a function body must not invalidate
   its callers' proofs as long as the function's *contract* is unchanged. The
   verifier should behave like an incremental build system: *body changes
   invalidate local proofs; contract changes invalidate callers.*

3. **Stubbing.** Libraries we cannot or will not verify must be replaceable by
   their declared behaviour. A caller proves against the stub's contract, which
   becomes an assumption; the trust boundary is the stub, written and reviewed
   once.

All three are, at bottom, the **frame property**: reasoning about one component
must be insensitive to the parts of the state it does not touch. This is exactly
what separation logic makes primitive, and it is why -- after building framing
the hard way once -- we are migrating Axiomander's proof backend to Iris.

---

## 2. First backend: framing by hand over a flat store

Our original backend lowers a verified subset of Python to a small imperative
language IMP, with a state that is a flat finite map from variable names to
values (`VZ | VBool | VUnit`, plus structural `VList | VTuple | VDict`, with
mutation modelled on a parallel heap representation). The WP calculus is
standard and proven sound in Rocq:

$$
\begin{aligned}
\mathrm{wp}(\mathsf{skip}, Q) &= Q,
&\mathrm{wp}(x := e, Q) &= Q[x \mapsto e], \\
\mathrm{wp}(c_1; c_2, Q) &= \mathrm{wp}(c_1, \mathrm{wp}(c_2, Q)),
&\mathrm{wp}(\mathsf{if}\ e\ c_1\ c_2, Q) &= (e \Rightarrow \mathrm{wp}(c_1,Q)) \wedge (\neg e \Rightarrow \mathrm{wp}(c_2,Q)).
\end{aligned}
$$

Calls are the interesting case. A call site `t := g(a)` is verified against
`g`'s contract using a `CCall` rule. To recover locality -- to let a caller
conclude that variables it cares about survive the call -- we model the callee's
effect with an explicit `clobber` operator that havocs the callee's declared
write set, and we must discharge, for *every* variable `v`, an obligation of the
form

$$
\forall v.\; v \notin (\textit{target} :: \textit{writes}) \;\Rightarrow\;
\mathrm{lget}\,s\,v = \mathrm{lget}\,(\mathrm{clobber}\,(\mathrm{lupd}\,s\,\textit{target}\,r)\,\textit{writes})\,v.
$$

This is the frame rule, but encoded extensionally over a flat store. Two
problems follow, both of which we hit in practice:

- **WP-term blowup.** Each successive call nests the full WP expansion inside the
  previous call's postcondition. A function with a handful of sequential calls
  produces terms too large for the kernel to handle comfortably.

- **Brittle automation.** The single universally-quantified frame subgoal does
  not match cleanly in compiled Ltac, partly because coercions (e.g. an `ls`
  wrapper) normalise away in the `.vo` and defeat the source-level pattern.

Our mitigation was to generate, at the Python IR level, **one frame lemma per
(callee, preserved-variable) pair**:

```coq
(* g writes ["result"]; the caller's "a" is preserved across t := g(a) *)
Lemma g_frame_a : forall (s : state) (r : Z),
  ~ In "a" ("t" :: "result" :: nil) ->
  lget s "a" = lget (clobber (lupd s "t" (VZ r)) ("result" :: nil)) "a".
Proof. apply wp_ccall_frame. Qed.
```

The caller's proof then replaces the monolithic `forall v` subgoal with a
sequence of `apply g_frame_a. apply g_frame_b. ...`, each trivial and each
failing independently with its own residual. This restores tractability and
keeps the per-obligation, fail-locally discipline we want. But it is, frankly, a
workaround: we are *reconstructing* the frame rule, one variable at a time, in a
logic that does not have it. It does not model aliasing, it does not express
ownership transfer, and it has no path to concurrency. The lesson is the
familiar one: **if framing is load-bearing, the assertion logic should be
substructural.**

---

## 3. Second backend: SnakeletLang and SnakeletWp over Iris

We have built a second backend in which framing is not reconstructed but
inherited. **Snakelet** is a small Iris *intermediate language* for the verified
Python subset, and **SnakeletWp** is its weakest-precondition calculus, defined
inside the Iris program logic. The state is an Iris heap; a mutable Python object
field is a points-to assertion `l \mapsto v`, and ownership is a separating
resource rather than an entry in a flat map; assertions are `iProp`. The next
three subsections give Snakelet's term language, its operational semantics, and
its weakest-precondition rules; the calculus currently carries **0 `Admitted`**
across the entire rule set -- values, binary operators, let, if,
load/store/alloc, the two call forms, and the exception and loop rules whose
postcondition ranges over a `Result`.

### 3.1 Snakelet: an intermediate language for the verified subset

Axiomander does not reason about arbitrary Python. The front end lowers a
*verified subset* -- straight-line assignment, conditionals, `while`/`for` loops,
`try`/`except`, and calls -- to Snakelet, and every proof obligation is discharged
at the Snakelet level. The Python-to-Snakelet lowering is the trusted boundary of
the pipeline (intended to be extracted from Coq later); Snakelet itself is small
enough to carry a complete operational semantics and WP calculus.

Snakelet is an expression language in administrative-normal form: every operator
and call takes values or variables, and evaluation order is made explicit by
`let`-binding and a per-item evaluation-context grammar. A store is a finite map
from locations to values; a mutable Python object field is a heap cell, exposed
in the logic as `l \mapsto v`. The immutable Python containers (list, tuple, dict,
set) are *structural* values, not heap objects, mirroring Dafny's `seq` and
F*'s `list`.

The core development carries float literals, dictionary get/set, and the
concurrency primitives `FAA`/`fork`; the exception-aware extension presented here
adds first-class exceptions and carries the complete, machine-checked rule set. We
present the latter because exceptions change the *shape of the judgement*:
following van Collem/de Vilhena/Krebbers (PLDI 2026), `raise v` on a value is a
**stuck terminal** expression -- not itself a value -- so an uncaught raise sits
in evaluation position as the program's exceptional result. A program terminates
in one of two ways, captured by the result type `r ::= val v | exn s v`, and the
WP postcondition ranges over `r` rather than over values. The term language:

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

### 3.2 Operational semantics

Reduction is small-step and factors into *pure* steps `e ~> e'` (no heap,
deterministic) and *head* steps `(e,s) -> (e',s')` (heap and calls), each lifted
under an evaluation context by the two decomposition rules. The unwinding rule
fires only for neutral `K`, so a raise propagates through `let`, operators, loads,
and the rest, but is *caught* by an enclosing `try` frame -- exactly Python/ML
exception propagation. Calls dispatch through a *contract table* `entries`: a name
maps to either `FunSpec P Q` (opaque -- the call steps to some result satisfying
`Q` only when `P` holds, so calling outside the precondition is stuck) or
`FunDef x b` (transparent -- substitute arguments into the body); the two modes
share one table with one entry per name.

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

### 3.3 The weakest-precondition rules

SnakeletWp is a hand-rolled weakest precondition whose postcondition is
`Phi : Result -> iProp`. It is the guarded fixpoint of: if `e` is terminal then
`Phi r` holds under a fancy update; otherwise `e` is reducible and, after one
step, the state interpretation (the Iris `gen_heap` authoritative view) and the WP
of the reduct are re-established. Ranging `Phi` over `Result` is the one
structural change exceptions force; everything else is standard Iris. All rules
below are proved with **0 `Admitted`**.

Composition goes through `bindp`, the `Result`-typed continuation of the bind
rule: `bindp K Phi (val v) = WPE K[v] {{Phi}}` and
`bindp K Phi (exn s v) = Phi (exn s v)` -- on a value it keeps evaluating the
context, on an exception it short-circuits to the exceptional postcondition. This
is the convergence-critical lemma. The heap rules are orthogonal to exceptions,
and the two call rules are the composition story of Section 3.6. Loops unfold one
iteration (While/ForNil/ForCons); on top of ForCons a structural fold rule carries
a user invariant over the remaining suffix of the iterated list and re-establishes
it (or escapes through the exceptional arm) at each element, and a heap-counter
`while` rule closes counting loops by Loeb induction. Each rule has a matching
*stage tactic* (Section 3.7): `pure_step` fires Let/Op/IfT/IfF/TryV/TryC,
`heap_load`/`store`/`alloc` the heap rules, `call_opaque`/`call_transparent` the
call rules, `raise_step` Raise/Unwind, and `loop_unfold` the loop rules.

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

### 3.4 Contracts compile to `iProp`, composed with the separating conjunction

Contracts remain ordinary Python -- plain `assert` statements (leading =
precondition, trailing-before-return = postcondition, in-loop = invariant) or a
verifier-only `axiomander:` docstring. A shared `ContractLinter` parses them into
a contract IR; a backend-specific pass (`contract_ir_iris`) compiles that IR to
`iProp`. Pure facts are injected with the persistent embedding `\ulcorner P
\urcorner`; resource facts compile to points-to assertions.

| Python contract fragment | `iProp` |
|---|---|
| `assert x >= 1` | $\ulcorner x \ge 1 \urcorner$ |
| `assert implies(A, B)` | $\ulcorner A \to B \urcorner$ |
| `assert all(x != i for i in range(0,10))` | $\ulcorner \forall i,\ 0 \le i < 10 \to x \ne i \urcorner$ |
| `owns(box)` | $\textit{box.value} \mapsto v$ (a resource, *not* under $\ulcorner\cdot\urcorner$) |

The decisive design choice is that **the default composition of contract clauses
is the separating conjunction $\ast$, not $\wedge$.** When a precondition or
postcondition is built from several `assert`s, they are joined with $\ast$. For
the current pure-integer fragment this costs nothing, since
$\ulcorner P \urcorner \ast \ulcorner Q \urcorner \dashv\vdash \ulcorner P
\wedge Q \urcorner$; but it means the *same* composition rule already accounts
for disjoint resources, and it is the connective that will let us scale to
invariants and atomic updates without changing the front end.

A typical mixed pure/resource contract, written by the user with no Iris
notation:

```python
def bump(box: Box) -> int:
    """
    axiomander:
        requires:
            owns(box)
            box.value >= 0
        modifies:
            box.value
        ensures:
            owns(box)
            box.value == old(box.value) + 1
            result == box.value
    """
    box.value = box.value + 1
    return box.value
```

compiles to the Hoare triple

$$
\{\ \textit{box.value} \mapsto n \ast \ulcorner n \ge 0 \urcorner\ \}
\quad
\textit{bump(box)}
\quad
\{\ r.\ \textit{box.value} \mapsto n+1 \ast \ulcorner r = n+1 \urcorner\ \}.
$$

`owns(box)` plus `modifies: box.value` *is* the resource footprint; the user
never writes $\ast$, $\mapsto$, masks, or proof-mode tactics.

### 3.5 The frame rule is free, and so is composition

Because assertions are `iProp`, the structural frame rule

$$
\frac{\{P\}\ c\ \{Q\}}{\{P \ast R\}\ c\ \{Q \ast R\}}
$$

holds without a side condition: any resource $R$ describing a disjoint region of
the heap is carried across `c` by the separating conjunction, automatically.
Compared with Section 2, the entire `clobber`/`forall v \notin writes`
apparatus, and the per-callee per-variable frame-lemma generator that papered
over it, simply disappear. Locality stops being something we encode and becomes
the shape of the logic. This is the single biggest reason for the migration:
*composability is sound, not merely convenient.*

### 3.6 Opaque vs. transparent calls: stubbing as a logical primitive

Calls are dispatched through a **contract table** (an Iris `FunCtx`) that maps
each callee to its specification. SnakeletWp provides two call rules:

- **Transparent call** -- the callee's body is available and is unfolded; used
  for first-party functions being verified in the same run.

- **Opaque call** -- only the callee's *contract* is available; the caller
  consumes the callee's precondition (giving up the relevant resources),
  receives its postcondition, and frames the rest. Schematically, for a callee
  with spec $\{P_g\}\ g\ \{Q_g\}$:

$$
\frac{P_g \ast R \quad\quad \forall r.\ (Q_g \ast R) \vdash \mathrm{wp}\ K\ \{\Phi\}}
{\;\mathrm{wp}\ (\mathsf{call}\ g;\ K)\ \{\Phi\}\;}
$$

The opaque rule is exactly **stubbing as a logical primitive**. A library
function is given a contract -- in a `.pyi` stub or an `axiomander:` docstring --
and that contract enters the `FunCtx`; callers prove against it via the opaque
rule, and the body is never required. It is also exactly **modular verification
under iteration**: a transparent callee can be re-declared opaque once its
contract is stable, and its callers' proofs depend only on the contract, so a
body edit does not disturb them. The `FunCtx` entry's hash is the summary that
our incremental cache keys on.

### 3.7 Staged, syntax-directed proofs with independent failure

SnakeletWp ships a small instruction set of **stage tactics** -- `pure_step`,
`case_bool`, `call_opaque`, `call_transparent`, `finish_pure`, and a
precondition-discharge stage `call_opaque_pre` -- and the proof generator
(`iris_proof_gen`) emits exactly one stage per IR node, chosen by the node's
syntax and the callee's table entry. The generator performs no symbolic
execution and needs no knowledge of intermediate values: each stage tactic
extracts what it needs from the Iris goal at proof time. Loops are handled by an
`iLob`-based invariant stage, with the invariant taken verbatim from the user's
in-loop `assert`. The proof script *is* the trace.

The payoff for the LLM loop is that **stages fail independently with classifiable
errors**. When `call_opaque_pre` cannot discharge a callee precondition (e.g.
nonlinear arithmetic, a string fact), the residual is exported to SMT; an UNSAT
result is imported as `Axiom smt_ax_N : ...` and the stage is regenerated as
`call_opaque_pre (exact smt_ax_N)`. A pure postcondition that `finish_pure`
cannot close (`reflexivity`/`lia`) is likewise an SMT candidate, and beyond SMT
the *structured residual goal* -- a named stage plus the goal state from
coq-lsp, rather than a stderr regex -- is what the LLM oracle receives. Small
named obligations give better SMT performance, better LLM prompts, per-stage
caching, and parallelism, and they mean a failed attempt yields a reusable
artifact rather than a dead end.

### 3.8 What the Iris choice does and does not change

The migration is deliberately confined to the proof backend. The
`ContractLinter`, the SMT export (`smt_export`, `theory_smt`), the LLM oracle,
and the function-level incremental cache are all backend-agnostic; the contract
IR diverges only at the final rendering step (flat-store `to_coq` vs.
`contract_ir_iris.iris_prop`). Iris *adds* per-stage hashing for finer-grained
reuse but does not replace the cache. From the user's side, nothing changes:
contracts are still decorator-free Python, and `owns(...)` is the only new,
entirely optional, resource vocabulary.

---

## 4. Discussion and relation to prior work

Axiomander's separation-logic interpretation of object fields and its opaque
call rule are textbook Iris; the novelty is not in the logic but in the *system
context*. To our knowledge the combination is unusual: (i) the assertion logic
is never exposed to the user -- contracts are plain Python and the separating
conjunction is the implicit default composition; (ii) the proof obligations are
generated and largely discharged by an LLM operating on structured residual
goals, with Iris/Rocq as the trust kernel; and (iii) the same `FunCtx` opaque
rule serves simultaneously as modular verification, incremental-reuse boundary,
and library stubbing mechanism. We see Axiomander as a stress test of the claim
that Iris's framing and ownership story is the right substrate for *automated*,
composition-heavy verification, not only for expert-driven interactive proof.

Our experience also offers a small, concrete data point: building a verifier
without a substructural logic and then retrofitting locality (Section 2) is
costly and bounded; starting from Iris (Section 3) makes the very properties our
LLM loop depends on -- frame, stub, reuse -- definitional.

---

## 5. Status and open questions for the community

**Status (June 2026).** Snakelet and SnakeletWp are complete and free of
`Admitted` across the full rule set: the core fragment (binop, let, if,
load/store/alloc, opaque/transparent call) and the exception-aware extension with
its `Result`-typed postcondition and loop rules, whose eight-lemma convergence
gate is `Qed`. The staged generator, the end-to-end Python-to-Iris pipeline
(sharing the `ContractLinter`), the contract-to-`iProp` compiler, and the
SMT-axiom escalation slot are in place, with tens of Iris-specific tests passing
alongside the mature flat-store backend. Remaining work wires the exception
calculus into the Python lowering and extends the fragment to loop invariants over
shared disjoint memory, in-place data-structure mutation, and a typed subset
(strings/floats/`isinstance`/`None`).

We would value the community's view on:

1. **Ownership inference from `modifies`.** We currently derive a footprint from
   explicit `owns(...)` plus `modifies:`. How far can footprints be *inferred*
   for an LLM-generated body without burdening the user, and what is the right
   failure mode when inference is ambiguous?

2. **Specs as the LLM's search space.** The LLM proposes both code and helper
   contracts. Are there idioms (magic wands, representation predicates, abstract
   predicates with `FunCtx`-level abstraction) that are especially amenable to
   automatic *generation*, as opposed to automatic *use*?

3. **Residual goals as oracle inputs.** We feed a failed stage's goal state to an
   LLM. Which Iris proof-mode presentations of a residual (hypothesis naming,
   spatial/persistent split, masks elided) make the best prompts?

4. **Concurrency on the same front end.** Our composition default is already
   $\ast$. What is the minimal extension of the decorator-free contract surface
   that could express invariants/atomic updates without exposing Iris syntax to
   the user?

5. **Trust surface.** With SMT-discharged facts imported as axioms and
   LLM-generated proofs re-checked by Rocq, the kernel remains the authority but
   the axiom slots are a trust boundary. What discipline (e.g. logged query
   hashes, replay) would the community consider acceptable for reproducibility?

---

## References and pointers

This paper summarises material developed in the Axiomander repository:

- Iris migration plan and current state -- `docs/iris-migration-plan.md`.
- Iris backend prototype (the `bump`/`owns` example, resource classification) --
  `docs/axiomander_iris_backend_prototype_plan.md`.
- Per-callee frame lemmas in the flat-store backend (Section 2) --
  `docs/frame-lemmas.md`.
- Staged proof engineering (small named obligations, residual capture) --
  `docs/staged_proof_engineering_guide.md`.
- Incremental verification as a build system (contracts as interfaces, proofs as
  cached artifacts) -- `docs/incremental_verification_cache_design.md`.
- Companion whitepaper and slides motivating vericoding -- `docs/whitepaper.md`,
  `docs/slides/`.
