# Vericoding with Axiomander

### Specification is the control surface. Code is a derived artifact. Correctness requires proof.

**Scidonia — Axiomander whitepaper**

---

## Abstract

Large language models (LLMs) write code that *looks* like a solution to the
request they were given. They are trained to satisfy the prompt, and they are
systematically optimistic: edge cases, error paths, and invariants are glossed,
and "the happy path runs" is treated as success. Types and tests narrow this gap
but do not close it — both are *samples* of intent rather than *statements* of
it.

This paper argues for **vericoding**: a development methodology in which a
*strong specification* is the primary, human-maintained artifact, the
implementation is a derived and disposable artifact produced by an LLM, and a
verifier delivers a deterministic, machine-checked verdict on whether the code
meets the specification. When the verdict is negative, a **heal-loop** returns a
structured residual — the exact remaining proof obligation, with hypotheses, and
where applicable a concrete counterexample — that drives the next implementation
attempt. The LLM is given freedom in *sub-specification*: it may decompose the
problem into helper functions, each carrying its own contract, which are checked
the same way. Because proofs compose through contracts (not implementations),
iteration and library **stubbing** scale without whole-program re-verification.

[Axiomander](https://github.com/scidonia/axiomander) is a concrete realisation
of this methodology for Python. Its stack is

$$\textbf{Axiomander} \;=\; \text{LLM} \;+\; \text{Rocq} \;+\; \text{Iris} \;+\; \text{Python}.$$

Python is the source language; the **Rocq** proof assistant (formerly Coq) is
the trust kernel; **Iris** — a separation-logic framework built on Rocq —
supplies the weakest-precondition calculus and the heap reasoning for mutable
values; and the **LLM** is the proof and code oracle that closes the residual
goals. Obligations are discharged through a tiered pipeline: deterministic Rocq
tactics, SMT/Hammer, a theory-dispatched SMT oracle for strings/regex/dimensions,
and finally the LLM oracle. The weakest-precondition calculus is proven sound in
Rocq/Iris, so the verdict is trustworthy by construction.

Vericoding as a *methodology* does not depend on this particular stack. Rocq is
*one possible* proof assistant; the same loop — strong specification, derived
code, machine-checked verdict, residual-driven repair — works over any backend
that can deliver a sound, deterministic decision and a structured residual on
failure. Axiomander commits to Rocq + Iris because separation logic is the right
foundation for reasoning about the mutation and aliasing that real Python
exhibits.

---

## 1. Why Vericoding?

### 1.1 The optimism problem

An LLM optimises for *apparent* intent satisfaction. Given a prompt, it produces
the most probable continuation that resembles a correct answer. This has a
characteristic failure mode: plausible code that is subtly wrong. The model is
not adversarial — it is optimistic. It assumes the inputs it didn't think about
behave like the ones it did, that the invariant it never wrote down holds, and
that the error path it omitted is unreachable.

The danger is that this failure mode is **silent**. The code compiles. The
example runs. A reviewer skims it and it reads correctly. Nothing surfaces the
gap between *the request was satisfied in appearance* and *the intent was
satisfied in fact*.

We therefore need a mechanism that decides — **deterministically** — whether a
piece of software meets its intent, across all inputs, not just the ones we
sampled.

### 1.2 The ladder of guarantees

| Mechanism | Catches | Misses |
|---|---|---|
| Prompt review | gross misunderstanding | everything subtle |
| Types | shape errors | values, relations, invariants |
| Tests | the cases you thought of | the cases you didn't |
| **Strong specification** | **anything expressible as a property** | **only what you leave unstated** |

Types constrain the *shape* of data; they say nothing about the *relationship*
between inputs and outputs. Tests assert facts at finitely many points. A
strong specification is a *total* statement of the intended input/output
relation — and, crucially, it can be **proved**, not merely sampled.

### 1.3 Tests sample; proofs quantify

A test is a finite set of points:

```python
def test_clamp():
    assert clamp(5, 0, 10) == 5
    assert clamp(-3, 0, 10) == 0
    assert clamp(99, 0, 10) == 10
```

Green means *these three* inputs are right. A specification is a statement over
*all* inputs:

$$\forall\, v, lo, hi.\;\; lo \le hi \;\Rightarrow\; lo \le \mathrm{clamp}(v, lo, hi) \le hi$$

Proved means *every* input is right. A passing test is evidence; a proof is a
guarantee.

### 1.4 What "vericoding" means

Vericoding is a loop:

1. The human writes and iterates on a **strong specification**.
2. An LLM proposes an **implementation** to satisfy it.
3. A **verifier** decides — deterministically — whether the code meets the spec.
4. On failure, the verifier returns a **structured residual** that drives the
   next attempt.

The specification is the thing you maintain. The code is generated, checked, and
regenerated underneath it.

---

## 2. The Methodology

### 2.1 Specification is the control surface

You steer the system by editing the *specification*, not the code. In the
traditional model, the code is the artifact you read, edit, and trust, while
tests sample it from the side. In vericoding, the specification is the artifact
you read, edit, and trust; the LLM emits code beneath it; and the verifier proves
the code against the spec.

```
Traditional                         Vericoding

  Human --writes--> Code              Human --writes--> Specification
  Code  --hopefully--> Intent         Spec  --drives--> LLM
  Tests --sample--> Code              LLM   --emits--> Code
                                      Verifier --proves--> Spec
                                      Code --> Verifier
```

The reviewable surface shrinks from "all the code" to "the contracts at the
boundary."

### 2.2 Code is a derived artifact

The implementation is **disposable**. If it doesn't verify, throw it away and
regenerate. The specification persists across many implementations. This inverts
the usual trust relationship: we do not trust the code because we read it — we
trust it because it was *proved* against a specification that we *did* read.

$$\underbrace{(P, Q)}_{\text{spec, human-authored}} \;\;\leadsto\;\; \underbrace{c}_{\text{code, LLM-derived}} \quad\text{such that}\quad \vDash \{P\}\, c \,\{Q\}$$

The human authors *both* halves of the specification: the assumption $P$ on
inputs and the guarantee $Q$ on outputs. The code is derived to make $Q$ hold
*under* the assumption of $P$ — the obligation only ever requires $Q$ on
$P$-constrained inputs.

### 2.3 Correctness requires proof

A specification is only as good as our ability to **discharge** it. Runtime
contracts catch violations *after* deployment, on whatever inputs happen to
occur. Static proof catches violations *before* deployment, on **all** inputs.
Axiomander reduces "does the code meet the spec?" to a Rocq proof obligation — a
binary, deterministic verdict:

$$\{P\}\;c\;\{Q\} \;\;\equiv\;\; \forall s.\; P(s) \Rightarrow \mathrm{wp}\,(c, Q)(s)$$

The Hoare triple holds iff the precondition implies the weakest precondition of
the body with respect to the postcondition. This equivalence is proven sound in
Rocq/Iris (Section 3.6).

### 2.4 The heal-loop

The verifier does not merely say "no." It says *why*, in a form the LLM can act
on:

```
Strong spec --> Proof obligations --> Proved?
                                        |-- yes --> Done: certified code
                                        '-- no  --> Residual goal + counterexample
                                                       --> LLM repair
                                                       --> new code / new sub-spec
                                                       --> (back to obligations)
```

Two things distinguish a heal-loop from naive re-prompting:

- A **counterexample** is a concrete witness of failure — typed values, not
  vibes.
- A **residual goal** is the exact remaining obligation with its hypotheses.

The LLM repairs against the residual, not against the original prompt.

### 2.5 Why the heal-loop beats re-prompting

Naive re-prompting gives the model no signal:

```
LLM:   here is code
human: it's wrong
LLM:   here is different code
human: still wrong
```

The model simply guesses again. A heal-loop hands the model the failing fact:

```
Goal:          lo <= result <= hi
Hyp:           val > hi
Counterexample: result = val   (= 99, > hi)
```

Now the model fixes *that*. Determinism turns "convince a reviewer" into "close a
goal."

### 2.6 Freedom in sub-specification

To prove the **entry point**, the LLM must specify the **helpers** it introduces.
The human writes the top-level contract — the one surface of understanding. The
LLM is free to decompose the problem: introduce helper functions, each with its
*own* contract. Those sub-specifications are the LLM's degrees of freedom — they
are how it makes the global proof go through — and they are checked the same way.
There is no privileged, unverified layer.

$$
\frac{\{P_g\}\,g\,\{Q_g\} \qquad \{P_f\}\,f\,\{Q_f\}\ \text{using}\ Q_g}{\{P_f\}\,f\,\{Q_f\}}
$$

The caller's proof uses only the callee's *contract* $Q_g$, never its body.

### 2.7 Why composability is non-negotiable

If every edit re-checked the whole program, vericoding would not scale. Three
forces demand composability:

- **Iteration cost.** You change one spec; you should re-verify only what depends
  on it.
- **Stubbing.** A library you can't (or won't) verify is replaced by its
  *contract*; callers prove against the stub's axioms.
- **Locality of trust.** A function's body can change freely as long as its
  contract is stable — callers are untouched.

The operating principle, borrowed from incremental build systems:

> Body changes invalidate local proofs. Contract changes invalidate callers.

### 2.8 Composition, formally

A contract is an *interface*; a proof is a *cached build artifact*. Each function
exports a semantic summary:

$$
\mathrm{summary}(g) = \mathrm{hash}\big(\text{pre},\ \text{post},\ \text{reads},\ \text{writes},\ \text{raises}\big)
$$

A caller $f$ depends on $\mathrm{summary}(g)$ — *not* on $g$'s implementation. If
$g$'s body changes but $\mathrm{summary}(g)$ is stable, $f$'s proof is **reused**.
If $\mathrm{summary}(g)$ changes, only $f$ and its transitive callers are
re-verified. The verifier becomes *a build system for correctness*, not a batch
theorem prover.

### 2.9 Stubbing libraries as axioms

You do not verify `dict.get`. You *declare its contract* and prove against it:

```python
# stubs/builtins.pyi  — the contract, not the implementation
def get(d: dict, k, default):
    """
    axiomander:
        ensures:
            implies(k in d, result == d[k])
            implies(k not in d, result == default)
        modifies:
            none
    """
```

The stub's `ensures` becomes an **axiom** available to callers. The trust
boundary is explicit and small: it is the stub, written once and reviewed once.
This replaces optimism ("the LLM probably calls `get` correctly") with an
enforced contract. Library functions can declare `reads`/`writes` in `.pyi`
stubs; the docstring and stub syntaxes lower to the same internal contract map.

---

## 3. The Axiomander Architecture

### 3.1 The stack: LLM + Rocq + Iris + Python

$$\textbf{Axiomander} \;=\; \text{LLM} \;+\; \text{Rocq} \;+\; \text{Iris} \;+\; \text{Python}.$$

Each layer has a distinct role:

- **Python** — the source language. The user writes ordinary Python; contracts
  are plain `assert` statements or verifier-only `axiomander:` docstrings.
- **Rocq** — the proof assistant (formerly named Coq) and the trust kernel.
  Every accepted verdict bottoms out in a Rocq-checked proof term. Rocq is the
  *final authority*; nothing is "proved" until Rocq says so.
- **Iris** — a separation-logic framework built on top of Rocq. Iris supplies
  the weakest-precondition calculus and, crucially, the *heap* reasoning needed
  for Python's mutation and aliasing. Separation logic is what lets a caller
  reason locally about the part of the heap a callee touches and frame off the
  rest — the formal engine behind composability (Sections 2.7–3.7).
- **LLM** — the oracle that closes residual goals and proposes implementations
  and sub-specifications. It operates *inside* the loop, on structured residual
  proof state, never as the trust kernel.

**Rocq is one possible backend.** Vericoding as a methodology is
backend-agnostic: any proof assistant or solver that can return a sound,
deterministic decision plus a structured residual would serve. Axiomander
commits to Rocq + Iris because separation logic is the correct foundation for
the mutation, aliasing, and resource ownership that real Python programs
exhibit. The Python front end, the contract language, and the heal-loop are
unchanged regardless of which proof backend sits underneath; swapping the
backend changes only the obligation-emission and proof-discharge layers.

### 3.2 From Python to a proof obligation

```
Python + asserts / axiomander: docstrings
        |
        v
  contract_linter.py  ->  Contract IR
        |
        v
  py_to_imp.py         ->  IMP body
        |
        v
  obligation_gen.py    ->  Rocq obligations
        |
        v
  Level 1: deterministic Rocq  --residual-->
  Level 2: SMT / Hammer       --residual-->
  Level 2b: theory-SMT (strings/regex/floats)  --residual-->
  Level 3: rocq-piler + LLM oracle
        |
        v
     Certified
```

Contracts are plain `assert` statements or verifier-only `axiomander:` docstring
blocks — zero imports, zero decorators. The user's code stays dependency-free;
the verification machinery does the heavy lifting.

### 3.3 Contracts as ordinary Python

```python
def clamp(val: int, lo: int, hi: int) -> int:
    assert lo <= hi                       # precondition
    if val < lo:    result = lo
    elif val > hi:  result = hi
    else:           result = val
    assert lo <= result <= hi             # postcondition
    assert implies(val < lo, result == lo)
    assert implies(val > hi, result == hi)
    return result
```

Leading assertions are preconditions; trailing assertions after the result
assignment are postconditions; loop-body assertions are invariants. The richer
`axiomander:` docstring block carries `requires / ensures / where / reads /
modifies / raises / units`. The linter classifies assertions by **position** and
lowers everything to the Contract IR.

### 3.4 The intermediate language and the heap: IMP over Iris

Axiomander does not prove properties of arbitrary Python. It lowers a verified
subset to a small imperative language, IMP:

$$
\begin{aligned}
e ::=&\ n \mid x \mid e_1 + e_2 \mid e_1 - e_2 \mid e_1 * e_2 \mid e_1 == e_2 \mid e_1 < e_2 \mid \neg e \mid \dots \\[4pt]
c ::=&\ \mathsf{skip} \mid x := e \mid c_1 ; c_2
   \mid \mathsf{if}\ e\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2
   \mid \mathsf{while}\ e\ \mathsf{inv}\ I\ \mathsf{do}\ c
   \mid \mathsf{assert}\ P
\end{aligned}
$$

Values are `VZ | VBool | VUnit`, extended with structural `VList | VTuple |
VDict`. Immutable values are structural, like Dafny's `seq` and F\*'s `list`;
mutable operations (append, pop) work on a **heap** representation that
*parallels* the immutable value. This is exactly where **Iris** earns its place
in the stack: the parallel heap is modelled in Iris's separation logic, so
ownership of a mutable object is a separating resource. A function's frame is
then the slice of the heap it owns, and everything outside that slice is
preserved *by construction* of the separating conjunction — the formal basis for
the frame rule in Section 3.8. IMP is small enough to formalise and prove sound,
yet rich enough to cover the verified subset of Python:

- Python `if/else` -> IMP `if`
- Python `while` -> IMP `while` (invariant from a loop-body assertion)
- Python assignments -> IMP `:=`
- Python `for i in range(n)` -> IMP `while` with a counter
- Python `return e` -> `result := e`

The IMP-over-Iris layer is the part of the stack that is specific to the Rocq +
Iris backend. A different proof assistant would lower Python to a different
object language; the Python front end and contract language above this layer are
unchanged.

### 3.5 Weakest precondition calculus

The WP calculus is the single source of truth, proven sound in Rocq/Iris:

$$
\begin{aligned}
\mathrm{wp}(\mathsf{skip}, Q) &= Q \\
\mathrm{wp}(x := e, Q) &= Q[x \mapsto e] \\
\mathrm{wp}(c_1 ; c_2, Q) &= \mathrm{wp}(c_1,\ \mathrm{wp}(c_2, Q)) \\
\mathrm{wp}(\mathsf{if}\ e\ \mathsf{then}\ c_1\ \mathsf{else}\ c_2, Q) &= (e \Rightarrow \mathrm{wp}(c_1,Q)) \wedge (\neg e \Rightarrow \mathrm{wp}(c_2,Q)) \\
\mathrm{wp}(\mathsf{while}\ e\ \mathsf{inv}\ I\ \mathsf{do}\ c, Q) &= I
\end{aligned}
$$

For loops, the invariant $I$ does not capture the loop semantics directly;
instead it generates two verification conditions:

$$
\text{VC}_1:\ I \wedge \neg e \Rightarrow Q
\qquad\qquad
\text{VC}_2:\ I \wedge e \Rightarrow \mathrm{wp}(c, I)
$$

VC$_1$ says the invariant plus the exit condition implies the postcondition;
VC$_2$ says the loop body preserves the invariant.

### 3.6 Soundness

The theorem that makes the verdict trustworthy:

$$
\{P\}\,c\,\{Q\} \;\;\Longleftrightarrow\;\; \big(\forall s.\; P(s) \Rightarrow \mathrm{wp}(c, Q)(s)\big)
$$

Proved by induction on the structure of $c$. Consequently, for a function `f(x)`
with precondition `P` and postcondition `Q` and body `c`, the top-level
obligation is:

$$
\forall x.\; P(x) \;\Rightarrow\; \mathrm{wp}\big(c,\ \lambda\, \mathit{result}.\ Q(x, \mathit{result})\big)
$$

which Axiomander emits as a Rocq theorem:

```coq
Theorem f_correct : forall x, P x -> wp c (fun result => Q x result).
Proof.
  (* discharged by the tiered pipeline *)
Qed.
```

### 3.7 Frames: calls reason from contracts

A callee's `modifies:` set is its *write frame*. Callers rely on everything
outside the frame being preserved across the call.

```python
def inc(x: int) -> int:
    """ axiomander:
        requires: x >= 0
        modifies: none
        ensures:  result == x + 1 """
    result = x + 1
    return result

def frame_two_calls(a: int, b: int) -> int:
    """ axiomander:
        ensures: a == old(a); b == old(b); result == a + b + 2 """
    a2 = inc(a); b2 = inc(b)
    result = a2 + b2
    return result
```

The CCall rule proves that any variable outside `target :: writes` is preserved:
$\forall v.\ v \notin (\textit{target} :: \textit{writes}) \Rightarrow v' = v$.
For CCall-heavy functions, Axiomander generates decomposed obligations: per-call
frame lemmas, one stage lemma per call, a post lemma, and a composition theorem
using `wp_seq_decompose`.

### 3.8 The frame rule

This is what makes proofs *local* — the heart of composability:

$$
\frac{\{P\}\,c\,\{Q\} \qquad \mathrm{modifies}(c) \cap \mathrm{free}(R) = \varnothing}{\{P \wedge R\}\,c\,\{Q \wedge R\}}
$$

Any assertion $R$ about variables the callee does not touch survives the call for
free. The caller never unfolds the callee's body; it uses only the contract plus
the frame. Axiomander generates per-callee frame lemmas so each `apply` fires
independently and produces its own residual on failure. In the Rocq + Iris
backend this rule is not an add-on but the *native* shape of separation logic:
$R$ describes a disjoint region of the heap, and the separating conjunction
carries it across the call automatically. Iris is the reason composability is
sound rather than merely convenient.

### 3.9 The proof pipeline: three tiers

| Level | Mechanism | Handles |
|---|---|---|
| **1** | deterministic Rocq (`wp_reduce`, `lia`) | assignments, conditionals, loops, frame/CCall obligations — ~80% of goals |
| **2** | SMT / Rocq-hammer (cvc4, cvc5, eprover) | linear and non-linear arithmetic, first-order residuals |
| **2b** | theory-SMT (Z3 / CVC5 `QF_SLIA`) | strings, contains/prefix/suffix, regex subsumption, float dimensions |
| **3** | rocq-piler + LLM oracle | loop invariants, induction, deep lemma chains |

Cheap, deterministic tactics run first. The LLM is the **fallback**, not the
first resort. Level 1 clears roughly four-fifths of goals before any external
prover is invoked.

### 3.10 Staged obligations, never one giant theorem

> Never lose partial proof work. A failed attempt produces reusable artifacts,
> not dead ends.

The system is not structured as "try Rocq; if Rocq fails, ask the LLM." It is
structured as a pipeline of small, stably-identified obligations:

```
Program -> IR -> Verification Conditions -> Normalization
        -> Mechanical tactics -> SMT -> Residual goals -> LLM assistance
        -> Re-integrate result
```

Each obligation has a stable identifier such as
`sort.insert.preserves_sorted.branch_2`. A failed stage emits a residual goal
with its hypotheses — exactly what the LLM needs — and the LLM operates on the
*residual proof state*, not on the original program:

```
Context:  xs_sorted : sorted(xs)
          pivot_le_head : pivot <= head(xs)
Goal:     sorted(pivot :: xs)
```

Per-obligation caching, parallelisation, and fine-grained reuse all follow from
this structure.

### 3.11 Counterexamples close the loop

When a goal is *false*, the verifier produces a concrete typed witness. For
regex contracts via the theory-SMT oracle:

```python
def accept(p: str) -> str:
    """ axiomander:
        requires: p.re_match("[0-9]{3}")
        ensures:  result.re_match("[a-z]+") """
    result = p
    return result
```

```
COUNTEREXAMPLE
  result = "000"
  satisfies requires-regex
  violates  ensures-regex
```

A digit string can never match `[a-z]+`. Dimensional analysis works the same
way: mixing `[USD]` and `[GBP]` is a typed dimension error, rejected before the
proof even runs. Counterexamples carry typed `TheoryValue` objects (quoted
strings, unscaled floats) and are surfaced in the report with an explanation of
which postcondition failed.

### 3.12 Incremental verification = a build system for correctness

```
Edit -> re-hash function
         |-- body changed?     -- yes --> re-verify this function only
         |-- contract changed? -- yes --> re-verify function + transitive callers
         '-- contract changed? -- no  --> reuse cached proofs
```

| Change | Re-verify |
|---|---|
| body only | the function |
| local assert / invariant | the function |
| **contract** | the function + direct + transitive callers |
| **callee contract** (`summary` hash) | the caller |

Each function carries a cache entry recording its body hash, contract-signature
hash, local-assertion hash, callees, callee-contract hashes, obligation hash, and
proof results. Caching occurs at the *obligation* level, keyed on the normalised
obligation, the imported contract summaries, the logical environment, the prover
configuration, and the tool version. This enables partial proof reuse,
fine-grained invalidation, and scalable verification — without whole-project
re-verification after every edit.

### 3.13 Dogfooding: Axiomander verifies itself

Axiomander carries contracts on its own logic. The function that decides whether
a verification goal passed is itself verified at Level 1:

```python
def is_proved(self) -> bool:
    """ axiomander:
        ensures:
          implies(self.level == ProofLevel.UNPROVED, result == False)
          implies(self.level == ProofLevel.COUNTEREXAMPLE, result == False)
          implies(self.level != ProofLevel.UNPROVED
                  and self.level != ProofLevel.COUNTEREXAMPLE, result == True)
    """
    return self.level not in (ProofLevel.UNPROVED, ProofLevel.COUNTEREXAMPLE)
```

Enum names (resolved to integer encodings from the AST), `implies()` per case,
attribute access (`self.level`, auto-flattened to `self_level: Z`), and `not in`
over a tuple are all lowered to IMP and discharged deterministically. Over a
dozen further functions — covering `isinstance` AST dispatch, string methods,
list/set construction, and Pydantic object construction — are self-verified
across Levels 1 and 3.

### 3.14 Tooling: verification in the editor (MCP)

Axiomander is an MCP server, so verification lives where the code is written.

| Tool | What it does |
|---|---|
| `check-file` | analyse a file for contract adornment opportunities |
| `check-function` | verify a single function (Level 1) + suggest contracts |
| `verify-function` | full verification (Level 1 -> 2 -> 3) |
| `verify-changed` | incremental — re-verify only changed functions |
| `verify-impacted` | dry-run — show what *would* re-verify |
| `explain-cache` | why a proof was reused or regenerated |
| `frame-report` | pre/post/invariant + frame conditions |

The first verification run compiles Rocq (a few seconds); subsequent runs hit the
cache (milliseconds).

---

## 4. What This Buys You

The argument, end to end:

- LLMs are **optimistic**; they satisfy the prompt, not the intent.
- Types and tests **sample** intent; a strong specification **states** it
  totally.
- Make the **specification the control surface** — iterate on it, derive code
  under it.
- A **heal-loop** drives the LLM on residual goals and counterexamples, not
  re-prompts.
- The LLM has freedom in **sub-specification**; helpers get contracts, checked
  the same way.
- **Composability** (the frame rule plus contract hashing) makes iteration and
  **stubbing** scale.
- Axiomander reduces all of this to **Rocq proof obligations**, soundly, through a
  tiered pipeline.

> Specification is the control surface. Code is a derived artifact. Correctness
> requires proof.

---

## References and Further Reading

- [`README.md`](../README.md) — project overview, quick start, full feature
  walkthrough.
- [`docs/ARCHITECTURE.md`](ARCHITECTURE.md) — pipeline stages and Rocq theory
  structure.
- [`docs/WP_CALCULUS.md`](WP_CALCULUS.md) — Hoare triples, WP definition, and
  soundness.
- [`docs/CONTRACT_LANGUAGE.md`](CONTRACT_LANGUAGE.md) — the full contract
  sublanguage (operators, sections, quantifiers, regex, units, exceptions,
  Pydantic).
- [`docs/incremental_verification_cache_design.md`](incremental_verification_cache_design.md)
  — contracts as interfaces, proofs as cached build artifacts.
- [`docs/staged_proof_engineering_guide.md`](staged_proof_engineering_guide.md)
  — small named obligations, residual capture, and the tactic ladder.
- [`docs/case-dispatch-verification.md`](case-dispatch-verification.md) —
  case-analysis over finite dispatch tables.
- Slide deck: [`docs/slides/`](slides/) — the presentation companion to this
  whitepaper.
