"""Syntax-directed Iris proof generator (Phase 2 of the Iris backend).

Walks a SnakeletIR expression and a function table, emitting a complete
.v file with:

  1. SMT-trusted axioms (obligations discharged externally),
  2. the FunCtx table: pre/post definitions, the entry table, a
     mechanically-proven totality lemma, and the instance,
  3. a theorem stating WP body {{ v, post }},
  4. a staged proof script -- one stage tactic per IR node.

The generator never executes the program.  Stage *selection* is
determined by IR syntax plus the table entry kind (FunSpec -> opaque,
FunDef -> transparent); stage *semantics* live in the Coq stage tactics
(SnakeletTactics.v), which extract everything from the goal at proof
time.  Consequently the generator needs no symbolic execution and no
knowledge of intermediate values -- only the shape of the tree.

Symbolic-execution analogy: the walk is a forward strongest-postcondition
pass.  Conditionals on symbolic booleans fork the path (case_bool) and
the continuation stages are duplicated into each arm; the branch
hypothesis acts as the path constraint.  Loops are out of scope until
invariant cut points land (phase 4).

SMT escalation contract: a call stage whose precondition the mechanical
ladder (snakelet_solve_pre) cannot solve is regenerated as
call_opaque_pre (<tactic referencing an smt axiom>); the axiom text is
supplied by the SMT pipeline and emitted at the top of the file.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, Union

from oracle.snakelet_ir import (
    SAlloc, SApp, SBinOp, SExpr, SIf, SLet, SLit, SLoad, SReturn, SSeq,
    SStore, SVar, SWhile,
)

# Coq unicode tokens, kept out of literals so the Python source stays ASCII.
TSTILE = "\u22a2"   # entailment turnstile
LCEIL = "\u231c"    # pure assertion left bracket
RCEIL = "\u231d"    # pure assertion right bracket


class IrisGenError(Exception):
    """Raised when an IR shape is outside the staged-generation fragment."""


# -- Function table -------------------------------------------------------

@dataclass
class OpaqueSpec:
    """Contract for an opaque function: pre/post over integer arguments.

    args: argument names used in the generated pre/post definitions.
    side: optional Coq Prop over the args (the nontrivial precondition);
          None means the precondition is just the arity/typing constraint.
    result: Coq Z expression over the args giving the (deterministic)
            result -- post is `r = LitInt (result)`.
    """
    args: list[str]
    side: Optional[str]
    result: str


@dataclass
class TransparentDef:
    """A helper definition that unfolds at call sites."""
    params: list[str]
    body: SExpr


FunEntry = Union[OpaqueSpec, TransparentDef]
FunTable = dict[str, FunEntry]


# -- Stage tree -----------------------------------------------------------

@dataclass
class Stage:
    """One staged tactic invocation."""
    tactic: str
    category: str
    comment: str = ""
    smt_relevant: bool = False


@dataclass
class Branch:
    """A path fork: one arm per goal produced by the preceding split."""
    arms: list[list["StageNode"]]


StageNode = Union[Stage, Branch]

_BULLETS = ["-", "+", "*", "--", "++", "**"]


# -- Table emission -------------------------------------------------------

def _emit_pre_def(name: str, spec: OpaqueSpec) -> str:
    binders = " ".join(f"({a} : Z)" for a in spec.args)
    args_list = "; ".join(f"LitInt {a}" for a in spec.args)
    body = f"args = [{args_list}]"
    if spec.side:
        body = f"{body} /\\ ({spec.side})"
    return (f"Definition {name}_pre (args : list sn_val) : Prop :=\n"
            f"  exists {binders}, {body}.")


def _emit_post_def(name: str, spec: OpaqueSpec) -> str:
    args_pat = "; ".join(f"LitInt {a}" for a in spec.args)
    return (f"Definition {name}_post (args : list sn_val) (r : sn_val) : Prop :=\n"
            f"  match args with\n"
            f"  | [{args_pat}] => r = LitInt ({spec.result})\n"
            f"  | _ => False\n"
            f"  end.")


def _emit_table(table: FunTable) -> str:
    """The entry table as a String.eqb chain (so totality can case-split)."""
    lines = ["Definition gen_table (f : string) : option fun_entry :="]
    if not table:
        lines.append("  None.")
        return "\n".join(lines)
    first = True
    for fname, entry in table.items():
        kw = "if" if first else "else if"
        first = False
        if isinstance(entry, OpaqueSpec):
            rhs = f"Some (FunSpec {fname}_pre {fname}_post)"
        else:
            params = "; ".join(f'"{p}"' for p in entry.params)
            rhs = f"Some (FunDef [{params}] {entry.body.to_coq()})"
        lines.append(f'  {kw} String.eqb f "{fname}" then {rhs}')
    lines.append("  else None.")
    return "\n".join(lines)


def _emit_totality(table: FunTable) -> str:
    """Mechanical proof that every spec'd entry is realizable.

    This is the callee-side total-correctness promise; in the full
    pipeline it is discharged when each implementation is verified
    against its contract.  Here the posts are deterministic equations,
    so `by eexists` realizes them.
    """
    lines = [
        "Lemma gen_table_total : forall f pre post vs,",
        "  gen_table f = Some (FunSpec pre post) -> pre vs -> exists v, post vs v.",
        "Proof.",
    ]
    if not table:
        lines.append("  intros f pre post vs Hf. unfold gen_table in Hf. discriminate Hf.")
        lines.append("Qed.")
        return "\n".join(lines)
    lines.append("  intros f pre post vs Hf Hpre. unfold gen_table in Hf.")
    for fname, entry in table.items():
        lines.append(f'  destruct (String.eqb f "{fname}"); simplify_eq.')
        if isinstance(entry, OpaqueSpec):
            pat = " & ".join(entry.args) + " & ->"
            if entry.side:
                pat += " & Hside"
            lines.append(f"  {{ destruct Hpre as ({pat}). by eexists. }}")
        # TransparentDef: both branches close via simplify_eq (FunDef <> FunSpec).
    lines.append("Qed.")
    return "\n".join(lines)


def _emit_table_section(table: FunTable) -> str:
    parts = []
    for fname, entry in table.items():
        if isinstance(entry, OpaqueSpec):
            parts.append(_emit_pre_def(fname, entry))
            parts.append(_emit_post_def(fname, entry))
    parts.append(_emit_table(table))
    parts.append(_emit_totality(table))
    parts.append(
        "#[global] Instance gen_fun_ctx : FunCtx :=\n"
        "  {| fun_entries := gen_table; fun_specs_total := gen_table_total |}."
    )
    return "\n\n".join(parts)


# -- Stage generation -----------------------------------------------------

def _is_value(e: SExpr) -> bool:
    return isinstance(e, (SLit, SVar))


def _check_anf_args(app: SApp) -> None:
    for a in app.args:
        if not _is_value(a):
            raise IrisGenError(
                f"call to '{app.func}' has a non-value argument "
                f"({type(a).__name__}); bodies must be in ANF -- "
                f"let-bind intermediate results")


def _gen(e: SExpr, table: FunTable, overrides: dict[str, str],
         k) -> list[StageNode]:
    """Generate stages reducing e to a value, then continue with k().

    k is a thunk producing the continuation stages; it is invoked once
    per execution path (duplicated into each arm of a case split).
    """
    if isinstance(e, (SLit, SVar)):
        return k()

    if isinstance(e, SReturn):
        return _gen(e.value, table, overrides, k)

    if isinstance(e, SSeq):
        if not e.exprs:
            return k()
        if len(e.exprs) == 1:
            return _gen(e.exprs[0], table, overrides, k)
        head, rest = e.exprs[0], SSeq(e.exprs[1:])
        return _gen(SLet("_", head, rest), table, overrides, k)

    if isinstance(e, SBinOp):
        def after_left():
            def after_right():
                return [Stage("pure_step", "pure_step",
                              comment=f"binop {e.op}")] + k()
            return _gen(e.right, table, overrides, after_right)
        return _gen(e.left, table, overrides, after_left)

    if isinstance(e, SApp):
        if e.func not in table:
            raise IrisGenError(f"call to unknown function '{e.func}': "
                               f"not in the function table")
        _check_anf_args(e)
        entry = table[e.func]
        if isinstance(entry, OpaqueSpec):
            ov = overrides.get(e.func)
            if ov is not None:
                st = Stage(f"call_opaque_pre ({ov})", "call_opaque",
                           comment=f"{e.func} (pre via SMT axiom)",
                           smt_relevant=True)
            else:
                st = Stage(f'call_opaque "{e.func}"', "call_opaque",
                           comment=f"opaque, pre: "
                                   f"{entry.side or 'arity/typing'}",
                           smt_relevant=entry.side is not None)
            return [st] + k()
        # Transparent: the unfolded body's stages follow, then the
        # continuation resumes.
        st = Stage(f'call_transparent "{e.func}"', "call_transparent",
                   comment="unfolds")
        return [st] + _gen(entry.body, table, overrides, k)

    if isinstance(e, SLet):
        def after_rhs():
            return [Stage("pure_step", "pure_step",
                          comment=f'bind "{e.var}"')] + \
                   _gen(e.body, table, overrides, k)
        return _gen(e.value, table, overrides, after_rhs)

    if isinstance(e, SWhile):
        # Concrete-state loop: emit a bounded repeat of one full
        # iteration block (loop_unfold + condition + select-true + body
        # + bind "_"), then the explicit exit iteration.  Each repeat
        # iteration is atomic (Ltac backtracking): on the exit pass the
        # block fails partway and rolls back, leaving the goal at the
        # exit unfolding.  Loops over symbolic state fail the first
        # block (pure_step refuses symbolic conditions), so the repeat
        # exits with zero unrollings and the failure lands at the exit
        # stages -- classifiable, no divergence.
        cond_stages = _gen(e.cond, table, overrides, lambda: [])
        body_stages = _gen(e.body, table, overrides, lambda: [])

        def flat(nodes: list[StageNode], what: str) -> list[str]:
            out = []
            for n in nodes:
                if isinstance(n, Branch):
                    raise IrisGenError(
                        f"while {what} contains a case split; loops with "
                        f"internal branching need the invariant path "
                        f"(later phase)")
                out.append(n.tactic)
            return out

        iter_block = "; ".join(
            ["loop_unfold"] + flat(cond_stages, "condition")
            + ["pure_step"] + flat(body_stages, "body") + ["pure_step"])
        return ([Stage(f"repeat ({iter_block})", "loop_iterations",
                       comment="concrete loop: all full iterations")]
                + [Stage("loop_unfold", "loop_unfold",
                         comment="exit iteration")]
                + cond_stages
                + [Stage("pure_step", "pure_step", comment="exit branch")]
                ) + k()

    if isinstance(e, SAlloc):
        return [Stage("heap_alloc", "heap_alloc",
                      comment="fresh location"),
                ] + k()

    if isinstance(e, SStore):
        return [Stage("heap_store", "heap_store",
                      comment=f"write {e.loc}"),
                ] + k()

    if isinstance(e, SLoad):
        return [Stage("heap_load", "heap_load",
                      comment=f"read {e.loc}"),
                ] + k()

    if isinstance(e, SIf):
        if isinstance(e.cond, SLit) and e.cond.lit_type == "bool":
            chosen = (e.then_branch if e.cond.value.lower() == "true"
                      else e.else_branch)
            return ([Stage("pure_step", "pure_step",
                           comment="literal conditional")] +
                    _gen(chosen, table, overrides, k))

        def after_cond():
            then_arm = ([Stage("pure_step", "pure_step",
                               comment="select then-branch")] +
                        _gen(e.then_branch, table, overrides, k))
            else_arm = ([Stage("pure_step", "pure_step",
                               comment="select else-branch")] +
                        _gen(e.else_branch, table, overrides, k))
            return [Stage("case_bool", "case_bool", comment="path fork"),
                    Branch([then_arm, else_arm])]
        return _gen(e.cond, table, overrides, after_cond)

    raise IrisGenError(
        f"unsupported node for staged generation: {type(e).__name__} "
        f"(phase 3: heap/exceptions/loops)")


def _emit_stage_lines(nodes: list[StageNode], depth: int,
                      indent: str) -> list[str]:
    lines: list[str] = []
    for n in nodes:
        if isinstance(n, Stage):
            text = f"{indent}{n.tactic}."
            if n.comment:
                text += f"  (* {n.comment} *)"
            lines.append(text)
        else:
            if depth >= len(_BULLETS):
                raise IrisGenError("case split nesting exceeds bullet depth")
            bullet = _BULLETS[depth]
            for arm in n.arms:
                arm_lines = _emit_stage_lines(arm, depth + 1, indent + "  ")
                first = arm_lines[0].lstrip()
                lines.append(f"{indent}{bullet} {first}")
                lines.extend(arm_lines[1:])
    return lines


# -- Top-level ------------------------------------------------------------

_HEADER = (
    "(* Generated by iris_proof_gen -- staged Iris proof. *)\n"
    "From Stdlib Require Import Uint63Axioms Floats.PrimFloat.\n"
    "From iris.proofmode Require Import proofmode.\n"
    "From iris.program_logic Require Import weakestpre lifting.\n"
    "Require Import SnakeletLang SnakeletWp SnakeletTactics RegMatch.\n"
    "Open Scope Z_scope.\n"
)


@dataclass
class IrisProof:
    """A complete staged proof artifact for one function."""
    name: str
    body_coq: str
    post: str
    params: list[str]
    pre: Optional[str]
    axioms: list[str]
    table_coq: str
    stages: list[StageNode]

    def stage_list(self) -> list[Stage]:
        """Flattened stages (for trace/cache consumers)."""
        out: list[Stage] = []

        def walk(nodes: list[StageNode]) -> None:
            for n in nodes:
                if isinstance(n, Stage):
                    out.append(n)
                else:
                    for arm in n.arms:
                        walk(arm)
        walk(self.stages)
        return out

    def emit(self) -> str:
        parts = [_HEADER]
        for i, ax in enumerate(self.axioms):
            parts.append(f"Axiom smt_ax_{i} : {ax}.")
        if self.axioms:
            parts.append("")
        parts.append(self.table_coq)
        parts.append("")
        parts.append("Section generated_proofs.")
        parts.append("  Context `{!snakelet_heapGS_gen hlc Sg}.")
        parts.append("")
        binders = "".join(f" ({p} : Z)" for p in self.params)
        parts.append(f"  Lemma {self.name}_correct s E{binders} :")
        if self.pre:
            parts.append(f"    ({self.pre}) ->")
        # %Z: inside the WP pure bracket, +/* would otherwise resolve in
        # type_scope (sum/prod) rather than Z_scope.
        parts.append(f"    {TSTILE} WP {self.body_coq} @ s; E "
                     f"{{{{ v, {LCEIL}({self.post})%Z{RCEIL} }}}}.")
        parts.append("  Proof.")
        if self.pre:
            parts.append("    intros Hpre.")
        parts.append("    iStartProof.")
        parts.extend(_emit_stage_lines(self.stages, 0, "    "))
        parts.append("  Qed.")
        parts.append("End generated_proofs.")
        return "\n".join(parts) + "\n"


def generate(name: str,
             body: SExpr,
             post: str,
             table: FunTable,
             params: Optional[list[str]] = None,
             pre: Optional[str] = None,
             axioms: Optional[list[str]] = None,
             pre_overrides: Optional[dict[str, str]] = None) -> IrisProof:
    """Generate a staged Iris proof for a SnakeletIR body.

    name: function name (theorem is <name>_correct).
    body: SnakeletIR expression; theorem parameters appear as
          SLit("int", "<param>") so they print as (Val (LitInt p)).
    post: Coq Prop over the result variable `v` (and theorem params).
    table: callee table; determines call_opaque vs call_transparent.
    params: theorem-level integer parameters.
    pre: optional Coq Prop premise (available to lia in pre obligations).
    axioms: SMT-discharged facts, emitted as Axiom smt_ax_<i>.
    pre_overrides: per-callee precondition discharge tactics referencing
                   the axioms (the SMT escalation slot).
    """
    overrides = pre_overrides or {}
    stages = _gen(body, table, overrides,
                  lambda: [Stage("finish_pure", "finish_pure",
                                 comment="postcondition")])
    return IrisProof(
        name=name,
        body_coq=body.to_coq(),
        post=post,
        params=params or [],
        pre=pre,
        axioms=axioms or [],
        table_coq=_emit_table_section(table),
        stages=stages,
    )
