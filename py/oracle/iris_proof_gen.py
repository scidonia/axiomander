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


@dataclass
class WhileInv:
    """Symbolic while-loop with an invariant (iLöb + per-loop lemma).

    Contains enough information to generate a per-loop Coq lemma using
    the proven iLöb-forall(z) pattern, and a call-site stage using
    reshape_expr + wp_bind + lemma application.
    """
    lemma_name: str            # e.g. loop_inv_foo_0
    cell_name: str             # e.g. "c" (IR variable name)
    bound_expr: str            # Coq expression for the bound (e.g. "LitInt n" or "n")
    cond_coq: str              # Coq While condition expression
    body_coq: str              # Coq While body expression
    invariants: list[str]      # Coq Props (from contract asserts)
    order_hint: str = ""       # "ascending" or "descending"


StageNode = Union[Stage, Branch, WhileInv]

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


def _unroll_count(cond: SExpr) -> Optional[int]:
    """If the condition is [ivar < lit_N] with a literal right operand,
    return N (the number of true iterations before exit)."""
    if isinstance(cond, SBinOp) and cond.op in ("lt", "le"):
        if isinstance(cond.right, SLit) and cond.right.lit_type == "int":
            try:
                return int(cond.right.value)
            except (ValueError, TypeError):
                pass
    return None


def _extract_while_cell(cond: SExpr) -> str:
    """Extract the cell name from a while condition like load(c) < N."""
    if isinstance(cond, SBinOp) and isinstance(cond.left, SLoad):
        return cond.left.loc
    return "c"


def _extract_while_bound(cond: SExpr) -> str:
    """Extract the bound expression from a while condition like load(c) < N."""
    if isinstance(cond, SBinOp):
        right = cond.right
        if isinstance(right, SLit) and right.lit_type == "int":
            return f"LitInt {right.value}"
        elif isinstance(right, SVar):
            return right.name
        elif isinstance(right, SLit):
            return f"LitInt {right.value}"
        return right.to_coq()
    return "n"


def _gen(e: SExpr, table: FunTable, overrides: dict[str, str],
         k, func_name: str = "", _inv_counter: list[int] | None = None) -> list[StageNode]:
    """Generate stages reducing e to a value, then continue with k().

    k is a thunk producing the continuation stages; it is invoked once
    per execution path (duplicated into each arm of a case split).
    """
    if isinstance(e, (SLit, SVar)):
        return k()

    if isinstance(e, SReturn):
        return _gen(e.value, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter)

    if isinstance(e, SSeq):
        if not e.exprs:
            return k()
        if len(e.exprs) == 1:
            return _gen(e.exprs[0], table, overrides, k, func_name=func_name, _inv_counter=_inv_counter)
        head, rest = e.exprs[0], SSeq(e.exprs[1:])
        return _gen(SLet("_", head, rest), table, overrides, k,
                     func_name=func_name, _inv_counter=_inv_counter)

    if isinstance(e, SBinOp):
        def after_left():
            def after_right():
                return [Stage("pure_step", "pure_step",
                              comment=f"binop {e.op}")] + k()
            return _gen(e.right, table, overrides, after_right, func_name=func_name, _inv_counter=_inv_counter)
        return _gen(e.left, table, overrides, after_left, func_name=func_name, _inv_counter=_inv_counter)

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
        return [st] + _gen(entry.body, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter)

    if isinstance(e, SLet):
        def after_rhs():
            return [Stage("pure_step", "pure_step",
                          comment=f'bind "{e.var}"')] + \
                   _gen(e.body, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter)
        return _gen(e.value, table, overrides, after_rhs, func_name=func_name, _inv_counter=_inv_counter)

    if isinstance(e, SWhile):
        cond_stages = _gen(e.cond, table, overrides, lambda: [], func_name=func_name, _inv_counter=_inv_counter)
        body_stages = _gen(e.body, table, overrides, lambda: [], func_name=func_name, _inv_counter=_inv_counter)

        # Symbolic loop with invariants: generate the per-loop lemma.
        if e.invariants:
            cell_name = _extract_while_cell(e.cond)
            bound_expr = _extract_while_bound(e.cond)
            cond_coq = e.cond.to_coq()
            body_coq = e.body.to_coq()
            if _inv_counter is not None:
                cid = _inv_counter[0]
                _inv_counter[0] += 1
            else:
                cid = 0
            lemma_name = f"loop_inv_{func_name}_{cid}"
            return [WhileInv(
                lemma_name=lemma_name,
                cell_name=cell_name,
                bound_expr=bound_expr,
                cond_coq=cond_coq,
                body_coq=body_coq,
                invariants=e.invariants,
            )]  # continuation handled by inferred Phi -- no k()

        def flat(nodes: list[StageNode], what: str) -> list[str]:
            out = []
            for n in nodes:
                if isinstance(n, Branch):
                    raise IrisGenError(
                        f"while {what} contains a case split; loops with "
                        f"internal branching need the invariant path "
                        f"(later phase)")
                if isinstance(n, Stage):
                    out.append(n.tactic)
            return out

        def has_heap(nodes):
            for n in nodes:
                if isinstance(n, Stage) and (
                        "heap_" in n.category or "heap_" in n.tactic):
                    return True
            return False

        cond_heap = has_heap(cond_stages)
        body_heap = has_heap(body_stages)

        if cond_heap or body_heap:
            iter_block = "; ".join(
                ["loop_unfold"] + flat(cond_stages, "condition")
                + ["pure_step"] + flat(body_stages, "body") + ["pure_step"])
            return ([Stage(f"repeat ({iter_block})", "loop_iterations",
                           comment="concrete heap loop: all full iterations")]
                    + [Stage("loop_unfold", "loop_unfold",
                             comment="exit iteration")]
                    + cond_stages
                    + [Stage("pure_step", "pure_step", comment="exit branch")]
                    ) + k()
        else:
            # Pure loop with a literal bound: unroll N times.
            unroll = _unroll_count(e.cond)
            if unroll is not None and unroll > 0:
                block = flat(body_stages, "body")
                stages = []
                for _ in range(unroll):
                    stages += [
                        Stage("loop_unfold", "loop_unfold",
                              comment="iteration"),
                        ] + cond_stages + [
                        Stage("pure_step", "pure_step",
                              comment="enter body"),
                        ] + [Stage(t, "pure_step", comment="body")
                             for t in block] + [
                        Stage("pure_step", "pure_step",
                              comment="step ;;"),
                        ]
                return stages + [
                    Stage("loop_unfold", "loop_unfold",
                          comment="exit iteration"),
                    ] + cond_stages + [
                    Stage("pure_step", "pure_step",
                          comment="exit branch"),
                    ] + k()
            # Symbolic pure loop or mutable symbolic loop: needs
            # ghost-state invariant (iLöb over a Coq-variable measure).
            # Falls through to IMP for now.
            raise IrisGenError(
                "symbolic while loop: needs Löb+invariant (phase 5)")

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
                    _gen(chosen, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter))

        def after_cond():
            then_arm = ([Stage("pure_step", "pure_step",
                               comment="select then-branch")] +
                        _gen(e.then_branch, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter))
            else_arm = ([Stage("pure_step", "pure_step",
                               comment="select else-branch")] +
                        _gen(e.else_branch, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter))
            return [Stage("case_bool", "case_bool", comment="path fork"),
                    Branch([then_arm, else_arm])]
        return _gen(e.cond, table, overrides, after_cond, func_name=func_name, _inv_counter=_inv_counter)

    raise IrisGenError(
        f"unsupported node for staged generation: {type(e).__name__} "
        f"(phase 3: heap/exceptions/loops)")


def _emit_stage_lines(nodes: list[StageNode], depth: int,
                      indent: str, post: str = "") -> list[str]:
    lines: list[str] = []
    for n in nodes:
        if isinstance(n, Stage):
            text = f"{indent}{n.tactic}."
            if n.comment:
                text += f"  (* {n.comment} *)"
            lines.append(text)
        elif isinstance(n, Branch):
            if depth >= len(_BULLETS):
                raise IrisGenError("case split nesting exceeds bullet depth")
            bullet = _BULLETS[depth]
            for arm in n.arms:
                arm_lines = _emit_stage_lines(arm, depth + 1, indent + "  ", post)
                first = arm_lines[0].lstrip()
                lines.append(f"{indent}{bullet} {first}")
                lines.extend(arm_lines[1:])
        elif isinstance(n, WhileInv):
            lines.extend(_emit_while_inv_stage(n, indent, post))
    return lines


# -- Top-level ------------------------------------------------------------

def _emit_while_inv_stage(wi: WhileInv, indent: str, post: str = "") -> list[str]:
    bound = wi.bound_expr
    if bound.startswith("LitInt "):
        bound = bound.removeprefix("LitInt ")
    return [f"{indent}focus_while.",
            f"{indent}iApply ({wi.lemma_name} s E l {bound} 0%Z _",
            f"{indent}  with \"[$] [] []\").",
            f"{indent}{{ iPureIntro; lia. }}",
            f"{indent}{{ iIntros \"Hc_n\".",
            f"{indent}  rewrite /fill_K /=.",
            f"{indent}  iApply (@wp_let _ _ _ _ _ _ \"_\" LitUnit _ _).",
            f"{indent}  iNext. snakelet_simpl.",
            f"{indent}  heap_load. pure_step. finish_pure. }}"]





_HEADER = (
    "(* Generated by iris_proof_gen -- staged Iris proof. *)\n"
    "From iris.proofmode Require Import proofmode coq_tactics reduction.\n"
    "From iris.program_logic Require Import weakestpre.\n"
    "Require Import SnakeletLang SnakeletWp SnakeletTactics.\n"
    "Import snakelet_notation.\n"
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
    aux_lemmas: list[str] = field(default_factory=list)

    def stage_list(self) -> list[Stage]:
        """Flattened stages (for trace/cache consumers)."""
        out: list[Stage] = []

        def walk(nodes: list[StageNode]) -> None:
            for n in nodes:
                if isinstance(n, Stage):
                    out.append(n)
                elif isinstance(n, Branch):
                    for arm in n.arms:
                        walk(arm)
                # WhileInv carries auxiliary-lemma info, not a stage.
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
        parts.append("  Context `{!snakelet_heapGS_gen hlc Σ}.")
        parts.append("  Context `{FC : FunCtx}.")
        parts.append("")
        for lemma_text in self.aux_lemmas:
            parts.append(lemma_text)
            parts.append("")
        binders = "".join(f" ({p} : Z)" for p in self.params)
        parts.append(f"  Lemma {self.name}_correct s E{binders} :")
        if self.pre:
            parts.append(f"    ({self.pre}) ->")
        parts.append(f"    {TSTILE} WP {self.body_coq}%S @ s; E "
                     f"{{{{ v, {LCEIL}({self.post})%Z{RCEIL} }}}}.")
        parts.append("  Proof.")
        if self.pre:
            parts.append("    intros Hpre.")
        parts.append("    iStartProof.")
        parts.extend(_emit_stage_lines(self.stages, 0, "    ", self.post))
        parts.append("  Qed.")
        parts.append("End generated_proofs.")
        return "\n".join(parts) + "\n"

def _emit_while_inv_lemma(wi: WhileInv) -> str:
    """Generate a per-loop Coq lemma following the proven loop_inv_lemma pattern.

    Lemma <lemma_name> s E l bound (z : Z) (Φ : sn_val → iProp Σ) :
      ⊢ pointsto l (DfracOwn 1) (LitInt z) -∗ ⌜P_inv(z)⌝ -∗
         (pointsto l (DfracOwn 1) (LitInt bound) -∗ Φ LitUnit) -∗
         WP (While cond body) @ s; E {{ Φ }}.
    """
    import re
    # Post-process invariants: replace cell-value references with z.
    # The ContractLinter may produce either plain Var references like "c"
    # or string-encoded references like 'asZ (s "c" % string)'.
    cell_pat = re.escape(wi.cell_name)
    # Also replace the bound parameter reference (e.g. "n") with "bound".
    bound_pat = wi.bound_expr
    bound_name = None
    if bound_pat.startswith("LitInt "):
        # Extract the inner name: LitInt n -> n
        bound_name = bound_pat.removeprefix("LitInt ").strip()
    elif bound_pat.startswith("LitLoc "):
        pass  # location literal, no substitution needed
    else:
        bound_name = bound_pat  # bare variable
    invs = []
    for inv in wi.invariants:
        # Replace asZ (s "c" % string) -> z
        inv_subst = re.sub(
            r'asZ\s*\(\s*s\s+"' + cell_pat + r'"\s*%\s*string\s*\)',
            'z', inv)
        # Replace plain variable references to the cell name -> z
        inv_subst = re.sub(
            r'\b' + cell_pat + r'\b',
            'z', inv_subst)
        # Replace bound parameter references (e.g., "n") -> bound
        if bound_name:
            inv_subst = re.sub(
                r'\b' + re.escape(bound_name) + r'\b',
                'bound', inv_subst)
        invs.append(inv_subst)
    inv_parts = " /\\ ".join(invs) if invs else "True"
    inv_prop = f"{LCEIL}{inv_parts}{RCEIL}"
    # Replace cell variable references with the location l in cond/body,
    # and replace bound variable references with the lemma parameter "bound".
    cond_coq = re.sub(rf'\(Var "{re.escape(wi.cell_name)}"\)',
                      '(Val (LitLoc l))', wi.cond_coq)
    body_coq = re.sub(rf'\(Var "{re.escape(wi.cell_name)}"\)',
                      '(Val (LitLoc l))', wi.body_coq)
    if bound_name:
        cond_coq = cond_coq.replace(f'(LitInt {bound_name})',
                                    '(LitInt bound)')
        body_coq = body_coq.replace(f'(LitInt {bound_name})',
                                    '(LitInt bound)')
    return f"""  Lemma {wi.lemma_name} s E l (bound : Z) (z : Z)
      (Φ : sn_val → iProp Σ) :
    {TSTILE} pointsto l (DfracOwn 1) (LitInt z) -∗
       {inv_prop} -∗
       (pointsto l (DfracOwn 1) (LitInt bound) -∗ Φ LitUnit) -∗
       WP (While ({cond_coq}) ({body_coq})) @ s; E {{{{ Φ }}}}.
  Proof.
    iLöb as "IH" forall (z Φ).
    iIntros "Hc %Hz Hwand".
    loop_unfold.
    heap_load. pure_step.
    case_bool.
    - apply bool_decide_eq_true_1 in Hcond.
      pure_step.
      heap_load. pure_step. pure_step. cbn. pure_step. heap_store. pure_step.
      iApply ("IH" $! (z + 1)%Z Φ with "Hc [] Hwand").
      {{ iPureIntro. lia. }}
    - apply bool_decide_eq_false_1 in Hcond.
      assert (z = bound) by lia.
      subst z.
      iApply wp_if_false.
      iNext. iApply wp_value'.
      iApply "Hwand".
      iExact "Hc".
  Qed."""


def _collect_while_invs(stages: list[StageNode]) -> list[WhileInv]:
    """Walk the stage tree and collect all WhileInv nodes."""
    out: list[WhileInv] = []

    def walk(nodes: list[StageNode]) -> None:
        for n in nodes:
            if isinstance(n, WhileInv):
                out.append(n)
            elif isinstance(n, Branch):
                for arm in n.arms:
                    walk(arm)
    walk(stages)
    return out


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
    inv_counter = [0]
    stages = _gen(body, table, overrides,
                  lambda: [Stage("finish_pure", "finish_pure",
                                 comment="postcondition")],
                  func_name=name, _inv_counter=inv_counter)
    aux_lemmas = [_emit_while_inv_lemma(wi)
                  for wi in _collect_while_invs(stages)]
    return IrisProof(
        name=name,
        body_coq=body.to_coq(),
        post=post,
        params=params or [],
        pre=pre,
        axioms=axioms or [],
        table_coq=_emit_table_section(table),
        stages=stages,
        aux_lemmas=aux_lemmas,
    )
