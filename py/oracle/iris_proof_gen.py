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
    SAlloc, SApp, SBinOp, SDictGet, SDictSet, SExpr, SIf, SLet, SLit, SLoad, SRaise, SReturn, SSeq,
    SStore, STry, SVar, SWhile, SFor,
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
    pure_counter: bool = False  # True if counter is a local var (no heap)


@dataclass
class ForList:
    """For-each loop over a list value, proven via wp_for_list or wp_for_list_forall.

    For the no-accumulator case the suffix invariant is trivial (emp), so the
    proof is fully automatic: apply wp_for_list with P := emp, discharge the
    _-closedness side-goal, and run the body stages per element.
    When invariants are present, uses wp_for_list_forall with a Forall predicate."""
    var: str                   # loop variable name
    lst_coq: str               # Coq expression for the list value
    body_coq: str              # Coq body expression
    body_stages: list["StageNode"]  # stage tactics for one body execution
    invariants: list[str]      # Coq Props (suffix invariant); [] => emp
    continuation_stages: list["StageNode"]  # stages for code after the for-loop
    iterable_type: str = "list"  # "list" | "dict" — which wp_for_* lemma to use
    forall_predicate: str = ""  # sn_val->Prop predicate for wp_for_list_forall


def _make_forall_predicate(invariants: list[str], loop_var: str) -> str:
    """Convert body assert invariants to a Coq sn_val->Prop predicate.
    E.g. ['(x > 0)'] -> fun v => match v with LitInt n => n > 0 | _ => False end"""
    if not invariants:
        return ""
    # Extract comparison threshold from first invariant (heuristic)
    inv = invariants[0].strip()
    # Pattern: (x > N) or (x < N) etc
    import re
    m = re.match(r'\((\w+)\s*([><=!]+)\s*(\d+)\)', inv)
    if m:
        var, op, val = m.groups()
        op_map = {">": "n > 0", "<": "n < 0", ">=": "n >= 0", "<=": "n <= 0", "==": f"n = {val}", "!=": f"n <> {val}"}
        coq_op = op_map.get(op.strip(), f"n > {val}")
        # Boolean predicate for compute-ability: Z.ltb produces bool, = true makes it Prop
        bool_pred = f"(fun (_v : sn_val) => match _v with LitInt n => Z.ltb {val} n = true | _ => False end)"
        if op == ">" and val == "0":
            return bool_pred
        if op in (">=", "<=", "<", ">"):
            return bool_pred
        # Generic: Prop-based comparison
        return (f"(fun (_v : sn_val) => "
                f"match _v with LitInt n => {coq_op} | _ => False end)")
    # Fallback: generic
    return f"(fun (_ : sn_val) => True)"


StageNode = Union[Stage, Branch, WhileInv, ForList]

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
         k, func_name: str = "", _inv_counter: list[int] | None = None,
         list_params: dict[str, str] | None = None,
         dict_params: dict[str, str] | None = None) -> list[StageNode]:
    """Generate stages reducing e to a value, then continue with k().

    k is a thunk producing the continuation stages; it is invoked once
    per execution path (duplicated into each arm of a case split).
    """
    lp = list_params or {}
    dp = dict_params or {}
    if isinstance(e, (SLit, SVar)):
        return k()

    if isinstance(e, SReturn):
        return _gen(e.value, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

    if isinstance(e, SSeq):
        if not e.exprs:
            return k()
        if len(e.exprs) == 1:
            return _gen(e.exprs[0], table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)
        head, rest = e.exprs[0], SSeq(e.exprs[1:])
        return _gen(SLet("_", head, rest), table, overrides, k,
                     func_name=func_name, _inv_counter=_inv_counter, list_params=lp)

    if isinstance(e, SBinOp):
        def after_left():
            def after_right():
                return [Stage("pure_step", "pure_step",
                              comment=f"binop {e.op}")] + k()
            return _gen(e.right, table, overrides, after_right, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)
        return _gen(e.left, table, overrides, after_left, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

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
        return [st] + _gen(entry.body, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

    if isinstance(e, SLet):
        def after_rhs():
            return [Stage("pure_step", "pure_step",
                          comment=f'bind "{e.var}"')] + \
                   _gen(e.body, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)
        return _gen(e.value, table, overrides, after_rhs, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

    if isinstance(e, SWhile):
        cond_stages = _gen(e.cond, table, overrides, lambda: [], func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)
        body_stages = _gen(e.body, table, overrides, lambda: [], func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

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

    if isinstance(e, SFor):
        # for x in xs: body  ->  wp_for_list fold.  Generate the body's stage
        # script for one iteration; the suffix invariant defaults to emp when
        # the loop has no accumulator contract.
        cont = k()
        body_stages = _gen(e.body, table, overrides, lambda: [],
                           func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)
        # wp_for_list takes the list MODEL (list sn_val), not the wrapped
        # value.  For a list literal, strip the LitList wrapper.  For a
        # list-typed parameter, use the model variable from list_params.
        if isinstance(e.lst, SLit) and e.lst.lit_type == "list":
            model_coq = e.lst.to_coq_val()  # (LitList (... :: nil))
            # strip outer "(LitList " ... ")"
            inner = model_coq.strip()
            if inner.startswith("(LitList ") and inner.endswith(")"):
                model_coq = inner[len("(LitList "):-1].strip()
            iterable_type = "list"
        elif isinstance(e.lst, SLit) and e.lst.lit_type == "dict":
            model_coq = e.lst.to_coq_val()  # (LitDict ((k,v) :: ... nil))
            inner = model_coq.strip()
            if inner.startswith("(LitDict ") and inner.endswith(")"):
                model_coq = inner[len("(LitDict "):-1].strip()
            iterable_type = "dict"
        elif isinstance(e.lst, SLit) and e.lst.lit_type == "val":
            param_name = e.lst.value
            if e.iterable_type == "dict":
                model_coq = dp.get(param_name, f"kvs_{param_name}")
            else:
                model_coq = lp.get(param_name, f"M_{param_name}")
            iterable_type = e.iterable_type
        else:
            # variable / parameter holding a list value: not yet supported
            raise IrisGenError(
                "for-loop over a non-literal list: needs a list contract "
                "(is_list) to expose the model. See "
                "docs/finite-iterable-relations.md.")
        return [ForList(
            var=e.var,
            lst_coq=model_coq,
            body_coq=e.body.to_coq(),
            body_stages=body_stages,
            invariants=e.invariants,
            continuation_stages=cont,
            iterable_type=iterable_type,
            forall_predicate=_make_forall_predicate(e.invariants, e.var),
        )]  # continuation handled by inferred Phi via wp_for_list' or wp_for_list_forall

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
                    _gen(chosen, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp))

        def after_cond():
            then_arm = ([Stage("pure_step", "pure_step",
                                comment="select then-branch")] +
                        _gen(e.then_branch, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp))
            else_arm = ([Stage("pure_step", "pure_step",
                                comment="select else-branch")] +
                        _gen(e.else_branch, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp))
            return [Stage("case_bool", "case_bool", comment="path fork"),
                    Branch([then_arm, else_arm])]
        return _gen(e.cond, table, overrides, after_cond, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

    if isinstance(e, SDictGet):
        def after_key():
            return [Stage("pure_step", "pure_step",
                          comment=f"dict lookup {e.loc}[key]")] + k()
        return _gen(e.key, table, overrides, after_key, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

    if isinstance(e, SDictSet):
        def after_dictset_key():
            def after_dictset_value():
                return [Stage("pure_step", "pure_step",
                              comment=f"dict insert {e.loc}[key]=val"),
                        Stage("pure_step", "pure_step",
                              comment="dict set: unit return")] + k()
            return _gen(e.value, table, overrides, after_dictset_value, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)
        return _gen(e.key, table, overrides, after_dictset_key, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

    if isinstance(e, SRaise):
        def after_exc():
            return [Stage("pure_step", "pure_step",
                          comment="raise exception")] + k()
        return _gen(e.exc, table, overrides, after_exc, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp)

    if isinstance(e, STry):
        # ANF ensures the body is an atom (value or variable), so after
        # substitution/sub-reduction it becomes Try (Val v) handler.
        # pure_step_redex handles Try (Val _) _ via wp_try_val.
        return [Stage("pure_step", "pure_step",
                       comment="try/except: body returned normally")] + k()

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
        elif isinstance(n, ForList):
            lines.extend(_emit_for_list_stage(n, indent))
    return lines


# -- Top-level ------------------------------------------------------------

def _emit_for_list_stage(fl: ForList, indent: str) -> list[str]:
    """Emit a wp_for_list' or wp_for_list_forall application for a for-loop.

    Focuses the For under any trailing continuation, applies the appropriate
    WP lemma with trivial invariant (emp) and inferred Phi.  The no-accumulator
    body runs per element; the final continuation runs after the loop.
    When invariants are present, uses wp_for_list_forall with a Forall predicate."""

    if fl.forall_predicate:
        # Forall-accumulating variant: uses wp_for_list_forall
        q_pred = fl.forall_predicate
        lemma = "wp_for_list_forall"
        inv_arg = f"{q_pred}"
        lines = [
            f"{indent}focus_for.",
            f"{indent}iApply ({lemma} {q_pred} s E \"{fl.var}\" ({fl.body_coq})",
            f"{indent}  ({fl.lst_coq}) _).",
            f"{indent}{{ intros w; reflexivity. }}",
            f"{indent}{{ (* Forall premise *) iPureIntro. simpl. repeat (try constructor; try lia). }}",
            f"{indent}{{ (* per-element body step *)",
            f"{indent}  iModIntro. iIntros (vfor vrest) \"Hinv\".",
            f"{indent}  iDestruct \"Hinv\" as %Hfor.",
            f"{indent}  inversion Hfor as [|? ? Hq Hvs]; subst.",
            f"{indent}  simpl.",
        ]
        body_lines = _emit_stage_lines(fl.body_stages, 0, indent + "  ")
        lines.extend(body_lines)
        lines.append(f"{indent}  (* forall step: close body, pass Hvs to postcondition *)")
        lines.append(f"{indent}  iApply wp_value'. iPureIntro. exact Hvs.")
        lines.append(f"{indent}}}")
        lines.append(f"{indent}{{ (* post-loop continuation *) iIntros \"_\". ")
        lines.append(f"{indent}  rewrite /fill_K /=.")
        lines.append(f"{indent}  unfold of_val.")
        cont_lines = _emit_stage_lines(fl.continuation_stages, 0, indent + "  ")
        lines.extend(cont_lines)
        lines.append(f"{indent}}}")
        return lines

    if fl.iterable_type == "dict":
        lemma = "wp_for_dict_keys'"
        inv_type = "⌜True⌝%I"
        vars_intro = 'iModIntro. iIntros (vfor vval vrest) "_".'
    else:
        lemma = "wp_for_list'"
        inv_type = "⌜True⌝%I"
        vars_intro = 'iModIntro. iIntros (vfor vrest) "_".'
    lines = [
        f"{indent}focus_for.",
        f"{indent}iApply ({lemma} s E \"{fl.var}\" ({fl.body_coq})",
        f"{indent}  ({fl.lst_coq}) (fun _ => {inv_type}) _).",
        f"{indent}{{ intros w; reflexivity. }}",
        f"{indent}{{ (* invariant at full list *) done. }}",
        f"{indent}{{ (* per-element body step *)",
        f"{indent}  {vars_intro}",
        f"{indent}  simpl.",
    ]
    body_lines = _emit_stage_lines(fl.body_stages, 0, indent + "  ")
    lines.extend(body_lines)
    lines.append(f"{indent}  finish_pure.")
    lines.append(f"{indent}}}")
    lines.append(f"{indent}(* post-loop continuation *)")
    lines.append(f"{indent}{{ iIntros \"_\".")
    lines.append(f"{indent}  rewrite /fill_K /=.")
    lines.append(f"{indent}  unfold of_val.")
    cont_lines = _emit_stage_lines(fl.continuation_stages, 0, indent + "  ")
    lines.extend(cont_lines)
    lines.append(f"{indent}}}")
    return lines


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

_HEADER_EXN = (
    "(* Generated by iris_proof_gen -- staged Iris proof (exception backend). *)\n"
    "From iris.proofmode Require Import proofmode coq_tactics reduction.\n"
    "From iris.base_logic.lib Require Import gen_heap.\n"
    "Require Import SnakeletExnLang SnakeletExnWp SnakeletExnTactics.\n"
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
    list_params: dict[str, str] = field(default_factory=dict)
    dict_params: dict[str, str] = field(default_factory=dict)

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
                elif isinstance(n, ForList):
                    walk(n.body_stages)
                    walk(n.continuation_stages)
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
        parts.append("")
        for lemma_text in self.aux_lemmas:
            parts.append(lemma_text)
            parts.append("")
        binders = "".join(f" ({p} : Z)" for p in self.params
                           if p not in self.list_params and p not in self.dict_params)
        for lp, mv in self.list_params.items():
            binders += f" ({lp} : sn_val) ({mv} : list sn_val)"
        for dp, kv in self.dict_params.items():
            binders += f" ({dp} : sn_val) ({kv} : list (sn_val * sn_val))"
        parts.append(f"  Lemma {self.name}_correct s E{binders} :")
        premises: list[str] = []
        if self.list_params:
            premises.extend(
                f"{lp} = LitList {mv}" for lp, mv in self.list_params.items())
        if self.dict_params:
            premises.extend(
                f"{dp} = LitDict {kv}" for dp, kv in self.dict_params.items())
        if premises:
            pre_terms = " -> ".join(premises)
            parts.append(f"    ({pre_terms}) ->")
        if self.pre:
            parts.append(f"    ({self.pre}) ->")
        parts.append(f"    {TSTILE} WP {self.body_coq}%S @ s; E "
                     f"{{{{ v, {LCEIL}({self.post})%Z{RCEIL} }}}}.")
        parts.append("  Proof.")
        for lp, _ in self.list_params.items():
            parts.append(f"    intros H_{lp}.")
            parts.append(f"    subst {lp}.")
        for dp, _ in self.dict_params.items():
            parts.append(f"    intros H_{dp}.")
            parts.append(f"    subst {dp}.")
        if self.pre:
            parts.append("    intros Hpre.")
        parts.append("    iStartProof.")
        parts.extend(_emit_stage_lines(self.stages, 0, "    ", self.post))
        parts.append("  Qed.")
        parts.append("End generated_proofs.")
        return "\n".join(parts) + "\n"

    def emit_exn(self) -> str:
        """Emit a staged proof against the exception-aware backend
        (SnakeletExn*, Result-postcondition WP).

        Differences from emit():
        - header imports SnakeletExn* (no weakestpre / notation)
        - heap context class snakeletExn_heapGS_gen
        - no stuckness/mask params (s, E dropped)
        - WPE goal with a Result-match postcondition:
              fun r => match r with
                       | RVal v => <post>
                       | RExn lbl pay => <raises arm, default False>
                       end
        """
        parts = [_HEADER_EXN]
        for i, ax in enumerate(self.axioms):
            parts.append(f"Axiom smt_ax_{i} : {ax}.")
        if self.axioms:
            parts.append("")
        parts.append(self.table_coq)
        parts.append("")
        parts.append("Section generated_proofs.")
        parts.append("  Context `{!snakeletExn_heapGS_gen hlc Sigma}.")
        parts.append("  Local Notation \"'WPE' e {{ Q } }\" := (wp_exn e Q)")
        parts.append("    (at level 20, e, Q at level 200) : bi_scope.")
        parts.append("")
        binders = "".join(f" ({p} : Z)" for p in self.params
                           if p not in self.list_params and p not in self.dict_params)
        parts.append(f"  Lemma {self.name}_correct{binders} :")
        if self.pre:
            parts.append(f"    ({self.pre}) ->")
        # Result-match postcondition.
        post_match = (
            f"(fun r => match r with "
            f"RVal v => {LCEIL}({self.post})%Z{RCEIL} | "
            f"RExn _ _ => False end)%I"
        )
        parts.append(f"    {TSTILE} WPE {self.body_coq} "
                     f"{{{{ {post_match} }}}}.")
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
            elif isinstance(n, ForList):
                walk(n.body_stages)
                walk(n.continuation_stages)
    walk(stages)
    return out


def generate(name: str,
             body: SExpr,
             post: str,
             table: FunTable,
             params: Optional[list[str]] = None,
             pre: Optional[str] = None,
             axioms: Optional[list[str]] = None,
             pre_overrides: Optional[dict[str, str]] = None,
             list_params: Optional[dict[str, str]] = None,
             dict_params: Optional[dict[str, str]] = None) -> IrisProof:
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
                  func_name=name, _inv_counter=inv_counter,
                  list_params=list_params or {},
                  dict_params=dict_params or {})
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
        list_params=list_params or {},
        dict_params=dict_params or {},
    )
