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
(SnakeletExnTactics.v), which extract everything from the goal at proof
time.  Consequently the generator needs no symbolic execution and no
knowledge of intermediate values -- only the shape of the tree.

The sole backend is the exception-aware WP (Result postcondition,
SnakeletExn* Coq stack), emitted by IrisProof.emit_exn.

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

from axiomander.oracle.snakelet_ir import (
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
            result -- post is `r = LitInt (result)`.  Used when the callee
            returns a known function of its arguments.

    For NON-deterministic opaque operations whose guarantee is a PREDICATE
    on the result (not a function of the args) -- e.g. a DB op that returns
    0 or 1, with only `0 <= r <= 1` promised -- set [post_pred] and
    [post_witness] instead of relying on [result]:

    post_pred:    Coq Prop over the args and the result-as-Z [r_z].
                   E.g. "0 <= r_z /\\ r_z <= 1".  The emitted post becomes
                   `exists rz : Z, r = LitInt rz /\\ (post_pred)`.
    post_witness: Coq Z expression satisfying [post_pred], used to realize
                   the callee's totality promise (exists v, post v).  The
                   proof discharges `post_pred[r_z := witness]` by lia.

    ghost_vars: Mapping from observer function names to the Coq variable
                names they correspond to in [post_pred].  Contract
                expressions that reference the observer (e.g.
                `db_get_payment_state(order_id)` in an ensures clause) are
                resolved to these ghost variables, so the caller can name
                and reason about the opaque state the callee establishes.
                Example: {"db_get_payment_state": "payment_final"} means
                `post_pred` contains `payment_final = 2`, and any ensures
                referencing `db_get_payment_state(order_id)` compiles to
                `payment_final == 2` -- a real hypothesis the proof can use.

    ghost_wits: Z-expr witness values for each ghost variable in
                [ghost_vars], keyed by ghost variable name (not observer
                name).  Used in the callee's totality proof to provide
                concrete witnesses for the existential binders.  Defaults
                to "0" for any ghost var not listed.
    """
    args: list[str]
    side: Optional[str]
    result: str
    post_pred: Optional[str] = None
    post_witness: Optional[str] = None
    ghost_vars: dict[str, str] = field(default_factory=dict)
    ghost_wits: dict[str, str] = field(default_factory=dict)
    result_kind: str = "int"  # "int" | "string" — wraps result as LitInt or LitString


@dataclass
class TransparentDef:
    """A helper definition that unfolds at call sites."""
    params: list[str]
    body: SExpr


FunEntry = Union[OpaqueSpec, TransparentDef]
FunTable = dict[str, FunEntry]


# -- Iris built-in primitives (the equivalent of IMP's PURE_BUILTINS).
# These are transparent definitions for common Python operations that
# the Iris pipeline doesn't have native primitives for yet.
# Each is a simple Coq-level function body that computes the result.

IRIS_BUILTINS: FunTable = {
    # String operations
    "s.startswith": TransparentDef(
        params=["s", "p"],
        body=SBinOp(op="starts_with", left=SVar(name="s"),
                    right=SVar(name="p"))),
    "s.endswith": TransparentDef(
        params=["s", "p"],
        body=SBinOp(op="ends_with", left=SVar(name="s"),
                    right=SVar(name="p"))),
    "s.lower": TransparentDef(
        params=["s"],
        body=SBinOp(op="to_lower", left=SVar(name="s"),
                    right=SLit(lit_type="int", value="0"))),
    "s.upper": TransparentDef(
        params=["s"],
        body=SBinOp(op="to_upper", left=SVar(name="s"),
                    right=SLit(lit_type="int", value="0"))),
    # Dict get with default: if k in d then d[k] else default
    "d.get": TransparentDef(
        params=["d", "k", "default"],
        body=SLet(
            var="__has",
            value=SBinOp(op="in", left=SVar(name="d"),
                         right=SVar(name="k")),
            body=SIf(
                cond=SVar(name="__has"),
                then_branch=SBinOp(op="dict_get", left=SVar(name="d"),
                                   right=SVar(name="k")),
                else_branch=SVar(name="default"),
            ))),
    # Dict set d[k] = v: update a key-value pair via DictSetOp.
    # Uses TupleOp to construct the (k, v) pair as a LitTuple.
    "dict_set": TransparentDef(
        params=["d", "k", "v"],
        body=SLet(var="_kv",
                  value=SBinOp(op="tuple",
                               left=SVar(name="k"),
                               right=SVar(name="v")),
                  body=SBinOp(op="dict_set",
                              left=SVar(name="d"),
                              right=SVar(name="_kv")))),
    # Dict indexing d[k]: PARTIAL Python subscript semantics.  Branch on
    # membership (InOp -> dict_has_kvs): a hit projects via DictGetOp
    # (dict_lookup_kvs); a miss raises KeyError(k) -- the looked-up key IS
    # the exception payload (MkKeyErrOp builds LitExn "KeyError" k), exactly
    # like CPython.  This makes a wrong access observable as RExn, not a
    # silently-wrong value.
    "dict_index": TransparentDef(
        params=["d", "k"],
        body=SLet(
            var="__has",
            value=SBinOp(op="in", left=SVar(name="d"), right=SVar(name="k")),
            body=SIf(
                cond=SVar(name="__has"),
                then_branch=SBinOp(op="dict_get", left=SVar(name="d"),
                                   right=SVar(name="k")),
                else_branch=SRaise(
                    exc=SBinOp(op="mk_key_err", left=SVar(name="k"),
                               right=SVar(name="k")))))),
    # Pydantic model field access model.field: TOTAL structural projection.
    # Uses DictGetIntOp (returns LitInt, not stuck sn_val) so the int-type
    # postcondition existential [exists z, v = LitInt z /\ ...] unpacks by
    # reflexivity with [model_field_Z model "field"].  Object identity is
    # preserved (model is a single sn_val LitDict, never flattened).
    "field_access": TransparentDef(
        params=["model", "field"],
        body=SBinOp(op="dict_get_int", left=SVar(name="model"),
                    right=SVar(name="field"))),
}


# -- Global stage ID counter -----------------------------------------------
# Assigned by _mk_stage; reset per generate() call.

_STAGE_ID_COUNTER: list[int] = [0]


def _mk_stage(tactic: str, category: str, comment: str = "",
              smt_relevant: bool = False) -> Stage:
    _STAGE_ID_COUNTER[0] += 1
    return Stage(tactic=tactic, category=category, comment=comment,
                 smt_relevant=smt_relevant, stage_id=_STAGE_ID_COUNTER[0])

# -- Stage tree -----------------------------------------------------------

@dataclass
class Stage:
    """One staged tactic invocation with a unique ID for trace/capture."""
    tactic: str
    category: str
    comment: str = ""
    smt_relevant: bool = False
    stage_id: int = 0  # assigned by _gen via global counter


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
    cell_name: str             # e.g. "l_i" (IR variable name for counter cell)
    bound_expr: str            # Coq expression for the bound (e.g. "LitInt n" or "n")
    cond_coq: str              # Coq While condition expression
    body_coq: str              # Coq While body expression
    invariant_exprs: list = field(default_factory=list)
    """contract_ir.Expr nodes — primary storage for invariants.
    to_coq() gives the Coq Prop; to_smt() gives SMT-LIB.  Never parsed."""

    @property
    def invariants(self) -> list[str]:
        """Coq Prop strings, compiled lazily from invariant_exprs."""
        from axiomander.oracle.contract_ir_iris import iris_prop
        return [iris_prop(e) for e in self.invariant_exprs]

    body_stages: list["StageNode"] = field(default_factory=list)
    order_hint: str = ""
    pure_counter: bool = False
    extra_cells: list[str] = field(default_factory=list)
    """Additional heap cell variable names tracked through the loop."""
    inv_axiom_indices: list[int] = field(default_factory=list)
    """Axiom indices (smt_ax_N) for invariant update obligations."""


@dataclass
class WhileStr:
    """String-guard while loop, proven via the wp_while_str Hoare rule.

    Models [while load(c) == g: body] where the body STORES a non-[g] value
    to the guard cell [c], so the loop runs the body at most once (guard
    falsified).  No counter, no coinduction.

    The body obligation is emitted as a SEPARATE named lemma
    [<func>_body_spec_<id>] (proved standalone); the call site applies
    wp_while_str and discharges the body via [iApply <func>_body_spec_<id>].

    The path-dependent invariant [Inv s := (s = g \\/ s = final)] records
    that the guard cell is either the guard value (start) or [final] (after
    the body).  Combined with the guard-false exit it yields [s = final]."""
    lemma_name: str            # e.g. fulfil_body_spec_0
    guard_cell: str            # IR var name of the guard cell (e.g. "c_status")
    guard_value: str           # the guard string literal (e.g. "ready")
    final_value: str           # value the body stores to the guard cell (e.g. "fulfilled")
    cond_coq: str              # Coq While condition
    body_coq: str              # Coq While body
    body_stages: list["StageNode"]  # per-iteration proof stages
    other_cells: list[tuple[str, str, str]] = field(default_factory=list)
    """Other heap cells the body writes: (cell_var, pre_value, post_value)."""


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
    from_precondition: bool = False  # True if predicate comes from forallb precondition


def _make_forall_predicate(invariants: list[str], loop_var: str) -> str:
    """Convert body assert invariants to a Coq sn_val->Prop predicate.
    E.g. [(x > 0)] -> fun v => match v with LitInt n => Z.ltb 0 n = true | _ => False end
    Supports both contract_ir.Expr nodes and legacy Coq strings."""
    if not invariants:
        return ""
    inv = invariants[0]
    # New style: contract_ir.Expr AST nodes
    from axiomander.oracle.contract_ir import BinOp as CIBinOp, Var as CIVar, IntLit as CIIntLit
    if isinstance(inv, CIBinOp) and isinstance(inv.left, CIVar) and isinstance(inv.right, CIIntLit):
        op = inv.op
        rhs = inv.right.value
        if op == ">" and rhs == "0":
            return "(fun (_v : sn_val) => match _v with LitInt n => Z.ltb 0 n = true | _ => False end)"
        if op in (">=", "<=", "<", ">"):
            return f"(fun (_v : sn_val) => match _v with LitInt n => Z.ltb {rhs} n = true | _ => False end)"
        return f"(fun (_v : sn_val) => match _v with LitInt n => Z.leb {rhs} n = true | _ => False end)"
    # Legacy style: Coq string
    inv_str = inv.strip() if isinstance(inv, str) else ""
    import re
    m = re.match(r'\((\w+)\s*([><=!]+)\s*(\d+)\)', inv_str)
    if m:
        var, op, val = m.groups()
        op_map = {">": "n > 0", "<": "n < 0", ">=": "n >= 0", "<=": "n <= 0", "==": f"n = {val}", "!=": f"n <> {val}"}
        coq_op = op_map.get(op.strip(), f"n > {val}")
        bool_pred = f"(fun (_v : sn_val) => match _v with LitInt n => Z.ltb {val} n = true | _ => False end)"
        if op == ">" and val == "0":
            return bool_pred
        if op in (">=", "<=", "<", ">"):
            return bool_pred
        return (f"(fun (_v : sn_val) => "
                f"match _v with LitInt n => {coq_op} | _ => False end)")
    return f"(fun (_ : sn_val) => True)"


StageNode = Union[Stage, Branch, WhileInv, ForList, WhileStr]

_BULLETS = ["-", "+", "*", "--", "++", "**"]


# -- Table emission -------------------------------------------------------

def _emit_pre_def(name: str, spec: OpaqueSpec) -> str:
    binders = " ".join(f"({a} : Z)" for a in spec.args)
    args_list = "; ".join(f"LitInt {a}" for a in spec.args)
    body = f"args = [{args_list}]"
    if spec.side:
        body = f"{body} /\\ ({spec.side})"
    # Sanitize: dots in names (e.g. Order.status) → underscores (Order_status)
    safe = name.replace(".", "_")
    return (f"Definition {safe}_pre (args : list sn_val) : Prop :=\n"
            f"  exists {binders}, {body}.")


def _emit_post_def(name: str, spec: OpaqueSpec) -> str:
    args_pat = "; ".join(f"LitInt {a}" for a in spec.args)
    if spec.post_pred is not None:
        ghost_binders = " ".join(
            f"exists ({v} : Z)," for v in spec.ghost_vars.values())
        if spec.result_kind == "string":
            rhs = (f"exists r_s : string, r = LitString r_s /\\ "
                   f"({ghost_binders} ({spec.post_pred}))")
        else:
            rhs = (f"exists r_z : Z, r = LitInt r_z /\\ "
                   f"({ghost_binders} ({spec.post_pred}))")
    else:
        # Functional post: the result is a known expression of the args.
        rhs = f"r = LitInt ({spec.result})"
    safe = name.replace(".", "_")
    return (f"Definition {safe}_post (args : list sn_val) (r : sn_val) : Prop :=\n"
            f"  match args with\n"
            f"  | [{args_pat}] => {rhs}\n"
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
            safe_fname = fname.replace(".", "_")
            rhs = f"Some (FunSpec {safe_fname}_pre {safe_fname}_post)"
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
            if entry.post_pred is not None:
                wit = entry.post_witness if entry.post_witness is not None else "0"
                # Nested ghost-var existentials inside post_pred:
                #   exists r_z, v = LitInt r_z /\ (exists gv..., post_pred)
                # Witnesses: LitInt(wit) for v, wit for r_z, then ghost_wits
                # per nested binder, then reflexivity/lia for the conj.
                gh_exists = " ".join(
                    f"exists ({entry.ghost_wits.get(v, '0')}). "
                    for v in entry.ghost_vars.values())
                lines.append(
                    f"  {{ destruct Hpre as ({pat}). "
                    f"exists (LitInt ({wit})). exists ({wit}). "
                    f"split. {{ reflexivity. }} {{ {gh_exists}"
                    f"repeat split; lia. }} }}")
            else:
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


def _detect_string_guard(e: "SWhile") -> Optional[tuple[str, str]]:
    """Detect a string-guard loop: while load(c) == "literal": ...

    Returns (guard_cell, guard_value) if the condition is
    [SBinOp(op="eq", left=SLoad(c), right=SLit(string))], else None."""
    cond = e.cond
    if (isinstance(cond, SBinOp) and cond.op == "eq"
            and isinstance(cond.left, SLoad)
            and isinstance(cond.right, SLit)
            and cond.right.lit_type == "string"):
        return (cond.left.loc, cond.right.value)
    return None


def _collect_body_stores(e: SExpr) -> list[tuple[str, str]]:
    """Collect (cell, value) for every [store(cell, "literal")] in a loop body.

    Walks the SExpr tree (SSeq / SLet bodies) gathering SStore nodes whose
    value is a string literal.  Used to synthesise the guard cell's final
    value and the other-cell frame for wp_while_str."""
    out: list[tuple[str, str]] = []

    def walk(n: SExpr) -> None:
        if isinstance(n, SStore):
            if isinstance(n.value, SLit) and n.value.lit_type == "string":
                out.append((n.loc, n.value.value))
        if isinstance(n, SSeq):
            for x in n.exprs:
                walk(x)
        elif isinstance(n, SLet):
            walk(n.value)
            walk(n.body)
    walk(e)
    return out


def _gen(e: SExpr, table: FunTable, overrides: dict[str, str],
         k, func_name: str = "", _inv_counter: list[int] | None = None,
         list_params: dict[str, str] | None = None,
         dict_params: dict[str, str] | None = None,
         forall_predicates: dict[str, str] | None = None) -> list[StageNode]:
    """Generate stages reducing e to a value, then continue with k().

    k is a thunk producing the continuation stages; it is invoked once
    per execution path (duplicated into each arm of a case split).
    """
    lp = list_params or {}
    dp = dict_params or {}
    fp = forall_predicates or {}
    if isinstance(e, (SLit, SVar)):
        return k()

    if isinstance(e, SReturn):
        return _gen(e.value, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)

    if isinstance(e, SSeq):
        if not e.exprs:
            return k()
        if len(e.exprs) == 1:
            return _gen(e.exprs[0], table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)
        head, rest = e.exprs[0], SSeq(e.exprs[1:])
        return _gen(SLet("_", head, rest), table, overrides, k,
                     func_name=func_name, _inv_counter=_inv_counter, list_params=lp)

    if isinstance(e, SBinOp):
        def after_left():
            def after_right():
                return [_mk_stage("pure_step", "pure_step",
                              comment=f"binop {e.op}")] + k()
            return _gen(e.right, table, overrides, after_right, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)
        return _gen(e.left, table, overrides, after_left, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)

    if isinstance(e, SApp):
        if e.func not in table:
            raise IrisGenError(f"call to unknown function '{e.func}': "
                               f"not in the function table")
        _check_anf_args(e)
        entry = table[e.func]
        if isinstance(entry, OpaqueSpec):
            ov = overrides.get(e.func)
            if entry.post_pred is not None:
                # Predicate post: self-contained.
                st = _mk_stage(f'call_opaque_pred "{e.func}"', "call_opaque_pred",
                           comment=f"opaque, pre: "
                                   f"{entry.side or 'arity/typing'}",
                           smt_relevant=entry.side is not None)
                result = [st]
                # Ghost vars: nested inside Hr as existentials.  Emit a
                # destruct stage to bring them into scope, then split Hr
                # into the equality hypotheses (Hrz for the result, one
                # per ghost var).
                if entry.ghost_vars:
                    suf = f"_{e.func}"  # unique suffix per callee
                    gv_names = " & ".join(
                        f"{gv}{suf}" for gv in entry.ghost_vars.values())
                    gv_splits = "".join(
                        f"; destruct Hr as [Hrz{suf} H_{gv}{suf}]"
                        for gv in entry.ghost_vars.values())
                    result.append(_mk_stage(
                        f"destruct Hr as ({gv_names} & Hr)"
                        f"{gv_splits}",
                        "destruct_ghost",
                        comment=f"name ghost vars: {', '.join(entry.ghost_vars.values())}"
                                f" (suffix {suf})"))
                return result + k()
            elif ov is not None:
                st = _mk_stage(f"call_opaque_pre ({ov})", "call_opaque",
                           comment=f"{e.func} (pre via SMT axiom)",
                           smt_relevant=True)
            else:
                st = _mk_stage(f'call_opaque "{e.func}"', "call_opaque",
                           comment=f"opaque, pre: "
                                   f"{entry.side or 'arity/typing'}",
                           smt_relevant=entry.side is not None)
            return [st] + k()
        # Transparent: the unfolded body's stages follow, then the
        # continuation resumes.
        st = _mk_stage(f'call_transparent "{e.func}"', "call_transparent",
                   comment="unfolds")
        return [st] + _gen(entry.body, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)

    if isinstance(e, SLet):
        # A raise in the bound position unwinds the Let, discarding the
        # continuation: the exception propagates and terminates this path.
        if isinstance(e.value, SRaise):
            return [_mk_stage("raise_step", "raise_step",
                          comment="raise unwinds the let")]
        def after_rhs():
            return [_mk_stage("pure_step", "pure_step",
                          comment=f'bind "{e.var}"')] + \
                   _gen(e.body, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)
        return _gen(e.value, table, overrides, after_rhs, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)

    if isinstance(e, SWhile):
        cond_stages = _gen(e.cond, table, overrides, lambda: [], func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)
        body_stages = _gen(e.body, table, overrides, lambda: [], func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)

        # String-guard loop: while load(c) == "literal": ...; store(c, ...)
        # Terminates by falsifying the guard (wp_while_str), NOT a counter.
        guard = _detect_string_guard(e)
        if guard is not None:
            guard_cell, guard_value = guard
            stores = _collect_body_stores(e.body)
            # The guard cell's final value: the last store to it in the body.
            final_value = None
            for cell, val in stores:
                if cell == guard_cell:
                    final_value = val
            if final_value is None:
                raise IrisGenError(
                    f"string-guard while on '{guard_cell}' but the body never "
                    f"stores to it; cannot prove the guard is falsified")
            if final_value == guard_value:
                raise IrisGenError(
                    f"string-guard while on '{guard_cell}' stores the guard "
                    f"value '{guard_value}' back; loop would not terminate")
            # Other cells the body writes (cell, post_value); pre_value filled
            # from the alloc later via overrides if available.
            other = [(cell, "", val) for cell, val in stores
                     if cell != guard_cell]
            if _inv_counter is not None:
                cid = _inv_counter[0]
                _inv_counter[0] += 1
            else:
                cid = 0
            lemma_name = f"{func_name}_body_spec_{cid}"
            return [WhileStr(
                lemma_name=lemma_name,
                guard_cell=guard_cell,
                guard_value=guard_value,
                final_value=final_value,
                cond_coq=e.cond.to_coq(),
                body_coq=e.body.to_coq(),
                body_stages=body_stages,
                other_cells=other,
            )]

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
            extra_cells = _extract_extra_cells(body_coq, cell_name)
            return [WhileInv(
                lemma_name=lemma_name,
                cell_name=cell_name,
                bound_expr=bound_expr,
                cond_coq=cond_coq,
                body_coq=body_coq,
                invariant_exprs=list(e.invariants),
                body_stages=body_stages,
                extra_cells=extra_cells,
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
            # Concrete heap loop: only unroll if the bound is a literal
            unroll = _unroll_count(e.cond)
            if unroll is not None and unroll > 0:
                iter_block = "; ".join(
                    ["loop_unfold"] + flat(cond_stages, "condition")
                    + ["pure_step"] + flat(body_stages, "body") + ["pure_step"])
                return ([_mk_stage(f"repeat ({iter_block})", "loop_iterations",
                               comment="concrete heap loop: all full iterations")]
                        + [_mk_stage("loop_unfold", "loop_unfold",
                                 comment="exit iteration")]
                        + cond_stages
                        + [_mk_stage("pure_step", "pure_step", comment="exit branch")]
                        ) + k()
            # Symbolic heap loop: generate WhileInv with trivial invariant
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
                invariant_exprs=[],
                body_stages=body_stages,
                extra_cells=_extract_extra_cells(body_coq, cell_name),
            )]
        else:
            # Pure loop with a literal bound: unroll N times.
            unroll = _unroll_count(e.cond)
            if unroll is not None and unroll > 0:
                block = flat(body_stages, "body")
                stages = []
                for _ in range(unroll):
                    stages += [
                        _mk_stage("loop_unfold", "loop_unfold",
                              comment="iteration"),
                        ] + cond_stages + [
                        _mk_stage("pure_step", "pure_step",
                              comment="enter body"),
                        ] + [_mk_stage(t, "pure_step", comment="body")
                             for t in block] + [
                        _mk_stage("pure_step", "pure_step",
                              comment="step ;;"),
                        ]
                return stages + [
                    _mk_stage("loop_unfold", "loop_unfold",
                          comment="exit iteration"),
                    ] + cond_stages + [
                    _mk_stage("pure_step", "pure_step",
                          comment="exit branch"),
                    ] + k()
            # Symbolic loop without invariants: still generate a WhileInv
            # with the trivial invariant (z <= bound) for the heap-counter
            # pattern.  wp_while_inv handles this case.
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
                invariant_exprs=[],
                body_stages=body_stages,
                extra_cells=_extract_extra_cells(body_coq, cell_name),
            )]

    if isinstance(e, SFor):
        # for x in xs: body  ->  wp_for_list fold.  Generate the body's stage
        # script for one iteration; the suffix invariant defaults to emp when
        # the loop has no accumulator contract.
        cont = k()
        body_stages = _gen(e.body, table, overrides, lambda: [],
                           func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)
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
        from axiomander.oracle.contract_ir_iris import iris_prop
        # Prefer forall predicate from function precondition (forallb fact).
        inv_pred = _make_forall_predicate(e.invariants, e.var)
        pre_pred = fp.get(model_coq, "")
        return [ForList(
            var=e.var,
            lst_coq=model_coq,
            body_coq=e.body.to_coq(),
            body_stages=body_stages,
            invariants=[iris_prop(x) for x in e.invariants],
            continuation_stages=cont,
            iterable_type=iterable_type,
            forall_predicate=pre_pred or inv_pred,
            from_precondition=bool(pre_pred),
        )]  # continuation handled by inferred Phi via wp_for_list' or wp_for_list_forall

    if isinstance(e, SAlloc):
        return [_mk_stage("heap_alloc", "heap_alloc",
                      comment="fresh location"),
                ] + k()

    if isinstance(e, SStore):
        return [_mk_stage("heap_store", "heap_store",
                      comment=f"write {e.loc}"),
                ] + k()

    if isinstance(e, SLoad):
        return [_mk_stage("heap_load", "heap_load",
                      comment=f"read {e.loc}"),
                ] + k()

    if isinstance(e, SIf):
        if isinstance(e.cond, SLit) and e.cond.lit_type == "bool":
            chosen = (e.then_branch if e.cond.value.lower() == "true"
                      else e.else_branch)
            return ([_mk_stage("pure_step", "pure_step",
                            comment="literal conditional")] +
                    _gen(chosen, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp))

        def after_cond():
            then_arm = ([_mk_stage("pure_step", "pure_step",
                                comment="select then-branch")] +
                        _gen(e.then_branch, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp))
            else_arm = ([_mk_stage("pure_step", "pure_step",
                                comment="select else-branch")] +
                        _gen(e.else_branch, table, overrides, k, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp))
            return [_mk_stage("case_bool", "case_bool", comment="path fork"),
                    Branch([then_arm, else_arm])]
        return _gen(e.cond, table, overrides, after_cond, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)

    if isinstance(e, SDictGet):
        def after_key():
            return [_mk_stage("pure_step", "pure_step",
                          comment=f"dict lookup {e.loc}[key]")] + k()
        return _gen(e.key, table, overrides, after_key, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)

    if isinstance(e, SDictSet):
        def after_dictset_key():
            def after_dictset_value():
                return [_mk_stage("pure_step", "pure_step",
                              comment=f"dict insert {e.loc}[key]=val"),
                        _mk_stage("pure_step", "pure_step",
                              comment="dict set: unit return")] + k()
            return _gen(e.value, table, overrides, after_dictset_value, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)
        return _gen(e.key, table, overrides, after_dictset_key, func_name=func_name, _inv_counter=_inv_counter, list_params=lp, dict_params=dp, forall_predicates=fp)

    if isinstance(e, SRaise):
        # A raise terminates the path with an exception result; the
        # continuation k() is unreachable.
        return [_mk_stage("raise_step", "raise_step",
                      comment="raise exception (terminal)")]

    if isinstance(e, STry):
        # ANF ensures the body is an atom (value or variable), so after
        # substitution/sub-reduction it becomes Try (Val v) handler.
        # pure_step_redex handles Try (Val _) _ via wp_try_val.
        return [_mk_stage("pure_step", "pure_step",
                       comment="try/except: body returned normally")] + k()

    raise IrisGenError(
        f"unsupported node for staged generation: {type(e).__name__} "
        f"(phase 3: heap/exceptions/loops)")


def _emit_while_inv_lemma_exn(wi: WhileInv) -> str:
    """Generate a per-loop Coq lemma for a specific while-loop shape.

    Supports multiple heap cells (wi.extra_cells) for loops that modify
    several local variables.  The counter cell takes [z]/[bound]; other
    cells carry through with existential final values."""
    bound = wi.bound_expr
    if bound.startswith("LitInt "):
        bound_val = bound[len("LitInt "):].strip()
    else:
        bound_val = bound

    cell = wi.cell_name
    extra = wi.extra_cells or []

    # String-substitute cell variable names with Coq [Val (LitLoc l_...)]
    # in the condition and body.
    cond = wi.cond_coq.replace(f'(Var "{cell}")', f'(Val (LitLoc {cell}))')
    cond = cond.replace(f'(Val (LitInt {bound_val}))', '(Val (LitInt bound))')
    body = wi.body_coq.replace(f'(Var "{cell}")', f'(Val (LitLoc {cell}))')
    body = body.replace(f'(Val (LitInt {bound_val}))', '(Val (LitInt bound))')
    for ec in extra:
        cond = cond.replace(f'(Var "{ec}")', f'(Val (LitLoc {ec}))')
        body = body.replace(f'(Var "{ec}")', f'(Val (LitLoc {ec}))')

    body_lines = _emit_stage_lines(wi.body_stages, 0, "      ")
    body_proof = "\n".join(body_lines)

    # Cell parameter list: (l_counter : loc) (l_extra : loc) ...
    cell_params = f"({cell} : loc)"
    for ec in extra:
        cell_params += f" ({ec} : loc)"

    # Points-to premise: l_counter ↦ LitInt z ∗ l_extra ↦ LitInt a_extra ...
    pts_premise = f"{cell} ↦ LitInt z"
    extra_params = ""
    for i, ec in enumerate(extra):
        pts_premise += f" ∗ {ec} ↦ LitInt a_{i}"
        extra_params += f" (a_{i} : Z)"

    if extra:
        cont_premise = f"∀ {' '.join(f'a_{i}' for i in range(len(extra)))}, "
        cont_premise += f"{cell} ↦ LitInt bound"
        for i, ec in enumerate(extra):
            cont_premise += f" ∗ {ec} ↦ LitInt a_{i}"
        cont_premise += f" -∗ Phi (RVal LitUnit)"
    else:
        cont_premise = f"{cell} ↦ LitInt bound -∗ Phi (RVal LitUnit)"

    extra_ih_vars = (" " + " ".join(f"a_{i}" for i in range(len(extra)))) if extra else ""
    extra_ih_args = (" " + " ".join(["_"] * len(extra))) if extra else ""

    # -- Loop invariants: pure premises (only for promoted loops) --
    inv_names: list[str] = []
    inv_premises: list[str] = []
    # Only add invariant premises for promoted loops (cell == "l").
    # Old heap-counter loops use explicit ref/load/store and their
    # invariants reference the heap cell directly.
    is_promoted = (cell == "l")
    if is_promoted and wi.invariants:
        for j, inv in enumerate(wi.invariants):
            name = f"Hinv{j}"
            inv_names.append(name)
            inv_premises.append(f"⌜({inv})⌝ -∗")
    inv_premise_block = "    " + "\n    ".join(inv_premises) if inv_premises else ""

    if extra:
        extra_intro = " & ".join(["H" + cell] + ["H" + ec for ec in extra])
        pure_intros = " ".join(["%Hz"] + [f"%{n}" for n in inv_names])
        intro_pat = f'"({extra_intro}) {pure_intros} Hwand"'
    else:
        pure_intros = " ".join(["%Hz"] + [f"%{n}" for n in inv_names])
        intro_pat = f'"H{cell} {pure_intros} Hwand"'

    destructs = ""

    # IH call: inv_provide has [] slots for each invariant
    inv_provide = "".join([" []"] * len(inv_names))
    inv_subgoals = ""
    if inv_names:
        extra_a_args = " ".join(f"a_{i}" for i in range(len(wi.extra_cells)))
        for j, name in enumerate(inv_names):
            if j < len(wi.inv_axiom_indices) and wi.inv_axiom_indices[j] >= 0:
                axidx = wi.inv_axiom_indices[j]
                inv_subgoals += (f"      {{ iPureIntro; eapply smt_ax_{axidx}; "
                                 f"[exact Hz | exact Hcond | exact Hinv{j}]. }}\n")
            else:
                inv_subgoals += f"      {{ iPureIntro. snakelet_pure_hyps. first [ nia | sfirstorder | lia ]. }}\n"

    return f"""  Lemma {wi.lemma_name} {cell_params} (bound : Z) (z : Z) {extra_params}
      (Phi : Result -> iProp Sigma) :
    {pts_premise} -∗
    ⌜Z.le z bound⌝ -∗
{inv_premise_block}
    ({cont_premise}) -∗
    WPE (While ({cond}) ({body})) {{{{ Phi }}}}.
  Proof.
    iLöb as "IH" forall (z{extra_ih_vars} Phi).
    iIntros {intro_pat}.
    {destructs}iApply wp_while; iNext; simpl.
    heap_load. pure_step. case_bool.
    - snakelet_pure_hyps.
      pure_step.
      iRename select (_ ↦ _)%I into "Hpt".
{body_proof}
      pure_step.  (* sequencing _ *)
      iApply ("IH" $! (z + 1)%Z{extra_ih_args} Phi
        with "[$] []{inv_provide} Hwand").
      {{ iPureIntro. apply (proj2 (Z.le_succ_l z bound)). exact Hcond. }}
{inv_subgoals}    - snakelet_pure_hyps.
      assert (z = bound) by lia. subst z.
      pure_step.
      iApply wp_value. iApply "Hwand". iFrame.
  Qed."""


def _collect_while_invs_exn(stages: list[StageNode]) -> list[WhileInv]:
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


def _while_str_inv_coq(ws: WhileStr) -> str:
    """The path-dependent loop invariant for a string-guard loop.

    [Inv s := (s = guard \\/ s = final)] for the guard cell, conjoined with
    the other cells' post-state points-to (those are written unconditionally
    in the body so they hold the post value once the body has run; in the
    invariant we only need them framed, so we phrase them path-dependently
    too).  Single-cell case: just the guard-value disjunction."""
    g = ws.guard_value
    f = ws.final_value
    # Guard cell: starts at g, ends at f.  Both branches are guard-false-
    # detectable: s = f gives eqb f g = false (f != g enforced at detection).
    return f'(fun s => (⌜s = "{g}"%string \\/ s = "{f}"%string⌝)%I)'


def _emit_while_str_lemma_exn(ws: WhileStr) -> str:
    """Generate the NAMED body-obligation lemma for a string-guard loop.

    This is the Hoare triple {l ↦ g * Inv g} body {∃ s', l ↦ s' * Inv s' *
    eqb s' g = false}, proved standalone and consumed by wp_while_str at the
    call site.  Single-cell (no other cells) for now."""
    g = ws.guard_value
    f = ws.final_value
    # Substitute the guard cell variable with the lemma's [l] location.
    body = ws.body_coq.replace(f'(Var "{ws.guard_cell}")', '(Val (LitLoc l))')
    inv_pred = f'(⌜s = "{g}"%string \\/ s = "{f}"%string⌝)%I'

    body_lines = _emit_stage_lines(ws.body_stages, 0, "      ")
    body_proof = "\n".join(body_lines)

    return f"""  Definition {ws.lemma_name}_inv (s : string) : iProp Sigma :=
    {inv_pred}.

  Lemma {ws.lemma_name} (l : loc) :
    l ↦ LitString "{g}"%string -∗ {ws.lemma_name}_inv "{g}"%string -∗
    WPE ({body})
      {{{{ (fun r => match r with
          | RVal _ => ∃ s', l ↦ LitString s' ∗ {ws.lemma_name}_inv s' ∗ ⌜String.eqb s' "{g}"%string = false⌝
          | RExn lbl p => False
          end)%I }}}}.
  Proof.
    iIntros "Hl _".
{body_proof}
    iExists "{f}"%string. iFrame. iSplit.
    - iPureIntro. right. reflexivity.
    - iPureIntro. reflexivity.
  Qed."""


def _collect_while_strs_exn(stages: list[StageNode]) -> list[WhileStr]:
    """Walk the stage tree and collect all WhileStr nodes."""
    out: list[WhileStr] = []
    def walk(nodes: list[StageNode]) -> None:
        for n in nodes:
            if isinstance(n, WhileStr):
                out.append(n)
            elif isinstance(n, Branch):
                for arm in n.arms:
                    walk(arm)
    walk(stages)
    return out


def _emit_while_str_stage_exn(ws: WhileStr, indent: str) -> list[str]:
    """Emit the call-site proof applying wp_while_str + the body lemma.

    Focuses the While via wp_bind_item, applies wp_while_str with the
    synthesised invariant, discharges the body obligation by [iApply
    <lemma>] (the named body lemma), and proves the closing wand (guard-
    false + Inv => continuation)."""
    g = ws.guard_value
    f = ws.final_value
    body = ws.body_coq.replace(f'(Var "{ws.guard_cell}")', '(Val (LitLoc l))')

    lines: list[str] = []
    lines.append(f'{indent}iApply (wp_bind_item (LetCtx "_" _)); [reflexivity|].')
    lines.append(
        f'{indent}iApply (wp_while_str l "{g}"%string "{g}"%string '
        f'({body}) {ws.lemma_name}_inv _ with "[$] [] [] []").')
    # Hbc: "_" not free in body
    lines.append(f'{indent}{{ intros v. reflexivity. }}')
    # initial invariant Inv g = (g = g \/ g = f) -> left
    lines.append(f'{indent}{{ iPureIntro. left. reflexivity. }}')
    # body obligation: the named lemma
    lines.append(f'{indent}{{ iApply {ws.lemma_name}. }}')
    # closing wand: guard-false sf + Inv sf => sf = f, then continuation
    lines.append(
        f'{indent}{{ iIntros (sf) "%Hsf Hl %Hinv". '
        f'assert (sf = "{f}"%string) as ->; '
        f'[ destruct Hinv as [-> | ->]; [discriminate Hsf | reflexivity] | ]. '
        f'unfold bind_post; simpl. pure_step. heap_load. pure_step. '
        f'finish_pure. }}')
    return lines


def _extract_extra_cells(body_coq: str, counter_cell: str) -> list[str]:
    """Find extra heap cell variable names in the body expression."""
    import re
    out: list[str] = []
    for m in re.finditer(r'Var\s+"(l\d*)"', body_coq):
        v = m.group(1)
        if v != counter_cell and v not in out:
            out.append(v)
    return out


def _emit_pure_counter_while(wi: WhileInv, indent: str) -> list[str]:
    """Emit a pure-counter while proof using wp_while_decreasing.

    Uses a nat counter as the decreasing measure.  The invariant I n
    holds the loop state; n decreases each iteration.  The body obligation
    proves ∃ n', n' < n ∧ I n'.
    """
    lines: list[str] = []
    lines.append(f'{indent}iApply (wp_while_decreasing '
                 f'({wi.cond_coq}) ({wi.body_coq}) 100%nat _ _).')
    # Body obligation
    lines.append(f'{indent}{{ (* body: ∀ n, I n -∗ WPE *)')
    lines.append(f'{indent}  iIntros (n) "HI".')
    # Emit the actual body stages
    bs = _emit_stage_lines(wi.body_stages, 0, indent + "  ")
    lines.extend(bs)
    # After body: prove the measure decreased
    lines.append(f'{indent}  iExists (n - 1)%nat. iSplit; '
                 f'[iPureIntro; lia | ].')
    lines.append(f'{indent}  (* restore invariant I (n-1) *)')
    lines.append(f'{indent}  done. }}')
    # Done case: I 0 → Φ (RVal LitUnit)
    lines.append(f'{indent}{{ (* done: I 0 -∗ Φ (RVal LitUnit)) *)')
    lines.append(f'{indent}  iIntros "HI". simpl. pure_step. '
                 f'finish_pure. }}')
    # Initial: prove I 100
    lines.append(f'{indent}{{ (* initial: I 100%nat *)')
    lines.append(f'{indent}  done. }}')
    return lines


def _emit_while_inv_stage_exn(wi: WhileInv, indent: str) -> list[str]:
    """Emit the call-site proof for a per-loop lemma.

    Focuses the While with wp_bind_item, then applies the pre-proved
    per-loop lemma."""
    bound = wi.bound_expr
    if bound.startswith("LitInt "):
        bound = bound[len("LitInt "):].strip()

    lines: list[str] = []
    if "Load" not in wi.cond_coq:
        # Pure-counter while: use wp_while_decreasing with nat measure.
        return _emit_pure_counter_while(wi, indent)
    lines.append(f'{indent}iApply (wp_bind_item (LetCtx "_" _)); '
                 f'[reflexivity|].')
    cell_args = ("l " + " ".join(list(wi.extra_cells))) if wi.extra_cells else "l"
    extra_zeros = " ".join(["0"] * len(wi.extra_cells))
    zeros_args = (" " + extra_zeros) if extra_zeros else ""

    # Invariant premises: only for promoted loops (cell == "l")
    is_promoted = (wi.cell_name == "l")
    inv_with_args = ""
    inv_blocks = ""
    if is_promoted and wi.invariants:
        for j in range(len(wi.invariants)):
            inv_with_args += " []"
            if j < len(wi.inv_axiom_indices) and wi.inv_axiom_indices[j] >= 0:
                axidx = wi.inv_axiom_indices[j]
                inv_blocks += f'{indent}{{ iPureIntro; try nia; try lia; simpl; reflexivity. }}\n'
            else:
                inv_blocks += (f'{indent}{{ iPureIntro. snakelet_pure_hyps. '
                               f'first [ nia | sfirstorder | lia ]. }}\n')

    lines.append(
        f'{indent}iApply ({wi.lemma_name} {cell_args} {bound} 0{zeros_args} _ with "[$] []{inv_with_args}").')
    lines.append(f'{indent}{{ iPureIntro. lia. }}')
    if inv_blocks:
        lines.append(inv_blocks.rstrip('\n'))
    extra = wi.extra_cells
    if extra:
        qi = " ".join(f"a_{i}" for i in range(len(extra)))
        cells_hyps = " & ".join([f"H{wi.cell_name}"] + [f"H{ec}" for ec in extra])
        post_loop = (f'{indent}{{ iIntros ({qi}) "({cells_hyps})". '
                     f'unfold bind_post; simpl. pure_step. '
                     f'heap_load. pure_step. finish_pure. }}')
    else:
        post_loop = (f'{indent}{{ iIntros "H{wi.cell_name}". '
                     f'unfold bind_post; simpl. pure_step. '
                     f'heap_load. pure_step. finish_pure. }}')
    lines.append(post_loop)
    return lines
    """Emit the call-site proof for a per-loop lemma.

    Focuses the While with wp_bind_item, then applies the pre-proved
    per-loop lemma."""
    bound = wi.bound_expr
    if bound.startswith("LitInt "):
        bound = bound[len("LitInt "):].strip()

    lines: list[str] = []
    if "Load" not in wi.cond_coq:
        raise IrisGenError(
            "pure-counter while loop: needs a Loeb lemma (later phase)")
    lines.append(f'{indent}iApply (wp_bind_item (LetCtx "_" _)); '
                 f'[reflexivity|].')

    # Build lemma application with all cell arguments and extra param zeros
    cell_args = ("l " + " ".join(list(wi.extra_cells))) if wi.extra_cells else "l"
    extra_zeros = " ".join(["0"] * len(wi.extra_cells))
    zeros_args = (" " + extra_zeros) if extra_zeros else ""

    # Invariant premises: only for promoted loops (cell == "l")
    is_promoted = (wi.cell_name == "l")
    inv_with_args = ""
    inv_blocks = ""
    if is_promoted and wi.invariants:
        for j in range(len(wi.invariants)):
            inv_with_args += " []"
            if j < len(wi.inv_axiom_indices) and wi.inv_axiom_indices[j] >= 0:
                inv_blocks += f'{indent}{{ iPureIntro; try nia; try lia; simpl; reflexivity. }}\n'
                inv_blocks += f'{indent}{{ iPureIntro; try nia; try lia; simpl; reflexivity. }}\n'
            else:
                inv_blocks += (f'{indent}{{ iPureIntro. snakelet_pure_hyps. '
                               f'first [ nia | sfirstorder | lia ]. }}\n')

    lines.append(
        f'{indent}iApply ({wi.lemma_name} {cell_args} {bound} 0{zeros_args} _ with "[$] []{inv_with_args}").')
    lines.append(f'{indent}{{ iPureIntro. lia. }}')
    if inv_blocks:
        lines.append(inv_blocks.rstrip('\n'))
    extra = wi.extra_cells
    if extra:
        qi = " ".join(f"a_{i}" for i in range(len(extra)))
        cells_hyps = " & ".join([f"H{wi.cell_name}"] + [f"H{ec}" for ec in extra])
        post_loop = (f'{indent}{{ iIntros ({qi}) "({cells_hyps})". '
                     f'unfold bind_post; simpl. pure_step. '
                     f'heap_load. pure_step. finish_pure. }}')
    else:
        post_loop = (f'{indent}{{ iIntros "H{wi.cell_name}". '
                     f'unfold bind_post; simpl. pure_step. '
                     f'heap_load. pure_step. finish_pure. }}')
    lines.append(post_loop)
    return lines


def _emit_stage_lines(nodes: list[StageNode], depth: int,
                       indent: str, post: str = "",
                       active_ghost_vars: set[tuple[str, str]] | None = None) -> list[str]:
    """Render a stage tree into proof-script lines for the exception
    backend (the sole Iris backend).

    active_ghost_vars: accumulated set of (gv_name, callee_suffix) pairs
    from destruct_ghost stages.  Emitted as ghost_close after each
    finish_pure stage, then cleared."""
    if active_ghost_vars is None:
        active_ghost_vars = set()
    lines: list[str] = []
    for n in nodes:
        if isinstance(n, Stage):
            text = f"{indent}{n.tactic}."
            cid = f"[{n.stage_id}]" if n.stage_id else ""
            if n.comment:
                text += f"  (* {cid} {n.comment} *)"
            elif cid:
                text += f"  (* {cid} *)"
            lines.append(text)
            # Track ghost vars from destruct_ghost stages
            if n.category == "destruct_ghost":
                for gv in _parse_ghost_names(n.comment):
                    active_ghost_vars.add(gv)
            # Emit ghost_close after finish_pure -- only for ghost vars
            # that actually appear in the WP postcondition.
            if n.category == "finish_pure" and active_ghost_vars:
                for gv, suf in sorted(active_ghost_vars):
                    if gv in post:
                        lines.append(
                            f"{indent}exists {gv}. "
                            f"split; [exact Hrz{suf} | exact H_{gv}{suf}].")
                active_ghost_vars.clear()
        elif isinstance(n, Branch):
            if depth >= len(_BULLETS):
                raise IrisGenError("case split nesting exceeds bullet depth")
            bullet = _BULLETS[depth]
            for arm in n.arms:
                # Each arm starts with a fresh copy of active ghost vars
                arm_vars = set(active_ghost_vars)
                arm_lines = _emit_stage_lines(arm, depth + 1, indent + "  ",
                                               post, arm_vars)
                first = arm_lines[0].lstrip()
                lines.append(f"{indent}{bullet} {first}")
                lines.extend(arm_lines[1:])
        elif isinstance(n, WhileInv):
            lines.extend(_emit_while_inv_stage_exn(n, indent))
        elif isinstance(n, WhileStr):
            lines.extend(_emit_while_str_stage_exn(n, indent))
        elif isinstance(n, ForList):
            lines.extend(_emit_for_list_stage_exn(n, indent))
    return lines


def _parse_ghost_names(comment: str) -> list[tuple[str, str]]:
    """Extract ghost var names with callee suffix from a destruct_ghost comment.

    Comment format: 'name ghost vars: payment_final, commit_final (suffix _do_capture)'
    Returns [(gv_name, suffix)] pairs."""
    import re
    prefix = "name ghost vars: "
    if not comment.startswith(prefix):
        return []
    rest = comment[len(prefix):]
    # Extract suffix if present: "..., gv (suffix _func)"
    m = re.search(r'\(suffix (_\w+)\)', rest)
    suffix = m.group(1) if m else ""
    names_part = rest[:m.start()].rstrip() if m else rest
    names = [s.strip() for s in names_part.split(",") if s.strip()]
    return [(n, suffix) for n in names]


# -- Top-level ------------------------------------------------------------


def _emit_for_list_stage_exn(fl: ForList, indent: str) -> list[str]:
    """Emit a wp_for_list' application for the exception backend.

    The new wp_for_list' has signature
        wp_for_list' x body M P Phi :
          (closed) -> P M -* (box step) -* (P [] -* Phi (RVal LitUnit))
          -* WPE (For x (Val (LitList M)) body) {{ Phi }}
    with the per-element step postcondition being the Result-match
        fun r => match r with RVal _ => P vs | RExn l p => Phi (RExn l p) end.

    For the no-accumulator case the suffix invariant is trivial (emp).  When
    there is a trailing continuation, the For sits under a [Let "_" _ cont]
    bind; we focus it with wp_bind_item and let Phi be the bind_post."""
    if fl.iterable_type == "dict":
        raise IrisGenError(
            "exn backend: dict for-loops not yet supported (phase 4)")

    has_cont = bool(fl.continuation_stages)
    lines: list[str] = []
    if has_cont:
        # The For is the bound expression of a Let "_" _ continuation.
        lines.append(f'{indent}iApply (wp_bind_item (LetCtx "_" _)); '
                     f'[reflexivity|].')

    if fl.forall_predicate:
        # Accumulating loop: the suffix invariant is [Forall Q vs].  The
        # full-list premise [Forall Q M] is discharged structurally (works
        # for literal lists; an opaque list parameter has no such proof and
        # will fail to compile -- which is sound).
        q_pred = fl.forall_predicate
        lines.append(f'{indent}iApply (wp_for_list_forall {q_pred}'
                     f' "{fl.var}" ({fl.body_coq}) ({fl.lst_coq}) _).')
        lines.append(f'{indent}{{ intros w; reflexivity. }}')
        lines.append(f'{indent}{{ (* Forall premise at full list *)')
        if fl.from_precondition:
            # Forall derived from forallb precondition via Hpre.
            lines.append(f'{indent}  iPureIntro. '
                         f'apply forallb_to_Forall. exact Hpre. }}')
        else:
            # Literal list: prove structurally.
            lines.append(f'{indent}  iPureIntro. simpl. '
                         f'repeat (try constructor; try lia). }}')
        lines.append(f'{indent}{{ (* per-element body step *)')
        lines.append(f'{indent}  iModIntro. iIntros (vfor vrest) "%Hfor".')
        lines.append(f'{indent}  inversion Hfor as [|? ? Hq Hvs]; subst.')
        lines.append(f'{indent}  simpl.')
        body_lines = _emit_stage_lines(fl.body_stages, 0, indent + "  ")
        lines.extend(body_lines)
        # Close the body: it reduces to a value; the postcondition is the
        # tail Forall fact carried in Hvs.
        lines.append(f'{indent}  popvals; iApply wp_value; iPureIntro; '
                     f'exact Hvs. }}')
    else:
        # No-accumulator case: trivial suffix invariant emp.
        lines.append(f'{indent}iApply (wp_for_list' + "'"
                     + f' "{fl.var}" ({fl.body_coq}) ({fl.lst_coq}) '
                     f'(fun _ => emp%I) _).')
        lines.append(f'{indent}{{ intros w; reflexivity. }}')
        lines.append(f'{indent}{{ (* invariant at full list *) done. }}')
        lines.append(f'{indent}{{ (* per-element body step *)')
        lines.append(f'{indent}  iModIntro. iIntros (vfor vrest) "_". simpl.')
        body_lines = _emit_stage_lines(fl.body_stages, 0, indent + "  ")
        lines.extend(body_lines)
        lines.append(f'{indent}  finish_pure.')
        lines.append(f'{indent}}}')

    # The terminal premise: P [] -* Phi (RVal LitUnit).
    lines.append(f'{indent}{{ (* post-loop continuation *) iIntros "_".')
    if has_cont:
        lines.append(f'{indent}  unfold bind_post; simpl.')
        cont_lines = _emit_stage_lines(fl.continuation_stages, 0,
                                       indent + "  ")
        lines.extend(cont_lines)
    else:
        # No continuation: the loop result LitUnit must meet the post.
        lines.append(f'{indent}  finish_pure.')
    lines.append(f'{indent}}}')
    return lines




_HEADER_EXN = (
    "(* Generated by iris_proof_gen -- staged Iris proof (exception backend). *)\n"
    "From iris.proofmode Require Import proofmode coq_tactics reduction.\n"
    "From iris.base_logic.lib Require Import gen_heap.\n"
    "From Hammer Require Import Hammer.\n"
    "Require Import SnakeletExnLang SnakeletExnWp SnakeletExnTactics.\n"
    "Require Import ListPredicates.\n"
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
    list_params: dict[str, str] = field(default_factory=dict)
    dict_params: dict[str, str] = field(default_factory=dict)
    raises: dict[str, str] = field(default_factory=dict)
    """Exception contracts: exc_type -> Coq condition Prop (the RExn arm)."""
    param_types: dict[str, str] = field(default_factory=dict)
    """Parameter type annotations: param_name -> python type (int|str|bool|dict|list|...)."""
    predicate_fixpoints: list[str] = field(default_factory=list)
    """Coq Fixpoint definitions for recursive user predicates."""
    supercompiled_pre: Optional[str] = None
    """Supercompiled precondition Prop (with parameter binding)."""
    supercompiled_post: Optional[str] = None
    """Supercompiled postcondition Prop (with parameter binding)."""
    supercompiled_block: str = ""
    """Raw Coq definitions block for supercompiled contract expressions."""

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
        # Recursive user predicate Fixpoints (D1/D2).
        if self.predicate_fixpoints:
            parts.append("")
            parts.extend(self.predicate_fixpoints)
            parts.append("")
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
        parts.append("  Local Notation \"l ↦ v\" := (pointsto l (DfracOwn 1) v)")
        parts.append("    (at level 20) : bi_scope.")
        parts.append("")
        if self.supercompiled_block:
            parts.append(self.supercompiled_block)
            parts.append("")
        # Emit per-loop lemmas for WhileInv nodes
        for wi in _collect_while_invs_exn(self.stages):
            parts.append(_emit_while_inv_lemma_exn(wi))
            parts.append("")
        # Emit named body-obligation lemmas for WhileStr (string-guard) nodes
        for ws in _collect_while_strs_exn(self.stages):
            parts.append(_emit_while_str_lemma_exn(ws))
            parts.append("")
        # Coq binder types: Z for int/bool, sn_val for everything else.
        # Model types (Pydantic/dataclass) are also sn_val.
        def _coq_type(py_type: str) -> str:
            if py_type in ("int", "bool", "float"):
                return "Z"
            return "sn_val"
        binders = "".join(
            f" ({p} : {_coq_type(self.param_types.get(p, 'int'))})"
            for p in self.params
            if p not in self.list_params and p not in self.dict_params)
        # List-typed params are split into a value binder [xs : sn_val] and
        # its model [M_xs : list sn_val], tied by the premise xs = LitList M_xs.
        for lp, mv in self.list_params.items():
            binders += f" ({lp} : sn_val) ({mv} : list sn_val)"
        parts.append(f"  Lemma {self.name}_correct{binders} :")
        model_premises: list[str] = [
            f"{lp} = LitList {mv}" for lp, mv in self.list_params.items()]
        if model_premises:
            parts.append(f"    ({' -> '.join(model_premises)}) ->")
        if self.pre:
            parts.append(f"    ({self.supercompiled_pre if self.supercompiled_pre else self.pre}) ->")
        # Result-match postcondition.  The RVal arm is the normal post;
        # the RExn arm dispatches on the exception label.  Each raises()
        # contract becomes [RExn "Type" _ => cond]; un-listed exceptions
        # default to False (the function must not raise them).
        if self.raises:
            # Nest String.eqb checks: dispatch the exception label to its
            # condition, defaulting un-listed labels to False.
            exn_arm = "False"
            for exc_type, cond in reversed(list(self.raises.items())):
                exn_arm = (
                    f'(if String.eqb lbl "{exc_type}" '
                    f'then {LCEIL}({cond})%Z{RCEIL} else {exn_arm})'
                )
            post_match = (
                f"(fun r => match r with "
                f"RVal v => {LCEIL}({self.supercompiled_post if self.supercompiled_post else self.post})%Z{RCEIL} | "
                f"RExn lbl _ => {exn_arm} end)%I"
            )
        else:
            post_match = (
                f"(fun r => match r with "
                f"RVal v => {LCEIL}({self.supercompiled_post if self.supercompiled_post else self.post})%Z{RCEIL} | "
                f"RExn _ _ => False end)%I"
            )
        parts.append(f"    {TSTILE} WPE {self.body_coq} "
                     f"{{{{ {post_match} }}}}.")
        parts.append("  Proof.")
        for lp, _ in self.list_params.items():
            parts.append(f"    intros H_{lp}.")
            parts.append(f"    subst {lp}.")
        if self.pre:
            parts.append("    intros Hpre.")
        parts.append("    iStartProof.")
        parts.extend(_emit_stage_lines(self.stages, 0, "    ", self.post))
        parts.append("  Qed.")
        parts.append("End generated_proofs.")
        return "\n".join(parts) + "\n"

    def emit_residual(self, stage_id: int) -> str:
        """Generate a residual .v fragment that replays the proof up to
        (but not including) the given [stage_id], then issues [Show.]
        to output the goal state.  Use when a tactic at [stage_id] fails
        and you need to inspect the open goal with its hypotheses.

        Returns a complete .v file that loads the same dependencies and
        replays the proof script up to the failing stage.
        """
        parts = [_HEADER_EXN]
        parts.append(self.table_coq)
        parts.append("")
        parts.append("Section generated_residual.")
        parts.append("  Context `{!snakeletExn_heapGS_gen hlc Sigma}.")
        # Emit the lemma and proof up to the target stage
        parts.append(f"  Lemma {self.name}_residual{self._render_binders()} :")
        if self.list_params:
            premises = " -> ".join(
                f"{lp} = LitList {mv}" for lp, mv in self.list_params.items())
            parts.append(f"    ({premises}) ->")
        if self.pre:
            parts.append(f"    ({self.pre}) ->")
        parts.append(f"    {TSTILE} WPE {self.body_coq} "
                      f"{{{{ (fun r => match r with "
                      f"RVal v => {LCEIL}({self.post})%Z{RCEIL} | "
                      f"RExn _ _ => False end)%I }}}}.")
        parts.append("  Proof.")
        for lp, _ in self.list_params.items():
            parts.append(f"    intros H_{lp}. subst {lp}.")
        if self.pre:
            parts.append("    intros Hpre.")
        parts.append("    iStartProof.")
        # Replay stages up to the target
        self._emit_stages_up_to(stage_id, parts, "    ")
        parts.append("    Show.")
        parts.append("  Abort.")
        parts.append("End generated_residual.")
        return "\n".join(parts) + "\n"

    def _render_binders(self) -> str:
        def _coq_type(py_type: str) -> str:
            if py_type in ("int", "bool", "float"):
                return "Z"
            return "sn_val"
        binders = "".join(
            f" ({p} : {_coq_type(self.param_types.get(p, 'int'))})"
            for p in self.params
            if p not in self.list_params and p not in self.dict_params)
        for lp, mv in self.list_params.items():
            binders += f" ({lp} : sn_val) ({mv} : list sn_val)"
        return binders

    def _emit_stages_up_to(self, target_id: int, parts: list[str],
                           indent: str) -> bool:
        """Emit proof-script lines for stages with id <= target_id.
        Returns True if we stopped at the target stage (emitted its
        preceding context but not the tactic itself)."""
        return _emit_stages_up_to_id(self.stages, 0, target_id, parts,
                                     indent, set(), self.post)

    def stage_trace(self) -> dict[int, Stage]:
        """Return {stage_id: Stage} for all stages in the proof."""
        out: dict[int, Stage] = {}
        for s in self.stage_list():
            out[s.stage_id] = s
        return out


def _emit_stages_up_to_id(nodes: list[StageNode], depth: int,
                          target_id: int, parts: list[str],
                          indent: str, ghost_vars: set[str],
                          post: str) -> bool:
    """Emit stages up to (not including) target_id.  Returns True iff
    the target was found and emission stopped at it."""
    for n in nodes:
        if isinstance(n, Stage):
            if n.stage_id >= target_id:
                return True  # stop before this stage
            text = f"{indent}{n.tactic}."
            if n.comment:
                text += f"  (* [{n.stage_id}] {n.comment} *)"
            else:
                text += f"  (* [{n.stage_id}] *)"
            parts.append(text)
            if n.category == "destruct_ghost":
                for gv in _parse_ghost_names(n.comment):
                    ghost_vars.add(gv)
            if n.category == "finish_pure" and ghost_vars:
                for gv, suf in sorted(ghost_vars):
                    if gv in post:
                        parts.append(f"{indent}exists {gv}. "
                                     f"split; [exact Hrz{suf} | exact H_{gv}{suf}].")
                ghost_vars.clear()
        elif isinstance(n, Branch):
            for arm in n.arms:
                arm_vars = set(ghost_vars)
                found = _emit_stages_up_to_id(arm, depth + 1, target_id,
                                              parts, indent + "  ",
                                              arm_vars, post)
                if found:
                    return True
    return False


def generate(name: str,
              body: SExpr,
              post: str,
              table: FunTable,
              params: Optional[list[str]] = None,
              pre: Optional[str] = None,
              axioms: Optional[list[str]] = None,
               pre_overrides: Optional[dict[str, str]] = None,
               list_params: Optional[dict[str, str]] = None,
               dict_params: Optional[dict[str, str]] = None,
               raises: Optional[dict[str, str]] = None,
               param_types: Optional[dict[str, str]] = None,
               predicate_fixpoints: Optional[list[str]] = None,
               forall_predicates: Optional[dict[str, str]] = None) -> IrisProof:
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
    _STAGE_ID_COUNTER[0] = 0
    stages = _gen(body, table, overrides,
                  lambda: [_mk_stage("finish_pure", "finish_pure",
                                 comment="postcondition")],
                  func_name=name, _inv_counter=inv_counter,
                  list_params=list_params or {},
                   dict_params=dict_params or {},
                  forall_predicates=forall_predicates or {})
    return IrisProof(
        name=name,
        body_coq=body.to_coq(),
        post=post,
        params=params or [],
        pre=pre,
        axioms=axioms or [],
        table_coq=_emit_table_section(table),
        stages=stages,
        list_params=list_params or {},
        dict_params=dict_params or {},
        raises=raises or {},
        param_types=param_types or {},
        predicate_fixpoints=predicate_fixpoints or [],
    )
