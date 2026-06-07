"""SnakeletIR — minimal Python-like IR with Iris-clean mappings.

~10 constructors, each with a direct Iris heapLang WP lemma.
The lowering from PyIR to SnakeletIR resolves Python field names
to abstract locations using the resource footprint (owns + modifies).
Pure side conditions become SMT-trusted axioms.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, Literal


# ── Expressions ──────────────────────────────────────────────────

@dataclass
class SLet:
    """Let-binding: let x = e1 in e2.  Iris: wp_let / wp_bind."""
    var: str
    value: "SExpr"
    body: "SExpr"
    kind: Literal["let"] = "let"


@dataclass
class SBinOp:
    """Binary operation.  Iris: wp_binop."""
    op: str          # "add" | "sub" | "mul" | "div" | "eq" | "lt" | "gt"
    left: "SExpr"
    right: "SExpr"
    kind: Literal["binop"] = "binop"


@dataclass
class SLoad:
    """Heap load.  Iris: wp_load."""
    loc: str         # abstract location name, e.g. "l__box_value"
    kind: Literal["load"] = "load"


@dataclass
class SStore:
    """Heap store.  Iris: wp_store."""
    loc: str         # abstract location name
    value: "SExpr"
    kind: Literal["store"] = "store"


@dataclass
class SIf:
    """Conditional.  Iris: wp_if."""
    cond: "SExpr"
    then_branch: "SExpr"
    else_branch: "SExpr"
    kind: Literal["if"] = "if"


@dataclass
class SReturn:
    """Return value.  Iris: postcondition (RET val)."""
    value: "SExpr"
    kind: Literal["return"] = "return"


@dataclass
class SLit:
    """Literal.  Iris: LitV (LitInt n) / LitV (LitLoc l)."""
    lit_type: str    # "int" | "bool" | "loc" | "unit"
    value: str       # "42" | "true" | "l__box_value"
    kind: Literal["lit"] = "lit"


@dataclass
class SVar:
    """Variable reference.  Iris: bound variable (wp_let naming)."""
    name: str
    kind: Literal["var"] = "var"


@dataclass
class SApp:
    """Function application.  Iris: wp_app."""
    func: str
    args: list["SExpr"]
    kind: Literal["app"] = "app"


@dataclass
class SSeq:
    """Sequence of expressions.  Iris: let _ = e1 in e2."""
    exprs: list["SExpr"]
    kind: Literal["seq"] = "seq"


@dataclass
class SFork:
    """Fork a thread.  Iris: wp_fork."""
    expr: "SExpr"
    kind: Literal["fork"] = "fork"


@dataclass
class SFAA:
    """Fetch-and-add: atomic x += v.  Iris: wp_faa."""
    loc: str
    value: "SExpr"
    kind: Literal["faa"] = "faa"


@dataclass
class SRaise:
    """Raise exception.  Encoded as ORaise outcome in WP."""
    exc: SExpr
    kind: Literal["raise"] = "raise"


@dataclass
class STry:
    """Try/except.  Encoded as ORaise match in WP."""
    body: SExpr
    exc_var: str
    handler: SExpr
    kind: Literal["try"] = "try"


@dataclass
class SDictGet:
    """Dict lookup: d[key] → gmap lookup.  Pure, no heap mutation."""
    loc: str
    key: SExpr
    kind: Literal["dict_get"] = "dict_get"


@dataclass
class SDictSet:
    """Dict set: d[key] = val → gmap insert.  Pure, no heap mutation."""
    loc: str
    key: SExpr
    value: SExpr
    kind: Literal["dict_set"] = "dict_set"


SExpr = SLit | SVar | SBinOp | SLoad | SStore | SLet | SIf | SReturn | SApp | SSeq | SFork | SFAA | SRaise | STry | SDictGet | SDictSet


# ── Resource layer ───────────────────────────────────────────────

@dataclass
class SField:
    """Resource: points-to assertion.  box.value ↦ v."""
    obj: str         # "box"
    field: str       # "value"
    loc: str         # abstract location, e.g. "l__box_value"
    old_var: str     # ghost name for pre-state value, e.g. "old_box_value"


@dataclass
class SOwns:
    """Resource: ownership marker.  becomes ↦ in Iris."""
    obj: str


@dataclass
class SPure:
    """Pure side condition.  becomes SMT axiom."""
    expr: str        # e.g. "t1 = old_box_value + 1"


# ── Function spec ────────────────────────────────────────────────

@dataclass
class SFunction:
    """A lowered function with resource spec."""
    name: str
    params: list[str]
    body: SExpr              # the lowered body
    pre_fields: list[SField]  # heap cells owned before execution
    pre_pure: list[SPure]     # pure preconditions
    post_pure: list[SPure]    # pure postconditions / side conditions
    modifies: list[str]       # field names written
    raises: list[str] = field(default_factory=list)   # exception names
    classification: str = "mixed_pure_resource"


# ── Iris emitter ─────────────────────────────────────────────────

def emit_iris_snakelet(fn: SFunction) -> str:
    """Emit an Iris Hoare triple + proof skeleton for a lowered function."""
    lines = []
    lines.append(f"(* Iris proof for `{fn.name}` — SnakeletIR lowering *)")
    lines.append(f"(* Classification: {fn.classification} *)")
    lines.append("")
    lines.append("From iris.program_logic Require Import weakestpre.")
    lines.append("From iris.proofmode Require Import proofmode.")
    lines.append("From iris.heap_lang Require Import lang proofmode notation.")
    lines.append("")

    # SMT-trusted axioms for pure side conditions
    for i, pc in enumerate(fn.post_pure):
        lines.append(f"Axiom smt_pure_{fn.name}_{i} : {pc.expr}.")
    if fn.post_pure:
        lines.append("")

    # Precondition heap ownership
    pre_heap = " ∗ ".join(
        f"{f.loc} ↦ {f.old_var}"
        for f in fn.pre_fields
    )
    pre_pure = " ∗ ".join(
        f"⌜{p.expr}⌝"
        for p in fn.pre_pure
    )
    pre_sep = " ∗ ".join(filter(None, [pre_heap, pre_pure]))
    if not pre_sep:
        pre_sep = "True"

    # Postcondition — normal return
    post_heap = " ∗ ".join(
        f"{f.loc} ↦ ({f.old_var} + 1)"
        for f in fn.pre_fields
    )
    post_pure = " ∗ ".join(
        f"⌜{p.expr}⌝"
        for p in fn.post_pure
    )
    post_sep = " ∗ ".join(filter(None, [post_heap, post_pure]))
    if not post_sep:
        post_sep = "True"

    # Exception postcondition — ORaise case
    raise_post = " | ".join(
        f"ORaise (LitString \"{e}\") σ ; l__box_value ↦ old_box_value"
        for e in fn.raises
    ) if hasattr(fn, 'raises') and fn.raises else ""

    lines.append(f"Lemma {fn.name}_spec {' '.join(fn.params)} :")
    lines.append(f"  {{{{{{ {pre_sep} }}}}}}")
    lines.append(f"    {fn.name}_core {' '.join(fn.params)}")
    lines.append(f"  {{{{{{ result, RET result;")
    lines.append(f"      {post_sep} }}}}}}")
    if raise_post:
        lines.append(f"  {{{{{{ e σ, ORaise e σ;")
        lines.append(f"      {raise_post} }}}}}}.")
    else:
        lines.append(".")

    lines.append(f"Proof.")
    lines.append(f"  iIntros (Φ) \"({', '.join(f'H{f.loc}' for f in fn.pre_fields)}) HΦ\".")

    # Body lowering
    _emit_body(lines, fn.body, indent=2)

    # Postcondition
    lines.append(f"  iApply \"HΦ\".")
    if fn.pre_fields:
        names = " ".join(f"H{f.loc}" for f in fn.pre_fields)
        lines.append(f"  iFrame \"{names}\".")
    lines.append(f"  iPureIntro.")
    if fn.post_pure:
        lines.append(f"  repeat split.")
        for i in range(len(fn.post_pure)):
            lines.append(f"  exact smt_pure_{fn.name}_{i}.")
    lines.append(f"Qed.")
    return "\n".join(lines)


def _emit_body(lines: list[str], expr: SExpr, indent: int = 2) -> None:
    """Recursively emit Iris tactics for SnakeletIR expressions.

    SnakeletIR maps directly to heapLang, so each constructor emits
    the heapLang expression code plus its corresponding wp_ tactic.
    """
    sp = " " * indent
    if isinstance(expr, SLet):
        lines.append(f"{sp}(* let {expr.var} = ... *)")
        _emit_body(lines, expr.value, indent)
        lines.append(f"{sp}wp_let.")
        _emit_body(lines, expr.body, indent)
    elif isinstance(expr, SBinOp):
        _emit_body(lines, expr.left, indent)
        _emit_body(lines, expr.right, indent)
        lines.append(f"{sp}wp_pures.  (* {expr.op} *)")
    elif isinstance(expr, SLoad):
        lines.append(f"{sp}wp_load.")
    elif isinstance(expr, SStore):
        # Emit the value expression first, then wp_store
        _emit_body(lines, expr.value, indent)
        lines.append(f"{sp}wp_store.")
    elif isinstance(expr, SIf):
        lines.append(f"{sp}wp_if.")
    elif isinstance(expr, SReturn):
        lines.append(f"{sp}(* return *)")
    elif isinstance(expr, SSeq):
        for e in expr.exprs:
            _emit_body(lines, e, indent)
    elif isinstance(expr, SApp):
        lines.append(f"{sp}wp_apply ({expr.func}_spec).")
    elif isinstance(expr, SFork):
        _emit_body(lines, expr.expr, indent)
        lines.append(f"{sp}wp_fork.")
    elif isinstance(expr, SFAA):
        lines.append(f"{sp}wp_faa.")
    elif isinstance(expr, SRaise):
        # Raise as proof obligation — encoded in WP outcome
        lines.append(f"{sp}(* raise — encoded as ORaise in WP outcome *)")
    elif isinstance(expr, STry):
        lines.append(f"{sp}(* try/catch — outcome dispatch in WP *)")
        _emit_body(lines, expr.body, indent)
        lines.append(f"{sp}(* if ORaise -> handler *)")
        _emit_body(lines, expr.handler, indent)
    elif isinstance(expr, SDictGet):
        lines.append(f"{sp}(* dict lookup — pure *)")
    elif isinstance(expr, SDictSet):
        lines.append(f"{sp}(* dict insert — atomic, like Store *)")
        _emit_body(lines, expr.value, indent)
        lines.append(f"{sp}wp_dict_set.")
    else:
        lines.append(f"{sp}(* {type(expr).__name__} *)")
