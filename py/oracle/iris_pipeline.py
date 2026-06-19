"""Python source -> staged Iris proof wiring.

End-to-end pipeline for the Iris backend on the pure-integer fragment.

    Python ast
      -> contract extraction        (ContractLinter -> contract_ir -> Iris Prop
                                     via contract_ir_iris; positional classifies)
      -> PyIR                      (py_ir_translator)
      -> SnakeletIR                (continuation-folded statement lowering)
      -> ANF normalization
      -> staged proof              (iris_proof_gen.generate)

Contracts are plain assert statements, per the project ground rules:

    def chain(x):
        assert x >= 1            # precondition (leading assert)
        a = square(x)
        b = decr(a)
        assert b == x * x - 1    # postcondition (before-final-return assert)
        return b

Contract expressions use the full contract vocabulary supported by
ContractLinter: integer arithmetic, comparisons, boolean logic,
forall/exists over ranges, implies, min, max, string comparisons,
regex via re_match, and user-defined predicates with recursors.
The compilation to Iris Props is handled by contract_ir_iris.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional

from oracle.contract_ir_iris import compile_postcondition, compile_precondition, _collect_vars, iris_prop
from oracle.contract_linter import ContractLinter
from oracle.iris_lowerer import IrisLowerer
from oracle.iris_proof_gen import (
    FunTable, IrisGenError, IrisProof, generate,
)
from oracle.reporting import (
    GoalStatus, ProofLevel, Action, PipelineReport,
)
from oracle.py_ir import (
    PyAssert, PyAssign, PyAugAssign, PyCall, PyConstant, PyExprStmt,
    PyFor, PyIf, PyName, PyRaise, PyReturn, PyStmt, PyStoreSubscript, PyTry, PyWhile,
)
from oracle.py_ir_translator import PyIRTranslator
from oracle.snakelet_ir import (
    SAlloc, SApp, SBinOp, SDictGet, SDictSet, SExpr, SIf, SLet, SLit, SLoad, SRaise, SReturn, SSeq,
    SStore, STry, SVar, SWhile, SFor,
)

# Binops supported by SnakeletLang's binop_eval on integers.
_SUPPORTED_OPS = {"add", "sub", "mul", "eq", "le", "lt", "gt", "ge", "ne", "mod", "and", "or", "in", "append", "length", "set_add", "str_index", "starts_with", "ends_with", "to_lower", "to_upper", "dict_set"}


# -- Contract extraction ----------------------------------------------------

@dataclass
class Contracts:
    pre: Optional[str]
    post: str
    loop_invariants: list[list] = field(default_factory=list)
    """Invariants per while loop — contract_ir.Expr AST nodes.
    Call expr.to_coq() / expr.to_smt() at the point of use."""
    loop_invariant_exprs: list[list] = field(default_factory=list)
    raises: dict[str, str] = field(default_factory=dict)
    """Exception contracts: exc_type -> compiled Coq condition Prop.
    Each becomes a [RExn "exc_type" _ => cond] arm of the exception
    postcondition in the exception backend (emit_exn)."""


def extract_contracts(
    source: str, fn_node: ast.FunctionDef,
    list_model: dict[str, str] | None = None,
    ghost_resolver: dict[str, str] | None = None,
) -> tuple[Contracts, list[ast.stmt], ContractLinter]:
    """Split positional asserts out of the function body.

    Uses the existing ContractLinter to compile each assert expression
    into contract_ir and then to Iris Props via contract_ir_iris.

    Args:
        source: the full Python source (needed by the linter for line context)
        fn_node: the raw AST function definition
    Returns:
        Contracts, the body stmts with contracts removed, and a linter
        pre-configured for the postcondition (for subsequent callee use).
    """
    params = [a.arg for a in fn_node.args.args]
    param_type_hint = _param_type_map(fn_node)
    float_params = {p for p, t in param_type_hint.items() if t == "float"}
    string_params = {p for p, t in param_type_hint.items() if t in ("str", "string")}
    # Detect return type: if returns a model (shape-registered type), use
    # "sn_val" result kind so the postcondition uses v directly.
    result_kind: str | None = None
    if fn_node.returns:
        from oracle.shape_ir import lookup_shape
        if isinstance(fn_node.returns, ast.Name):
            if lookup_shape(fn_node.returns.id) is not None:
                result_kind = "sn_val"
    from oracle.contract_ir_iris import _FLOAT_PARAMS, _STRING_PARAMS
    _FLOAT_PARAMS.clear()
    _FLOAT_PARAMS.update(float_params)
    _STRING_PARAMS.clear()
    _STRING_PARAMS.update(string_params)
    pre_linter = ContractLinter(params=params, context="precondition",
                                ghost_resolver=ghost_resolver,
                                param_type_hint=param_type_hint)
    post_linter = ContractLinter(params=params, context="postcondition",
                                 ghost_resolver=ghost_resolver,
                                 param_type_hint=param_type_hint)

    lm = list_model or {}

    body = list(fn_node.body)
    pres: list[str] = []

    # Extract raises() contracts FIRST (position-independent): any assert
    # whose test is a raises(ExcType, cond) call.  Removing them before the
    # pre/post scan prevents a trailing raises() assert from being mistaken
    # for the postcondition.  Multiple conditions per exc_type are ANDed.
    from oracle.contract_ir import RaisesExpr
    from oracle.contract_ir_iris import iris_prop
    raises: dict[str, str] = {}
    _kept: list[ast.stmt] = []
    for stmt in body:
        if isinstance(stmt, ast.Assert):
            linted = post_linter.lint_expression(stmt.test)
            if linted.ir is not None and isinstance(linted.ir, RaisesExpr):
                cond_coq = iris_prop(linted.ir.cond)
                stmt_exc = linted.ir.exc_type
                if stmt_exc:
                    if stmt_exc in raises:
                        raises[stmt_exc] = f"({raises[stmt_exc]}) /\\ ({cond_coq})"
                    else:
                        raises[stmt_exc] = cond_coq
                continue
        _kept.append(stmt)
    body = _kept

    # Leading asserts = precondition
    while body and isinstance(body[0], ast.Assert):
        linted = pre_linter.lint_expression(body[0].test)
        if linted.ir is not None:
            pres.append(compile_precondition(linted.ir, list_model=lm))
        body = body[1:]

    pre = None
    if len(pres) == 1:
        pre = pres[0]
    elif pres:
        pre = " /\\ ".join(f"({p})" for p in pres)

    # Asserts immediately before final return = postcondition.
    # Multiple asserts are conjoined with `and`.
    post = "True"
    if body and isinstance(body[-1], ast.Return):
        ret_node = body[-1]
        ret_var = None
        if isinstance(ret_node.value, ast.Name):
            ret_var = ret_node.value.id
        post_asserts: list[ast.Assert] = []
        idx = len(body) - 2
        while idx >= 0 and isinstance(body[idx], ast.Assert):
            post_asserts.insert(0, body[idx])
            idx -= 1
        if post_asserts and ret_var is not None:
            posts: list[str] = []
            for a in post_asserts:
                linted = post_linter.lint_expression(a.test)
                if linted.ir is not None:
                    # Strip the existential wrapper so we can share [z].
                    prop = iris_prop(linted.ir, post_var=ret_var,
                                     post_bound="z")
                    posts.append(prop)
            if len(posts) == 1:
                # Single assert: use the standard wrapper.
                linted = post_linter.lint_expression(post_asserts[0].test)
                post = compile_postcondition(linted.ir, ret_var, list_model=lm,
                                               result_kind=result_kind,
                                               ghost_resolver=ghost_resolver)
            elif posts:
                # Shared existential: exists z, v = LitInt z /\ P1 /\ P2.
                # Ghost vars from ghost_resolver are nested inside.
                gh = ghost_resolver or {}
                ghost_vars_used: list[str] = []
                for a in post_asserts:
                    linted = post_linter.lint_expression(a.test)
                    if linted.ir is not None:
                        ghost_vars_used.extend(
                            sorted(_collect_vars(linted.ir).intersection(gh.values())))
                ghost_binders = "".join(
                    f"(exists ({gv} : Z), " for gv in dict.fromkeys(ghost_vars_used))
                ghost_closers = "".join(")" for _ in dict.fromkeys(ghost_vars_used))
                inner = " /\\ ".join(f"({p})" for p in posts)
                post = (f"exists z : Z, v = LitInt z /\\ "
                        f"({ghost_binders} ({inner}){ghost_closers})")
            body = body[:idx + 1] + [ret_node]

    # Extract loop invariants from while loops in the body
    loop_invs: list[list[str]] = []
    _extract_while_invariants(body, loop_invs, pre_linter, lm)

    return Contracts(pre=pre, post=post, loop_invariants=loop_invs,
                     raises=raises), body, post_linter


# -- Statement folding (PyIR statements -> SnakeletIR) ---------------------

_AUG_OPS = {"+": "add", "-": "sub", "*": "mul"}


def _iterable_type_for_kind(kind: str, iterable, lw) -> str:
    """Determine iterable_type for an SFor from the classifier kind."""
    if kind == "dict":
        return "dict"
    if kind in ("str", "name"):
        if (hasattr(iterable, 'name') and hasattr(lw, '_dict_params')
                and iterable.name in lw._dict_params):
            return "dict"
        return "list"
    return kind  # "list", etc.


def _classify_iterable(it: "object") -> str:
    """Classify a for-loop iterable for a precise unsupported-feature
    diagnostic.  Returns one of: 'list', 'dict', 'set', 'str', 'generator',
    'enumerate', 'zip', 'comprehension', 'name', 'unknown'.

    See docs/finite-iterable-relations.md and docs/generator-specs.md for the
    planned verification rules for each kind."""
    cls = type(it).__name__
    if cls == "PyListLiteral":
        return "list"
    if cls == "PyDictLiteral":
        return "dict"
    if cls == "PySetLiteral":
        return "set"
    if cls == "PyConstant":
        val = getattr(it, "value", None)
        if isinstance(val, str):
            return "str"
        return "unknown"
    if cls == "PyCall":
        fname = getattr(it, "func", "")
        if fname in ("list", "tuple"):
            return "list"
        if fname == "dict":
            return "dict"
        if fname in ("set", "frozenset"):
            return "set"
        if fname == "enumerate":
            return "enumerate"
        if fname == "zip":
            return "zip"
        if fname in ("sorted", "reversed", "filter", "map"):
            return "generator"
        # A user call returning an iterable: treat as a (possibly opaque)
        # generator -- needs a GeneratorSpec contract.
        return "generator"
    if cls in ("PyListComp",):
        return "comprehension"
    if cls == "PyName":
        # A bound variable: could be a list/dict/set parameter.  Without a
        # type annotation or contract we cannot tell which.
        return "name"
    return "unknown"


# Per-kind guidance pointing at the design docs.  These features are
# recognised but not yet lowered to a proof; the diagnostic is precise so
# the pipeline can fall through to IMP (or report a clear gap) rather than
# emitting a confusing generic error.
_ITERABLE_GUIDANCE = {
    "list": ("list iteration: needs the `list` Iterable instance "
             "(fold_left over `list val`). See docs/finite-iterable-relations.md."),
    "dict": ("dict iteration: needs the `dict` Iterable instance "
             "(ordered assoc-list model + gmap lookup). "
             "See docs/finite-iterable-relations.md."),
    "set": ("set iteration: needs the `set` Iterable instance with a "
            "COMMUTATIVE fold (wp_for_set). Order-dependent bodies are "
            "rejected. See docs/finite-iterable-relations.md."),
    "str": ("string iteration: reuse the `list` instance over ascii. "
            "See docs/finite-iterable-relations.md."),
    "generator": ("generator iteration: needs a GeneratorSpec contract "
                  "(produces(result, count) + element(result, i)). "
                  "See docs/generator-specs.md."),
    "enumerate": ("enumerate(): a composed Iterable (index, element). "
                  "See docs/finite-iterable-relations.md open questions."),
    "zip": ("zip(): a composed Iterable over tuples. "
            "See docs/finite-iterable-relations.md open questions."),
    "comprehension": ("comprehension as iterable: lower the comprehension "
                      "first, then iterate its `list` model."),
    "name": ("iterating a bound variable: annotate its type (list/dict/set) "
             "or supply a contract so the right Iterable instance is chosen. "
             "See docs/finite-iterable-relations.md."),
    "unknown": ("unrecognised iterable: only range(hi)/range(lo,hi) lower "
                "directly today; list/dict/set/generator need their Iterable "
                "instances (docs/finite-iterable-relations.md, "
                "docs/generator-specs.md)."),
}


def _iterable_not_supported_msg(kind: str, var: str) -> str:
    guidance = _ITERABLE_GUIDANCE.get(kind, _ITERABLE_GUIDANCE["unknown"])
    return (f"for-loop over a {kind} (binding '{var}') is not yet lowered "
            f"to an Iris proof. {guidance}")


def _extract_while_invariants(stmts: list[ast.stmt], acc: list[list],
                                linter: ContractLinter,
                                lm: dict[str, str] | None = None) -> None:
    """Walk [stmts] depth-first, collecting invariant asserts from
    [ast.While] and [ast.For] bodies.  Each loop contributes one list of
    contract_ir.Expr nodes — NOT pre-compiled strings.  to_coq() and
    to_smt() are called lazily from the Expr when needed."""
    for s in stmts:
        if isinstance(s, ast.While):
            invs = []
            for b in s.body:
                if isinstance(b, ast.Assert):
                    linted = linter.lint_expression(b.test)
                    if linted.ir is not None:
                        invs.append(linted.ir)   # keep Expr, compile late
            acc.append(invs)
            _extract_while_invariants(s.body, acc, linter, lm)
        elif isinstance(s, ast.For):
            invs = []
            for b in s.body:
                if isinstance(b, ast.Assert):
                    linted = linter.lint_expression(b.test)
                    if linted.ir is not None:
                        invs.append(linted.ir)
            acc.append(invs)
            _extract_while_invariants(s.body, acc, linter, lm)
        elif isinstance(s, ast.If):
            _extract_while_invariants(s.body, acc, linter, lm)
            _extract_while_invariants(s.orelse, acc, linter, lm)
        elif isinstance(s, ast.Try):
            _extract_while_invariants(s.body, acc, linter, lm)
            for h in s.handlers:
                _extract_while_invariants(h.body, acc, linter, lm)


def _rewrite_body(e: SExpr, counter_var: str, fresh_loc: str) -> SExpr:
    """Rewrite var refs to Load(loc) and SLet(var=...) to Store(loc,...)."""
    if isinstance(e, SVar) and e.name == counter_var:
        return SLoad(loc=fresh_loc)
    if isinstance(e, SLet):
        if e.var == counter_var:
            return SLet(var="_",
                       value=SStore(loc=fresh_loc,
                                     value=_rewrite_body(e.value, counter_var, fresh_loc)),
                       body=_rewrite_body(e.body, counter_var, fresh_loc))
        return SLet(var=e.var,
                    value=_rewrite_body(e.value, counter_var, fresh_loc),
                    body=_rewrite_body(e.body, counter_var, fresh_loc))
    if isinstance(e, SBinOp):
        return SBinOp(op=e.op,
                     left=_rewrite_body(e.left, counter_var, fresh_loc),
                     right=_rewrite_body(e.right, counter_var, fresh_loc))
    if isinstance(e, SIf):
        return SIf(cond=_rewrite_body(e.cond, counter_var, fresh_loc),
                  then_branch=_rewrite_body(e.then_branch, counter_var, fresh_loc),
                  else_branch=_rewrite_body(e.else_branch, counter_var, fresh_loc))
    if isinstance(e, SSeq):
        return SSeq(exprs=[_rewrite_body(se, counter_var, fresh_loc) for se in e.exprs])
    if isinstance(e, SReturn):
        rv = _rewrite_body(e.value, counter_var, fresh_loc)
        # Wrap Load at return position in a Let for proper proof context
        if isinstance(rv, SLoad):
            tmp = f"_ret_{fresh_loc}"
            return SLet(var=tmp, value=rv, body=SReturn(value=SVar(name=tmp)))
        return SReturn(value=rv)
    return e


def _collect_var_names(e: SExpr) -> set[str]:
    """Collect all SVar names in an expression tree."""
    out: set[str] = set()
    if isinstance(e, SVar):
        out.add(e.name)
    elif isinstance(e, SLet):
        out.update(_collect_var_names(e.value))
        out.update(_collect_var_names(e.body))
    elif isinstance(e, SBinOp):
        out.update(_collect_var_names(e.left))
        out.update(_collect_var_names(e.right))
    elif isinstance(e, SIf):
        out.update(_collect_var_names(e.cond))
        out.update(_collect_var_names(e.then_branch))
        out.update(_collect_var_names(e.else_branch))
    elif isinstance(e, SSeq):
        for se in e.exprs:
            out.update(_collect_var_names(se))
    elif isinstance(e, SReturn):
        out.update(_collect_var_names(e.value))
    elif isinstance(e, SLoad):
        pass  # loc is a string, not a var
    elif isinstance(e, SStore):
        out.update(_collect_var_names(e.value))
    return out


def _rewrite_invariants(invs: list, counter_var: str,
                        cells: list[tuple[str, str]],
                        cond: SExpr) -> list:
    """Substitute variable names in invariant Expr nodes to use lemma params.

    Works at the AST level — no string manipulation.
    counter_var -> 'z', bound var -> 'bound', extras -> 'a_0', 'a_1', ...
    """
    from oracle.contract_ir import Var as CVar, BinOp as CBinOp, Logical, \
        IntLit, LenExpr, AllExpr, AnyExpr, RecursorExpr

    sub: dict[str, str] = {counter_var: "z"}
    if isinstance(cond.right, SVar):
        sub[cond.right.name] = "bound"
    extra_idx = 0
    for py_name, _ in cells:
        if py_name != counter_var:
            sub[py_name] = f"a_{extra_idx}"
            extra_idx += 1

    def rename_expr(e):
        """Recursively rename Var nodes in a contract_ir.Expr."""
        if hasattr(e, 'kind') and e.kind == "var" and e.name in sub:
            return CVar(name=sub[e.name])
        # Recurse into children
        if hasattr(e, 'kind') and e.kind == "binop":
            new_left = rename_expr(e.left)
            new_right = rename_expr(e.right)
            if new_left is e.left and new_right is e.right:
                return e
            return CBinOp(op=e.op, left=new_left, right=new_right)
        if hasattr(e, 'kind') and e.kind == "logical":
            new_ops = [rename_expr(o) for o in e.operands]
            if all(a is b for a, b in zip(new_ops, e.operands)):
                return e
            return Logical(op=e.op, operands=new_ops)
        if hasattr(e, 'kind') and e.kind == "len":
            new_name = sub.get(e.name, e.name)
            if new_name == e.name:
                return e
            return type(e)(name=new_name)
        # Default: return unchanged
        return e

    return [rename_expr(inv) for inv in invs]


def _promote_locals(cond: SExpr, body: SExpr, lw) \
        -> Optional[tuple[str, list[tuple[str, str]], SExpr, SExpr]]:
    """Promote ALL local variables modified in the while body to heap cells.

    Returns (counter_var, [(py_name, cell_name)], heap_body, heap_cond)
    or None if not a promotable while loop.
    """
    if not (isinstance(cond, SBinOp) and cond.op == "lt"
            and isinstance(cond.left, SVar)):
        return None
    counter_var = cond.left.name
    # Only promote symbolic bounds
    if isinstance(cond.right, SLit) and cond.right.lit_type == "int":
        return None
    # Collect all variables assigned (SLet LHS) in the body
    assigned = _collect_assigned_vars(body)
    # Must include the counter variable
    if counter_var not in assigned:
        return None
    # Allocate fresh heap cell names matching heap_alloc's fresh "l" pattern:
    # counter gets "l", subsequent cells get "l0", "l1", ...
    cells: list[tuple[str, str]] = []  # (py_name, cell_name)
    extra_count = 0
    for v in sorted(assigned):
        if v == counter_var:
            cells.append((v, "l"))
        else:
            cells.append((v, f"l{extra_count}"))
            extra_count += 1
    # Build cell_name → py_name map for rewriting
    cell_of = {py: cl for py, cl in cells}
    # Rewrite condition: counter becomes load from its cell
    heap_cond = SBinOp(op="lt",
                       left=SLoad(loc=cell_of[counter_var]),
                       right=cond.right)
    # Rewrite body: all assigned vars become load/store to their cells
    heap_body = _rewrite_multi_body(body, cell_of)
    if not any(_contains_store_of(heap_body, cl) for _, cl in cells):
        return None
    return (counter_var, cells, heap_body, heap_cond)


def _collect_assigned_vars(e: SExpr) -> set[str]:
    """Collect all variable names that appear on the LHS of an SLet."""
    out: set[str] = set()
    if isinstance(e, SLet):
        out.add(e.var)
        out.update(_collect_assigned_vars(e.value))
        out.update(_collect_assigned_vars(e.body))
    elif isinstance(e, SBinOp):
        out.update(_collect_assigned_vars(e.left))
        out.update(_collect_assigned_vars(e.right))
    elif isinstance(e, SIf):
        out.update(_collect_assigned_vars(e.cond))
        out.update(_collect_assigned_vars(e.then_branch))
        out.update(_collect_assigned_vars(e.else_branch))
    elif isinstance(e, SSeq):
        for se in e.exprs:
            out.update(_collect_assigned_vars(se))
    elif isinstance(e, SReturn):
        out.update(_collect_assigned_vars(e.value))
    return out


def _rewrite_multi_body(e: SExpr, cell_of: dict[str, str]) -> SExpr:
    """Rewrite all var refs in [cell_of] to Load/Store."""
    if isinstance(e, SVar) and e.name in cell_of:
        return SLoad(loc=cell_of[e.name])
    if isinstance(e, SLet):
        if e.var in cell_of:
            cl = cell_of[e.var]
            return SLet(var="_",
                       value=SStore(loc=cl,
                                     value=_rewrite_multi_body(e.value, cell_of)),
                       body=_rewrite_multi_body(e.body, cell_of))
        return SLet(var=e.var,
                    value=_rewrite_multi_body(e.value, cell_of),
                    body=_rewrite_multi_body(e.body, cell_of))
    if isinstance(e, SBinOp):
        return SBinOp(op=e.op,
                     left=_rewrite_multi_body(e.left, cell_of),
                     right=_rewrite_multi_body(e.right, cell_of))
    if isinstance(e, SIf):
        return SIf(cond=_rewrite_multi_body(e.cond, cell_of),
                  then_branch=_rewrite_multi_body(e.then_branch, cell_of),
                  else_branch=_rewrite_multi_body(e.else_branch, cell_of))
    if isinstance(e, SSeq):
        return SSeq(exprs=[_rewrite_multi_body(se, cell_of) for se in e.exprs])
    if isinstance(e, SReturn):
        rv = _rewrite_multi_body(e.value, cell_of)
        if isinstance(rv, SLoad):
            tmp = "_ret"
            return SLet(var=tmp, value=rv, body=SReturn(value=SVar(name=tmp)))
        return SReturn(value=rv)
    return e


def _contains_store_of(e: SExpr, loc: str) -> bool:
    if isinstance(e, SStore) and e.loc == loc:
        return True
    if isinstance(e, SLet):
        return (_contains_store_of(e.value, loc)
                or _contains_store_of(e.body, loc))
    if isinstance(e, SBinOp):
        return (_contains_store_of(e.left, loc)
                or _contains_store_of(e.right, loc))
    if isinstance(e, SSeq):
        return any(_contains_store_of(se, loc) for se in e.exprs)
    if isinstance(e, SIf):
        return (_contains_store_of(e.cond, loc)
                or _contains_store_of(e.then_branch, loc)
                or _contains_store_of(e.else_branch, loc))
    if isinstance(e, SReturn):
        return _contains_store_of(e.value, loc)
    return False


def collect_inv_obligations(proof) -> list[tuple]:
    """Collect invariant update obligations from all WhileInv nodes.

    Returns (wi, inv_idx, coq_prop, smt_hyps, smt_conc) tuples.
    All SMT strings come from expr.to_smt() — no regex, no string parsing.
    """
    from oracle.iris_proof_gen import WhileInv
    from oracle.contract_ir import Var as CVar, BinOp as CBinOp, IntLit

    def subst_body_update(e):
        """Replace Var('z') -> z+1 AND a_i -> a_i + (z+1) (body update)."""
        import re as _re2
        if hasattr(e, 'kind') and e.kind == "var":
            if e.name == "z":
                return CBinOp(op="+", left=CVar(name="z"), right=IntLit(value=1))
            for m in _re2.finditer(r'^a_(\d+)$', e.name):
                idx = int(m.group(1))
                if idx >= 0:
                    return CBinOp(op="+",
                                  left=CVar(name=e.name),
                                  right=CBinOp(op="+",
                                               left=CVar(name="z"),
                                               right=IntLit(value=1)))
            return e
        if hasattr(e, 'kind') and e.kind == "binop":
            return CBinOp(op=e.op,
                         left=subst_body_update(e.left),
                         right=subst_body_update(e.right))
        if hasattr(e, 'kind') and e.kind == "logical":
            return Logical(op=e.op, operands=[subst_body_update(o) for o in e.operands])
        return e

    obligations: list[tuple] = []

    def walk(nodes):
        for n in nodes:
            if isinstance(n, WhileInv) and n.invariant_exprs and n.cell_name == "l":
                extra = n.extra_cells or []
                for j, expr in enumerate(n.invariant_exprs):
                    # inv_new: substitute z -> z+1 in the Expr AST
                    inv_new_expr = subst_body_update(expr)
                    # Coq and SMT from the AST — late compilation, no strings
                    inv_coq = expr.to_coq()
                    inv_new_coq = inv_new_expr.to_coq()
                    inv_smt = expr.to_smt()
                    inv_new_smt = inv_new_expr.to_smt()
                    extra_params = "".join(f" (a_{i} : Z)" for i in range(len(extra)))
                    coq_prop = (
                        f"forall (z : Z){extra_params} (bound : Z), "
                        f"Z.le z bound -> z < bound -> {inv_coq} -> {inv_new_coq}")
                    smt_hyps = ["(<= z bound)", "(< z bound)", inv_smt]
                    smt_conc = inv_new_smt
                    obligations.append((n, j, coq_prop, smt_hyps, smt_conc))
            if hasattr(n, 'arms'):
                for arm in n.arms: walk(arm)
            if hasattr(n, 'body_stages'):
                walk(n.body_stages)

    walk(proof.stages)
    return obligations


def discharge_inv_obligations(proof, axiom_offset: int = 0) -> list[str]:
    """Send all invariant update obligations to SMT and populate
    WhileInv.inv_axiom_indices.  Returns new axiom Coq Prop strings."""
    obligations = collect_inv_obligations(proof)
    new_axioms: list[str] = []
    for wi, j, coq_prop, smt_hyps, smt_conc in obligations:
        # SMT query built directly from to_smt() output — no string parsing
        verified = _smt_check(smt_hyps, smt_conc,
                               extra_vars=["z", "bound"] + [f"a_{i}" for i in range(len(wi.extra_cells))])
        if not verified:
            continue
        axidx = axiom_offset + len(new_axioms)
        new_axioms.append(coq_prop)
        wi.inv_axiom_indices.extend([-1] * (j + 1 - len(wi.inv_axiom_indices)))
        wi.inv_axiom_indices[j] = axidx
    return new_axioms


def _smt_check(hyps: list[str], conc: str, extra_vars: list[str] | None = None) -> bool:
    """Check UNSAT of (hyps /\ not conc) using cvc4/z3.  All strings are
    already SMT-LIB format (produced by contract_ir.Expr.to_smt())."""
    import subprocess, tempfile, shutil, os
    solver = next((s for s in ("cvc4", "z3", "cvc5") if shutil.which(s)), None)
    if not solver:
        return False
    import re
    # Collect variable names from hypotheses and conclusion
    all_text = " ".join(hyps) + " " + conc
    vars_found = set(re.findall(r'\b([a-z][a-z0-9_]*)\b', all_text))
    KEYWORDS = {'and', 'or', 'not', 'true', 'false', 'mod', 'div', 'abs'}
    vars_found -= KEYWORDS
    if extra_vars:
        vars_found.update(extra_vars)
    lines = ["(set-logic QF_NIA)"]
    for v in sorted(vars_found):
        lines.append(f"(declare-fun {v} () Int)")
    for h in hyps:
        lines.append(f"(assert {h})")
    lines.append(f"(assert (not {conc}))")
    lines.append("(check-sat)")
    smt_src = "\n".join(lines)
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(smt_src); tf = f.name
    try:
        r = subprocess.run([solver, tf], capture_output=True, text=True, timeout=15)
        return "unsat" in r.stdout
    except Exception:
        return False
    finally:
        try: os.unlink(tf)
        except OSError: pass


def _verify_coq_prop_with_smt(coq_prop: str) -> bool:
    """Send a universally-quantified Coq Z implication to the SMT solver.
    Returns True if UNSAT (i.e., the proposition is valid)."""
    import re, subprocess, tempfile, shutil, os

    solver = next((s for s in ("cvc4", "z3", "cvc5") if shutil.which(s)), None)
    if not solver:
        return False

    # Strip forall binders
    prop = coq_prop.strip()
    var_names: list[str] = []
    m = re.match(r'^forall\s+(.*?),\s*(.+)$', prop, re.DOTALL)
    if m:
        binders_str, body = m.group(1).strip(), m.group(2).strip()
        for binder in re.finditer(r'\((\w+)\s*:\s*Z\)', binders_str):
            var_names.append(binder.group(1))
    else:
        body = prop

    # Split on -> to get hypotheses and conclusion
    parts = [p.strip() for p in re.split(r'\s*->\s*', body)]
    if len(parts) < 2:
        return False
    hyps, concl = parts[:-1], parts[-1]

    def to_smt(e: str) -> str:
        """Convert a Coq Z expression to SMT-LIB. Handles the subset
        generated by our invariant rewriting."""
        e = e.strip().strip('()')
        e = e.strip()
        # Z.le a b → (<= a b)
        m = re.match(r'^Z\.le\s+(\S+)\s+(\S+)$', e)
        if m:
            return f"(<= {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # Z.lt a b → (< a b)
        m = re.match(r'^Z\.lt\s+(\S+)\s+(\S+)$', e)
        if m:
            return f"(< {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # a = b (equality)
        m = re.match(r'^(.*?)\s*=\s*(.+)$', e)
        if m:
            return f"(= {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # a < b
        m = re.match(r'^(.*?)\s*<\s*(.+)$', e)
        if m:
            return f"(< {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # a <= b
        m = re.match(r'^(.*?)\s*<=\s*(.+)$', e)
        if m:
            return f"(<= {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # (a op b) — binary arithmetic in parens
        m = re.match(r'^\((.+)\)$', e)
        if m:
            return to_smt(m.group(1))
        # a + b
        m = re.match(r'^(.*?)\s*\+\s*(.+)$', e)
        if m:
            return f"(+ {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # a - b
        m = re.match(r'^(.*?)\s*-\s*(.+)$', e)
        if m:
            return f"(- {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # a * b
        m = re.match(r'^(.*?)\s*\*\s*(.+)$', e)
        if m:
            return f"(* {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # a / b (integer division)
        m = re.match(r'^(.*?)\s*/\s*(.+)$', e)
        if m:
            return f"(div {to_smt(m.group(1))} {to_smt(m.group(2))})"
        # Literal or variable
        return e.strip()

    from oracle.smt_export import _expr_to_smt as _old_smt
    def convert_hyp(h: str) -> str | None:
        h = h.strip()
        # Z.le a b
        m = re.match(r'^Z\.le\s+(\S+)\s+(\S+)$', h)
        if m:
            return f"(<= {m.group(1)} {m.group(2)})"
        # a < b or a = b etc
        try:
            return _old_smt(h)
        except Exception:
            return None

    lines = ["(set-logic QF_NIA)"]
    for v in var_names:
        lines.append(f"(declare-fun {v} () Int)")

    # Add hypotheses
    for h in hyps:
        s = convert_hyp(h.strip("() "))
        if s:
            lines.append(f"(assert {s})")

    # Negate conclusion
    try:
        c = _old_smt(concl.strip("() "))
    except Exception:
        c = None
    if not c:
        return False
    lines.append(f"(assert (not {c}))")
    lines.append("(check-sat)")
    smt_src = "\n".join(lines)

    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(smt_src); tf = f.name
    try:
        r = subprocess.run([solver, tf], capture_output=True, text=True, timeout=15)
        return "unsat" in r.stdout
    except Exception:
        return False
    finally:
        try: os.unlink(tf)
        except OSError: pass


def _fold(stmts: list[PyStmt], lw: IrisLowerer,
           invs_iter: "object | None" = None) -> SExpr:
    """..."""
    def next_invs() -> list[str]:
        if invs_iter is None:
            return []
        try:
            return next(invs_iter)  # type: ignore[arg-type]
        except StopIteration:
            return []
    if not stmts:
        return SLit(lit_type="unit", value="")
    s, rest = stmts[0], stmts[1:]

    if isinstance(s, PyAssert):
        return _fold(rest, lw, invs_iter=invs_iter)

    if isinstance(s, PyAssign):
        rhs = lw.lower_expr(s.value)
        if rhs is None:
            raise IrisGenError(
                f"cannot lower assignment to '{s.target}'")
        # Mutable empty collections need heap allocation (sets are value types)
        if isinstance(rhs, SLit) and rhs.lit_type in ("list", "dict"):
            if not rhs.elements:
                rhs = SAlloc(value=rhs)
        if isinstance(rhs, SLit) and rhs.lit_type == "set":
            lw._set_vars.add(s.target)
        if not rest:
            return SLet(var=s.target, value=rhs, body=SVar(name=s.target))
        return SLet(var=s.target, value=rhs, body=_fold(rest, lw, invs_iter=invs_iter))

    if isinstance(s, PyAugAssign):
        if s.op not in _AUG_OPS:
            raise IrisGenError(f"unsupported augmented op: {s.op}")
        rhs = lw.lower_expr(s.value)
        if rhs is None:
            raise IrisGenError(
                f"cannot lower augmented assignment to '{s.target}'")
        binop = SBinOp(op=_AUG_OPS[s.op], left=SVar(name=s.target),
                       right=rhs)
        body = _fold(rest, lw, invs_iter=invs_iter) if rest else SVar(name=s.target)
        return SLet(var=s.target, value=binop, body=body)

    if isinstance(s, PyReturn):
        if s.value is None:
            return SLit(lit_type="unit", value="")
        val = lw.lower_expr(s.value)
        if val is None:
            raise IrisGenError("cannot lower return expression")
        return val

    if isinstance(s, PyIf):
        cond = lw.lower_expr(s.test)
        if cond is None:
            raise IrisGenError("cannot lower if-condition")
        then_b = _fold(list(s.body) + rest, lw, invs_iter=invs_iter)
        else_b = _fold(list(s.orelse) + rest, lw, invs_iter=invs_iter)
        return SIf(cond=cond, then_branch=then_b, else_branch=else_b)

    if isinstance(s, PyWhile):
        cond = lw.lower_expr(s.test)
        if cond is None:
            raise IrisGenError("cannot lower while-condition")
        invs = next_invs()
        body = _fold(list(s.body), lw, invs_iter=invs_iter)
        rest_e = _fold(rest, lw, invs_iter=invs_iter)
        # Promote ALL local variables in the body to heap cells
        promoted = _promote_locals(cond, body, lw)
        if promoted is not None:
            counter_var, cells, heap_body, heap_cond = promoted
            # Rewrite invariants to reference lemma parameters
            if invs:
                invs = _rewrite_invariants(invs, counter_var, cells, cond)
        if promoted is not None:
            counter_var, cells, heap_body, heap_cond = promoted
            cell_of = {py: cl for py, cl in cells}
            # Rewrite rest of function too
            heap_rest = _rewrite_multi_body(rest_e, cell_of)
            # Wrap naked Load in a Let for proper proof context
            if isinstance(heap_rest, SLoad):
                tmp = "_ret"
                heap_rest = SLet(var=tmp, value=heap_rest, body=SVar(name=tmp))
            # Build: Let cell_1 = Alloc init_1 in Let cell_2 = Alloc init_2 in
            #        Let "_" = While ... in rest
            alloc_body = SLet(var="_",
                              value=SWhile(cond=heap_cond,
                                            body=heap_body,
                                            invariants=invs),
                              body=heap_rest)
            for py_name, cell_name in cells:
                alloc_body = SLet(var=cell_name,
                                  value=SAlloc(value=SLit(lit_type="int", value="0")),
                                  body=alloc_body)
            return alloc_body
        return SLet(var="_", value=SWhile(cond=cond, body=body,
                                           invariants=invs),
                    body=rest_e)

    if isinstance(s, PyExprStmt):
        val = lw.lower_expr(s.expr)
        if val is None:
            raise IrisGenError("cannot lower expression statement")
        # Value-type list/set mutation: SBinOp("append"/"set_add", SVar(xs), v)
        if (isinstance(val, SBinOp) and val.op in ("append", "set_add", "dict_set")
                and isinstance(val.left, SVar)):
            root = lw._rename_root.get(val.left.name, val.left.name)
            if root in lw._list_params or root in lw._set_vars:
                fresh = lw._var_renames.get(root, root)
                # Discard the original expression's sv (it's a diagnostic
                # node); the body uses the fresh var name.
                rest_e = _fold(rest, lw, invs_iter=invs_iter) if rest else SVar(name=fresh)
                return SLet(var=fresh, value=val, body=rest_e)
        if not rest:
            return val
        return SLet(var="_", value=val, body=_fold(rest, lw, invs_iter=invs_iter))

    if isinstance(s, PyRaise):
        val = lw.lower_stmt(s)
        if val is None:
            raise IrisGenError("cannot lower raise statement")
        if not rest:
            return val
        return SLet(var="_", value=val, body=_fold(rest, lw, invs_iter=invs_iter))

    if isinstance(s, PyTry):
        body_e = _fold(list(s.body), lw, invs_iter=invs_iter)
        if s.handlers:
            h = s.handlers[0]
            exc_name = h.exc_var or "_ex"
            handler_e = _fold(list(h.body), lw, invs_iter=invs_iter)
            if not rest:
                return STry(body=body_e, exc_var=exc_name,
                            handler=handler_e)
            return SLet(var="_", value=STry(body=body_e, exc_var=exc_name,
                                            handler=handler_e),
                        body=_fold(rest, lw, invs_iter=invs_iter))
        if not rest:
            return body_e
        return SLet(var="_", value=body_e, body=_fold(rest, lw, invs_iter=invs_iter))

    if isinstance(s, PyFor):
        # Desugar: for x in range(lo, hi): body
        #   → x_ivar = lo; while x_ivar < hi: body'; x_ivar += 1
        # The init binds the index variable, then the while loop scopes
        # over the continuation (the rest of the function after the for).
        range_call = s.iterable
        lo_val = None
        hi_val = None
        if (isinstance(range_call, PyCall) and range_call.func == "range"
                and 1 <= len(range_call.args) <= 2):
            lo_val = lw.lower_expr(range_call.args[0])
            if len(range_call.args) >= 2:
                hi_val = lw.lower_expr(range_call.args[1])
            else:
                lo_val, hi_val = SLit(lit_type="int", value="0"), lo_val
        if hi_val is None:
            # Not a range(): try list-iteration via the For primitive.
            # The iterable must lower to a value that evaluates to a LitList
            # (a list literal, or a list-typed bound variable / parameter).
            kind = _classify_iterable(s.iterable)
            if kind in ("list", "str", "name", "dict"):
                lst_e = lw.lower_expr(s.iterable)
                if lst_e is not None:
                    # for x in lst: body  ->  For x lst (body with x bound)
                    body_e = _fold(list(s.body), lw, invs_iter=invs_iter)
                    invs = next_invs()
                    for_e = SFor(var=s.var, lst=lst_e, body=body_e,
                                 invariants=invs,
                                 iterable_type=_iterable_type_for_kind(kind, s.iterable, lw))
                    rest_e = _fold(rest, lw, invs_iter=invs_iter)
                    return SLet(var="_", value=for_e, body=rest_e)
            raise IrisGenError(_iterable_not_supported_msg(kind, s.var))
        ivar = f"_{s.var}_i"
        body_stmts = [PyAssign(target=s.var,
                               value=PyName(name=ivar)),
                      *(list(s.body)),
                      PyAugAssign(target=ivar, op="+",
                                  value=PyConstant(value=1, py_type="int"))]
        body_e = _fold(body_stmts, lw, invs_iter=invs_iter)
        while_e = SWhile(cond=SBinOp(op="lt", left=SVar(name=ivar),
                                     right=hi_val),
                         body=body_e)
        rest_e = _fold(rest, lw, invs_iter=invs_iter)
        # Chain: let ivar = lo in (while ivar < hi: ...); rest
        return SLet(var=ivar, value=lo_val,
                    body=SLet(var="_", value=while_e, body=rest_e))

    if isinstance(s, PyStoreSubscript):
        val = lw.lower_stmt(s)
        if val is None:
            raise IrisGenError("cannot lower dict subscript assignment")
        if not rest:
            return val
        return SLet(var="_", value=val, body=_fold(rest, lw, invs_iter=invs_iter))

    raise IrisGenError(
        f"unsupported statement for Iris lowering: {type(s).__name__} "
        f"(break/continue: later phases)")


# -- Parameter substitution -------------------------------------------------

def _param_type_map(fn_node: ast.FunctionDef) -> dict[str, str]:
    """Extract {param_name: python_type_name} from function annotations."""
    from oracle.shape_ir import lookup_shape
    out: dict[str, str] = {}
    for a in fn_node.args.args:
        if a.annotation:
            if isinstance(a.annotation, ast.Name):
                ptype = a.annotation.id
                # Shape registry lookup: model types get their class name
                # so the lowerer can find field definitions.
                if lookup_shape(ptype) is not None:
                    out[a.arg] = ptype  # keep class name for shape lookup
                else:
                    out[a.arg] = ptype
            elif isinstance(a.annotation, ast.Subscript):
                if isinstance(a.annotation.value, ast.Name):
                    out[a.arg] = a.annotation.value.id
    return out


def _subst_params(e: SExpr, params: set[str], bound: set[str],
                   list_params: set[str] | None = None,
                   param_types: dict[str, str] | None = None) -> SExpr:
    """Replace free references to function parameters with Coq-level
    binders.  The Coq value type is determined by the parameter's type
    annotation (defaults to Int).  List params (in list_params) become
    value-level SLit that print as (Val name).
    Respects shadowing by let-bound program variables."""
    lp = list_params or set()
    pt = param_types or {}
    if isinstance(e, SVar):
        if e.name in params and e.name not in bound:
            if e.name in lp:
                return SLit(lit_type="val", value=e.name)
            ptype = pt.get(e.name, "int")
            if ptype == "float":
                return SLit(lit_type="float_param", value=e.name)
            if ptype in ("int", "bool"):
                return SLit(lit_type="int", value=e.name)
            return SLit(lit_type="val", value=e.name)
        return e
    if isinstance(e, SLit):
        return e
    if isinstance(e, SBinOp):
        return SBinOp(op=e.op,
                      left=_subst_params(e.left, params, bound, lp, pt),
                      right=_subst_params(e.right, params, bound, lp, pt))
    if isinstance(e, SLet):
        return SLet(var=e.var,
                    value=_subst_params(e.value, params, bound, lp, pt),
                    body=_subst_params(e.body, params, bound | {e.var}, lp, pt))
    if isinstance(e, SIf):
        return SIf(cond=_subst_params(e.cond, params, bound, lp, pt),
                   then_branch=_subst_params(e.then_branch, params, bound, lp, pt),
                   else_branch=_subst_params(e.else_branch, params, bound, lp, pt))
    if isinstance(e, SWhile):
        return SWhile(cond=_subst_params(e.cond, params, bound, lp, pt),
                      body=_subst_params(e.body, params, bound, lp, pt),
                      invariants=e.invariants)
    if isinstance(e, SFor):
        return SFor(var=e.var,
                    lst=_subst_params(e.lst, params, bound, lp, pt),
                    body=_subst_params(e.body, params, bound | {e.var}, lp, pt),
                    invariants=e.invariants,
                    iterable_type=e.iterable_type)
    if isinstance(e, SApp):
        return SApp(func=e.func,
                    args=[_subst_params(a, params, bound, lp, pt) for a in e.args])
    if isinstance(e, SAlloc):
        return SAlloc(value=_subst_params(e.value, params, bound, lp, pt))
    if isinstance(e, SStore):
        return SStore(loc=e.loc, value=_subst_params(e.value, params, bound, lp, pt))
    if isinstance(e, SLoad):
        return e
    if isinstance(e, SReturn):
        return _subst_params(e.value, params, bound, lp, pt)
    if isinstance(e, SDictGet):
        return SDictGet(loc=e.loc,
                        key=_subst_params(e.key, params, bound, lp, pt))
    if isinstance(e, SDictSet):
        return SDictSet(loc=e.loc,
                        key=_subst_params(e.key, params, bound, lp, pt),
                        value=_subst_params(e.value, params, bound, lp, pt))
    if isinstance(e, SRaise):
        return SRaise(exc=_subst_params(e.exc, params, bound, lp, pt))
    if isinstance(e, STry):
        return STry(body=_subst_params(e.body, params, bound, lp, pt),
                    exc_var=e.exc_var,
                    handler=_subst_params(e.handler, params, bound, lp, pt))
    raise IrisGenError(
        f"unsupported node in parameter substitution: {type(e).__name__}")


# -- ANF normalization -------------------------------------------------------

def _is_atom(e: SExpr) -> bool:
    return isinstance(e, (SLit, SVar))


def _atomize(e: SExpr, ctr: list[int], binds: list[tuple[str, SExpr]]) -> SExpr:
    if _is_atom(e):
        return e
    sub = _anf(e, ctr)
    ctr[0] += 1
    name = f"_t{ctr[0]}"
    binds.append((name, sub))
    return SVar(name=name)


def _wrap(binds: list[tuple[str, SExpr]], core: SExpr) -> SExpr:
    for name, ex in reversed(binds):
        core = SLet(var=name, value=ex, body=core)
    return core


def _anf(e: SExpr, ctr: list[int]) -> SExpr:
    """Normalize so call arguments and binop operands are atoms.

    SnakeletLang's evaluation contexts require the other binop operand
    to be a value, so a binop with two non-value operands is stuck --
    ANF makes the generated program well-evaluating by construction.
    """
    if _is_atom(e):
        return e
    if isinstance(e, SReturn):
        return _anf(e.value, ctr)
    if isinstance(e, SBinOp):
        binds: list[tuple[str, SExpr]] = []
        left = _atomize(e.left, ctr, binds)
        right = _atomize(e.right, ctr, binds)
        return _wrap(binds, SBinOp(op=e.op, left=left, right=right))
    if isinstance(e, SApp):
        binds = []
        args = [_atomize(a, ctr, binds) for a in e.args]
        return _wrap(binds, SApp(func=e.func, args=args))
    if isinstance(e, SLoad):
        return e
    if isinstance(e, SAlloc):
        binds: list[tuple[str, SExpr]] = []
        val = _atomize(e.value, ctr, binds)
        return _wrap(binds, SAlloc(value=val))
    if isinstance(e, SStore):
        binds: list[tuple[str, SExpr]] = []
        val = _atomize(e.value, ctr, binds)
        return _wrap(binds, SStore(loc=e.loc, value=val))
    if isinstance(e, SDictGet):
        binds: list[tuple[str, SExpr]] = []
        key = _atomize(e.key, ctr, binds)
        return _wrap(binds, SDictGet(loc=e.loc, key=key))
    if isinstance(e, SDictSet):
        binds: list[tuple[str, SExpr]] = []
        key = _atomize(e.key, ctr, binds)
        val = _atomize(e.value, ctr, binds)
        return _wrap(binds, SDictSet(loc=e.loc, key=key, value=val))
    if isinstance(e, SLet):
        return SLet(var=e.var, value=_anf(e.value, ctr),
                    body=_anf(e.body, ctr))
    if isinstance(e, SIf):
        binds = []
        cond = e.cond
        if isinstance(cond, SBinOp):
            left = _atomize(cond.left, ctr, binds)
            right = _atomize(cond.right, ctr, binds)
            cond = SBinOp(op=cond.op, left=left, right=right)
        elif not _is_atom(cond):
            cond = _atomize(cond, ctr, binds)
        return _wrap(binds, SIf(cond=cond,
                                then_branch=_anf(e.then_branch, ctr),
                                else_branch=_anf(e.else_branch, ctr)))
    if isinstance(e, SWhile):
        cond = e.cond
        binds: list[tuple[str, SExpr]] = []
        # Hoist non-atom/non-load condition operands into let-bindings
        # before the while (sound when the operand is loop-invariant,
        # which is the common case for len/const expressions).
        if isinstance(cond, SBinOp):
            if not _is_atom(cond.left) and not isinstance(cond.left, SLoad):
                v = f"_whl{ctr[0]}"; ctr[0] += 1
                binds.append((v, cond.left))
                cond = SBinOp(op=cond.op, left=SVar(v), right=cond.right)
            if not _is_atom(cond.right) and not isinstance(cond.right, SLoad):
                v = f"_whl{ctr[0]}"; ctr[0] += 1
                binds.append((v, cond.right))
                cond = SBinOp(op=cond.op, left=cond.left, right=SVar(v))
        return _wrap(binds, SWhile(cond=cond, body=_anf(e.body, ctr),
                                   invariants=e.invariants))
    if isinstance(e, SFor):
        # The list operand must already be a value (atom): a list literal or
        # a bound variable.  The For evaluation context evaluates it, but the
        # generated proof expects a Val (LitList ...) head.
        if not _is_atom(e.lst):
            raise IrisGenError(
                "for-loop iterable must be an atom (list literal or "
                "variable); lower complex iterables to a let-bound list first")
        return SFor(var=e.var, lst=e.lst, body=_anf(e.body, ctr),
                    invariants=e.invariants,
                    iterable_type=e.iterable_type)
    if isinstance(e, SRaise):
        binds: list[tuple[str, SExpr]] = []
        exc = _atomize(e.exc, ctr, binds)
        return _wrap(binds, SRaise(exc=exc))
    if isinstance(e, STry):
        # Atomize the body so the Try body is always a value/atom.
        # This avoids needing TryCtx in reshape_expr.
        binds: list[tuple[str, SExpr]] = []
        body_atom = _atomize(e.body, ctr, binds)
        handler_nf = _anf(e.handler, ctr)
        return _wrap(binds, STry(body=body_atom, exc_var=e.exc_var,
                                 handler=handler_nf))
    raise IrisGenError(f"unsupported node in ANF: {type(e).__name__}")


# -- Validation --------------------------------------------------------------

def _validate_ops(e: SExpr) -> None:
    if isinstance(e, SBinOp):
        if e.op not in _SUPPORTED_OPS:
            raise IrisGenError(
                f"binop '{e.op}' is not in the supported integer fragment "
                f"({sorted(_SUPPORTED_OPS)})")
        _validate_ops(e.left)
        _validate_ops(e.right)
    elif isinstance(e, SLet):
        _validate_ops(e.value)
        _validate_ops(e.body)
    elif isinstance(e, SIf):
        _validate_ops(e.cond)
        _validate_ops(e.then_branch)
        _validate_ops(e.else_branch)
    elif isinstance(e, SWhile):
        _validate_ops(e.cond)
        _validate_ops(e.body)
    elif isinstance(e, SFor):
        _validate_ops(e.lst)
        _validate_ops(e.body)
    elif isinstance(e, SApp):
        for a in e.args:
            _validate_ops(a)
    elif isinstance(e, SAlloc):
        _validate_ops(e.value)
    elif isinstance(e, SStore):
        _validate_ops(e.value)
    elif isinstance(e, SLoad):
        pass
    elif isinstance(e, SReturn):
        _validate_ops(e.value)
    elif isinstance(e, SDictGet):
        _validate_ops(e.key)
    elif isinstance(e, SDictSet):
        _validate_ops(e.key)
        _validate_ops(e.value)
    elif isinstance(e, SRaise):
        _validate_ops(e.exc)
    elif isinstance(e, STry):
        _validate_ops(e.body)
        _validate_ops(e.handler)


# -- Entry point --------------------------------------------------------------

def _detect_list_params(body: SExpr, params: set[str]) -> dict[str, str]:
    """Find params used as list for-loop iterables and assign model variable names."""
    out: dict[str, str] = {}
    def walk(e: SExpr) -> None:
        if isinstance(e, SFor):
            if isinstance(e.lst, SVar) and e.lst.name in params \
               and e.iterable_type in ("list", "str", "name"):
                out[e.lst.name] = f"M_{e.lst.name}"
            walk(e.lst)
            walk(e.body)
        elif isinstance(e, SLet):
            walk(e.value)
            walk(e.body)
        elif isinstance(e, SIf):
            walk(e.cond)
            walk(e.then_branch)
            if e.else_branch:
                walk(e.else_branch)
        elif isinstance(e, SWhile):
            walk(e.cond)
            walk(e.body)
        elif isinstance(e, SBinOp):
            walk(e.left)
            walk(e.right)
        elif isinstance(e, SApp):
            for a in e.args:
                walk(a)
        elif isinstance(e, SAlloc):
            walk(e.value)
        elif isinstance(e, SStore):
            walk(e.value)
        elif isinstance(e, SLoad):
            pass
        elif isinstance(e, SDictGet):
            walk(e.key)
        elif isinstance(e, SDictSet):
            walk(e.key)
            walk(e.value)
        elif isinstance(e, SRaise):
            walk(e.exc)
        elif isinstance(e, STry):
            walk(e.body)
            walk(e.handler)
        elif isinstance(e, (SLit, SVar)):
            pass
        else:
            raise IrisGenError(
                f"unsupported node in list-param detection: {type(e).__name__}")
    walk(body)
    return out


def _detect_dict_params(body: SExpr, params: set[str]) -> dict[str, str]:
    """Find params used as dict for-loop iterables and assign model variable names."""
    out: dict[str, str] = {}
    def walk(e: SExpr) -> None:
        if isinstance(e, SFor):
            if isinstance(e.lst, SVar) and e.lst.name in params \
               and e.iterable_type == "dict":
                out[e.lst.name] = f"kvs_{e.lst.name}"
            walk(e.lst)
            walk(e.body)
        elif isinstance(e, SLet):
            walk(e.value)
            walk(e.body)
        elif isinstance(e, SIf):
            walk(e.cond)
            walk(e.then_branch)
            if e.else_branch:
                walk(e.else_branch)
        elif isinstance(e, SWhile):
            walk(e.cond)
            walk(e.body)
        elif isinstance(e, SBinOp):
            walk(e.left)
            walk(e.right)
        elif isinstance(e, SApp):
            for a in e.args:
                walk(a)
        elif isinstance(e, SAlloc):
            walk(e.value)
        elif isinstance(e, SStore):
            walk(e.value)
        elif isinstance(e, SLoad):
            pass
        elif isinstance(e, SDictGet):
            walk(e.key)
        elif isinstance(e, SDictSet):
            walk(e.key)
            walk(e.value)
        elif isinstance(e, SRaise):
            walk(e.exc)
        elif isinstance(e, STry):
            walk(e.body)
            walk(e.handler)
        elif isinstance(e, (SLit, SVar)):
            pass
        else:
            raise IrisGenError(
                f"unsupported node in dict-param detection: {type(e).__name__}")
    walk(body)
    return out


def python_to_iris_proof(source: str,
                         table: FunTable,
                         func_name: Optional[str] = None,
                         axioms: Optional[list[str]] = None,
                         pre_overrides: Optional[dict[str, str]] = None,
                         dict_params: Optional[set[str]] = None,
                         _cwd: str = ".",
                         ) -> IrisProof:
    """Lower a Python function with assert contracts to a staged Iris proof.

    source: Python source containing the function definition.
    table: callee contract/definition table (FunTable).
    func_name: which function to verify (default: the first def).
    axioms / pre_overrides: SMT escalation inputs, passed through.
    dict_params: set of parameter names that are dicts (for for-loop detection).
    """
    tree = ast.parse(source)
    # Load the shape/enum registry so enum member refs (PaymentState.CAPTURED)
    # are resolved to their integer encodings in contract expressions.
    from oracle.shape_ir import build_shape_registry
    build_shape_registry(tree, _cwd=_cwd)
    target = None
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            if func_name is None or node.name == func_name:
                target = node
                break
    if target is None:
        raise IrisGenError(f"function '{func_name}' not found in source")

    # Detect list/dict params from type annotations (needed before
    # contract extraction for len() compilation and before lowering).
    user_dict = dict_params or set()
    ann_list_params: set[str] = set()
    for a in target.args.args:
        if a.annotation:
            if isinstance(a.annotation, ast.Subscript):
                base = None
                if isinstance(a.annotation.value, ast.Name):
                    base = a.annotation.value.id
                if base in ("list", "List"):
                    ann_list_params.add(a.arg)
                elif base in ("dict", "Dict"):
                    user_dict.add(a.arg)
            elif isinstance(a.annotation, ast.Name):
                if a.annotation.id in ("list", "List"):
                    ann_list_params.add(a.arg)
                elif a.annotation.id in ("dict", "Dict"):
                    user_dict.add(a.arg)
    ann_lm = {p: f"M_{p}" for p in ann_list_params}

    # Contracts: use ContractLinter + contract_ir_iris.
    # Build a ghost_resolver from the callee table: observer calls in
    # contracts resolve to the ghost variable names the callee's post names.
    ghost_resolver: dict[str, str] = {}
    from oracle.iris_proof_gen import OpaqueSpec
    for entry in table.values():
        if isinstance(entry, OpaqueSpec):
            ghost_resolver.update(entry.ghost_vars)
    # First parse docstring contracts and merge them into contract extraction.
    from oracle.docstring_contracts import docstring_assert_nodes
    dc_asserts = docstring_assert_nodes(target)
    # Inject docstring assertions as synthetic asserts at the top of the body
    # so extract_contracts picks them up (same as the IMP pipeline does via
    # _docstring_contract_asserts).
    for (node, klass) in dc_asserts:
        if klass == "precondition":
            target.body.insert(0, node)
        elif klass == "postcondition":
            # Insert before the last Return statement.
            for i in range(len(target.body) - 1, -1, -1):
                if isinstance(target.body[i], ast.Return):
                    target.body.insert(i, node)
                    break
    contracts, body_ast, _ = extract_contracts(source, target, list_model=ann_lm,
                                                ghost_resolver=ghost_resolver)

    # Strip docstring string-node from the body before lowering (it leaks
    # into the IR as a LitString literal otherwise).
    _is_str_expr = (
        lambda s: isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
        and isinstance(s.value.value, str))
    target.body = [s for s in target.body if not _is_str_expr(s)]

    # Body: PyIR -> SnakeletIR -> ANF
    fn = PyIRTranslator().translate_function(target)

    param_types = _param_type_map(target)
    lw = IrisLowerer(loc_map={}, func_name=fn.name, dict_params=user_dict,
                      list_params=ann_list_params,
                      param_types=param_types)
    invs_iter = iter(contracts.loop_invariants) if contracts.loop_invariants else None
    body = _fold(fn.body, lw, invs_iter=iter(contracts.loop_invariants))
    list_params = _detect_list_params(body, set(fn.params))
    detected_dict = _detect_dict_params(body, set(fn.params))
    # Merge annotation-based list params with IR-detected ones
    merged_lp: dict[str, str] = dict(list_params)
    for lp in ann_list_params:
        if lp not in merged_lp:
            merged_lp[lp] = f"M_{lp}"
    body = _subst_params(body, set(fn.params), set(),
                          set(merged_lp.keys()) | set(detected_dict.keys()),
                          param_types=param_types)
    body = _anf(body, [0])
    _validate_ops(body)

    # Build the proof first with the caller-supplied axioms
    proof = generate(
        name=fn.name,
        body=body,
        post=contracts.post,
        table=table,
        params=list(fn.params),
        pre=contracts.pre,
        axioms=list(axioms or []),
        pre_overrides=pre_overrides,
        list_params=merged_lp,
        dict_params=detected_dict,
        raises=contracts.raises,
        param_types=param_types,
    )

    # Collect invariant update obligations from all WhileInv nodes,
    # discharge via SMT in one batch, and inject as smt_ax_N axioms.
    inv_axs = discharge_inv_obligations(proof, axiom_offset=len(proof.axioms))
    proof.axioms.extend(inv_axs)

    return proof


def capture_residual(source: str,
                     table: FunTable,
                     func_name: str | None = None,
                     error_output: str = "",
                     _cwd: str = ".",
                     ) -> str | None:
    """Generate a proof and, if verification fails, produce a residual
    .v fragment showing the goal state at the failure point.

    Returns the residual as a string, or None if the proof already
    verifies (no residual needed).

    [error_output] should be the coqc stderr from a prior verification
    attempt; if empty, we run coqc internally and use its output to
    locate the failure.
    """
    import re, tempfile, subprocess, os
    proof = python_to_iris_proof(source, table, func_name=func_name,
                                 _cwd=_cwd)
    full_text = proof.emit_exn()
    if not error_output:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v',
                                         delete=False) as f:
            f.write(full_text)
            tf = f.name
        try:
            r = subprocess.run(
                ["coqc", "-R", _coq_root(), "", tf],
                capture_output=True, text=True, timeout=60)
        finally:
            try:
                os.unlink(tf)
            except OSError:
                pass
        error_output = r.stderr
        if r.returncode == 0:
            return None  # already verified

    # Parse line number from error: "File ..., line N, characters ..."
    m = re.search(r'line (\d+)', error_output)
    if not m:
        return None
    err_line = int(m.group(1))
    emit_lines = full_text.splitlines()
    # Find the LAST stage whose emit line is strictly before the error
    # line.  (The error is often at Qed, not the failing tactic.)
    stage_id = None
    for i, el in enumerate(emit_lines):
        if (i + 1) >= err_line:
            break
        s_match = re.search(r'\[\s*(\d+)\s*\]', el)
        if s_match:
            stage_id = int(s_match.group(1))
    if stage_id is None:
        return None
    return proof.emit_residual(stage_id + 1)  # capture goal AT this stage


def _coq_root() -> str:
    """Return the path to the coq source root."""
    import pathlib
    return str(pathlib.Path(__file__).parent.parent.parent / "coq")


# ---------------------------------------------------------------------------
# Fault-isolated verification (parity with pipeline.py: _verify_one)
# ---------------------------------------------------------------------------

def verify_iris_safe(source: str,
                     func_name: str,
                     table: FunTable,
                     _cwd: str = ".",
                     **kwargs) -> GoalStatus:
    """Fault-isolated Iris verification of one function.

    Wraps python_to_iris_proof + coqc compilation in try/except so
    one crashing function does not abort a batch run.
    Returns a GoalStatus with elapsed_ms, error_detail, and level.
    """
    import time
    import subprocess
    import tempfile
    import os

    t0 = time.monotonic()
    try:
        proof = python_to_iris_proof(
            source, table, func_name=func_name, _cwd=_cwd, **kwargs)
        full_text = proof.emit_exn()

        with tempfile.NamedTemporaryFile(
                mode="w", suffix=".v", delete=False) as f:
            f.write(full_text)
            tf = f.name
        try:
            r = subprocess.run(
                ["coqc", "-R", _coq_root(), "", tf],
                capture_output=True, text=True, timeout=120)
        finally:
            try:
                os.unlink(tf)
            except OSError:
                pass

        elapsed_ms = (time.monotonic() - t0) * 1000.0

        if r.returncode == 0:
            return GoalStatus(
                name=func_name,
                goal_statement=proof.post,
                level=ProofLevel.LEVEL1_LTAC,
                elapsed_ms=elapsed_ms,
                proof_method="iris_exn",
            )
        else:
            return GoalStatus(
                name=func_name,
                goal_statement=proof.post,
                level=ProofLevel.UNPROVED,
                error_detail=(r.stderr[:200] if r.stderr
                              else "coqc returned non-zero"),
                elapsed_ms=elapsed_ms,
                proof_method="iris_exn",
            )
    except Exception as exc:
        elapsed_ms = (time.monotonic() - t0) * 1000.0
        return GoalStatus(
            name=func_name,
            goal_statement="",
            level=ProofLevel.UNPROVED,
            error_detail=f"{type(exc).__name__}: {exc}",
            elapsed_ms=elapsed_ms,
            suggested_action=Action.REFACTOR,
        )


# ---------------------------------------------------------------------------
# Batch verification (parity with pipeline.py: run_pipeline)
# ---------------------------------------------------------------------------

def _enumerate_iris_functions(source: str) -> list[tuple[str, ast.FunctionDef]]:
    """Return (name, node) for top-level functions and class methods."""
    tree = ast.parse(source)
    pairs: list[tuple[str, ast.FunctionDef]] = []
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.FunctionDef):
            pairs.append((node.name, node))
        elif isinstance(node, ast.ClassDef):
            for child in ast.iter_child_nodes(node):
                if isinstance(child, ast.FunctionDef):
                    pairs.append((child.name, child))
    return pairs


def run_iris_pipeline(python_file: str,
                      table: FunTable,
                      func_name: str | None = None,
                      **kwargs) -> PipelineReport:
    """Batch-verify Iris-contracted functions in a Python file.

    Each function is verified independently via verify_iris_safe
    (fault isolation).  Returns a PipelineReport aggregating all
    GoalStatus results.
    """
    import time
    from pathlib import Path

    py_file = Path(python_file) if isinstance(python_file, str) else python_file
    source = py_file.read_text()
    func_pairs = _enumerate_iris_functions(source)

    if func_name:
        func_pairs = [(n, node) for n, node in func_pairs if n == func_name]
        if not func_pairs:
            raise IrisGenError(
                f"function '{func_name}' not found in {py_file.name}")

    t0 = time.monotonic()
    goals: list[GoalStatus] = []

    for name, _func_node in func_pairs:
        result = verify_iris_safe(
            source, name, table, _cwd=str(py_file.parent), **kwargs)
        goals.append(result)
        if result.is_proved():
            print(f"  PROVED   {name}  [{result.level.value}]")
        else:
            detail = result.error_detail or ""
            print(f"  UNPROVED {name}  {detail[:80]}")

    elapsed_ms = (time.monotonic() - t0) * 1000.0
    proved = sum(1 for g in goals if g.is_proved())

    return PipelineReport(
        source_file=str(py_file),
        total_goals=len(goals),
        proved_goals=proved,
        goals=goals,
        elapsed_total_ms=elapsed_ms,
    )


# ---------------------------------------------------------------------------
# CLI entry point (parity with pipeline.py: main)
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    """Argparse CLI for the Iris verification pipeline.

    Usage:
        python -m oracle.iris_pipeline <file> [--function F] [--json] [--quiet]

    Exit codes:
        0  all goals verified
        1  one or more goals not verified
        2  usage / file / toolchain error
    """
    import argparse
    import shutil
    import sys as _sys
    from pathlib import Path

    parser = argparse.ArgumentParser(
        prog="python -m oracle.iris_pipeline",
        description="Run Axiomander Iris verification on a Python file.",
    )
    parser.add_argument(
        "file", help="Python source file to verify")
    parser.add_argument(
        "--function", "-f", metavar="NAME", default=None,
        help="Verify only this function (default: all functions)")
    parser.add_argument(
        "--json", action="store_true", default=False,
        help="Emit JSON report to stdout instead of human text")
    parser.add_argument(
        "--quiet", "-q", action="store_true", default=False,
        help="Suppress per-function status lines")

    try:
        args = parser.parse_args(argv)
    except SystemExit:
        return 2

    if shutil.which("coqc") is None:
        print(
            "ERROR: coqc not found on PATH.\n"
            "Run `eval $(opam env)` to activate the Coq toolchain, then retry.",
            file=_sys.stderr,
        )
        return 2

    py_file = Path(args.file)
    if not py_file.exists():
        print(f"ERROR: file not found: {py_file}", file=_sys.stderr)
        return 2

    table: FunTable = {}

    try:
        report = run_iris_pipeline(str(py_file), table, func_name=args.function)
    except Exception as exc:
        print(f"ERROR: {exc}", file=_sys.stderr)
        return 2

    if args.json:
        print(report.to_json())
    elif not args.quiet:
        print(f"\n{'=' * 50}")
        print(report.summary())
        print(f"Elapsed: {report.elapsed_total_ms:.0f} ms")

    proved = sum(1 for g in report.goals if g.is_proved())
    return 0 if proved == report.total_goals else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
