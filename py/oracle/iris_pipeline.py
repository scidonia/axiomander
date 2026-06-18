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
from oracle.py_ir import (
    PyAssert, PyAssign, PyAugAssign, PyCall, PyConstant, PyExprStmt,
    PyFor, PyIf, PyName, PyRaise, PyReturn, PyStmt, PyStoreSubscript, PyTry, PyWhile,
)
from oracle.py_ir_translator import PyIRTranslator
from oracle.snakelet_ir import (
    SAlloc, SApp, SBinOp, SDictGet, SDictSet, SExpr, SIf, SLet, SLit, SLoad, SRaise, SReturn, SStore,
    STry, SVar, SWhile, SFor,
)

# Binops supported by SnakeletLang's binop_eval on integers.
_SUPPORTED_OPS = {"add", "sub", "mul", "eq", "le", "lt", "gt", "ge", "ne", "mod", "and", "or", "in", "append", "length"}


# -- Contract extraction ----------------------------------------------------

@dataclass
class Contracts:
    pre: Optional[str]
    post: str
    loop_invariants: list[list[str]] = field(default_factory=list)
    """Invariants per while loop in the function body, in order."""
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
    pre_linter = ContractLinter(params=params, context="precondition",
                                ghost_resolver=ghost_resolver)
    post_linter = ContractLinter(params=params, context="postcondition",
                                 ghost_resolver=ghost_resolver)

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


def _extract_while_invariants(stmts: list[ast.stmt], acc: list[list[str]],
                                linter: ContractLinter,
                                lm: dict[str, str] | None = None) -> None:
    """Walk [stmts] depth-first, collecting invariant asserts from
    [ast.While] and [ast.For] bodies.  Each loop contributes one list of
    Coq Prop strings (in encounter order)."""
    for s in stmts:
        if isinstance(s, ast.While):
            invs = []
            for b in s.body:
                if isinstance(b, ast.Assert):
                    linted = linter.lint_expression(b.test)
                    if linted.ir is not None:
                        invs.append(compile_precondition(linted.ir, list_model=lm))
            acc.append(invs)
            _extract_while_invariants(s.body, acc, linter, lm)
        elif isinstance(s, ast.For):
            invs = []
            for b in s.body:
                if isinstance(b, ast.Assert):
                    linted = linter.lint_expression(b.test)
                    if linted.ir is not None:
                        invs.append(compile_precondition(linted.ir, list_model=lm))
            acc.append(invs)
            _extract_while_invariants(s.body, acc, linter, lm)
        elif isinstance(s, ast.If):
            _extract_while_invariants(s.body, acc, linter, lm)
            _extract_while_invariants(s.orelse, acc, linter, lm)
        elif isinstance(s, ast.Try):
            _extract_while_invariants(s.body, acc, linter, lm)
            for h in s.handlers:
                _extract_while_invariants(h.body, acc, linter, lm)


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
        # Mutable empty collections need heap allocation
        if isinstance(rhs, SLit) and rhs.lit_type in ("list", "dict", "set"):
            if not rhs.elements:
                rhs = SAlloc(value=rhs)
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
        return SLet(var="_", value=SWhile(cond=cond, body=body,
                                          invariants=invs),
                    body=rest_e)

    if isinstance(s, PyExprStmt):
        val = lw.lower_expr(s.expr)
        if val is None:
            raise IrisGenError("cannot lower expression statement")
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
            if ptype in ("int", "bool", "float"):
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
        if a.annotation and isinstance(a.annotation, ast.Subscript):
            base = None
            if isinstance(a.annotation.value, ast.Name):
                base = a.annotation.value.id
            if base in ("list", "List"):
                ann_list_params.add(a.arg)
            elif base in ("dict", "Dict"):
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

    return generate(
        name=fn.name,
        body=body,
        post=contracts.post,
        table=table,
        params=list(fn.params),
        pre=contracts.pre,
        axioms=axioms,
        pre_overrides=pre_overrides,
        list_params=merged_lp,
        dict_params=detected_dict,
        raises=contracts.raises,
        param_types=param_types,
    )
