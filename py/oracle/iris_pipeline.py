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

from oracle.contract_ir_iris import compile_postcondition, compile_precondition
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
_SUPPORTED_OPS = {"add", "sub", "mul", "eq", "le", "lt", "gt", "ge"}


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
    pre_linter = ContractLinter(params=params, context="precondition")
    post_linter = ContractLinter(params=params, context="postcondition")

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
            pres.append(compile_precondition(linted.ir))
        body = body[1:]

    pre = None
    if len(pres) == 1:
        pre = pres[0]
    elif pres:
        pre = " /\\ ".join(f"({p})" for p in pres)

    # Assert immediately before final return = postcondition
    post = "True"
    if body and isinstance(body[-1], ast.Return):
        ret_node = body[-1]
        ret_var = None
        if isinstance(ret_node.value, ast.Name):
            ret_var = ret_node.value.id
        if (len(body) >= 2 and isinstance(body[-2], ast.Assert)
                and ret_var is not None):
            linted = post_linter.lint_expression(body[-2].test)
            if linted.ir is not None:
                post = compile_postcondition(linted.ir, ret_var)
            body = body[:-2] + [ret_node]

    # Extract loop invariants from while loops in the body
    loop_invs: list[list[str]] = []
    _extract_while_invariants(body, loop_invs, pre_linter)

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
                               linter: ContractLinter) -> None:
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
                        invs.append(compile_precondition(linted.ir))
            acc.append(invs)
            _extract_while_invariants(s.body, acc, linter)
        elif isinstance(s, ast.For):
            invs = []
            for b in s.body:
                if isinstance(b, ast.Assert):
                    linted = linter.lint_expression(b.test)
                    if linted.ir is not None:
                        invs.append(compile_precondition(linted.ir))
            acc.append(invs)
            _extract_while_invariants(s.body, acc, linter)
        elif isinstance(s, ast.If):
            _extract_while_invariants(s.body, acc, linter)
            _extract_while_invariants(s.orelse, acc, linter)
        elif isinstance(s, ast.Try):
            _extract_while_invariants(s.body, acc, linter)
            for h in s.handlers:
                _extract_while_invariants(h.body, acc, linter)


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

def _subst_params(e: SExpr, params: set[str], bound: set[str],
                   list_params: set[str] | None = None) -> SExpr:
    """Replace free references to function parameters with Coq-level
    binders: SVar("x") -> SLit("int", "x") prints as (Val (LitInt x)).
    List params (in list_params) become SLit("val", name) printing as (Val name).
    Respects shadowing by let-bound program variables."""
    lp = list_params or set()
    if isinstance(e, SVar):
        if e.name in params and e.name not in bound:
            if e.name in lp:
                return SLit(lit_type="val", value=e.name)
            return SLit(lit_type="int", value=e.name)
        return e
    if isinstance(e, SLit):
        return e
    if isinstance(e, SBinOp):
        return SBinOp(op=e.op,
                      left=_subst_params(e.left, params, bound, lp),
                      right=_subst_params(e.right, params, bound, lp))
    if isinstance(e, SLet):
        return SLet(var=e.var,
                    value=_subst_params(e.value, params, bound, lp),
                    body=_subst_params(e.body, params, bound | {e.var}, lp))
    if isinstance(e, SIf):
        return SIf(cond=_subst_params(e.cond, params, bound, lp),
                   then_branch=_subst_params(e.then_branch, params, bound, lp),
                   else_branch=_subst_params(e.else_branch, params, bound, lp))
    if isinstance(e, SWhile):
        return SWhile(cond=_subst_params(e.cond, params, bound, lp),
                      body=_subst_params(e.body, params, bound, lp),
                      invariants=e.invariants)
    if isinstance(e, SFor):
        return SFor(var=e.var,
                    lst=_subst_params(e.lst, params, bound, lp),
                    body=_subst_params(e.body, params, bound | {e.var}, lp),
                    invariants=e.invariants,
                    iterable_type=e.iterable_type)
    if isinstance(e, SApp):
        return SApp(func=e.func,
                    args=[_subst_params(a, params, bound, lp) for a in e.args])
    if isinstance(e, SAlloc):
        return SAlloc(value=_subst_params(e.value, params, bound, lp))
    if isinstance(e, SStore):
        return SStore(loc=e.loc, value=_subst_params(e.value, params, bound, lp))
    if isinstance(e, SLoad):
        return e
    if isinstance(e, SReturn):
        return _subst_params(e.value, params, bound, lp)
    if isinstance(e, SDictGet):
        return SDictGet(loc=e.loc,
                        key=_subst_params(e.key, params, bound, lp))
    if isinstance(e, SDictSet):
        return SDictSet(loc=e.loc,
                        key=_subst_params(e.key, params, bound, lp),
                        value=_subst_params(e.value, params, bound, lp))
    if isinstance(e, SRaise):
        return SRaise(exc=_subst_params(e.exc, params, bound, lp))
    if isinstance(e, STry):
        return STry(body=_subst_params(e.body, params, bound, lp),
                    exc_var=e.exc_var,
                    handler=_subst_params(e.handler, params, bound, lp))
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
        # The condition is re-evaluated each iteration: hoisting any
        # part of it outside the While would change semantics.  The
        # supported shape is a binop whose operands are atoms or loads
        # (loads are valid ectx redexes against a value operand).
        cond = e.cond
        if isinstance(cond, SBinOp):
            left_ok = _is_atom(cond.left) or isinstance(cond.left, SLoad)
            right_ok = _is_atom(cond.right) or isinstance(cond.right, SLoad)
            if not (left_ok and right_ok) or \
               (isinstance(cond.left, SLoad) and isinstance(cond.right, SLoad)):
                raise IrisGenError(
                    "while condition must be a binop over atoms with at "
                    "most one load (value-restricted ectx)")
        elif not _is_atom(cond):
            raise IrisGenError(
                "while condition must be an atom or a simple binop")
        return SWhile(cond=cond, body=_anf(e.body, ctr),
                      invariants=e.invariants)
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
                         ) -> IrisProof:
    """Lower a Python function with assert contracts to a staged Iris proof.

    source: Python source containing the function definition.
    table: callee contract/definition table (FunTable).
    func_name: which function to verify (default: the first def).
    axioms / pre_overrides: SMT escalation inputs, passed through.
    dict_params: set of parameter names that are dicts (for for-loop detection).
    """
    tree = ast.parse(source)
    target = None
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            if func_name is None or node.name == func_name:
                target = node
                break
    if target is None:
        raise IrisGenError(f"function '{func_name}' not found in source")

    # Contracts: use ContractLinter + contract_ir_iris
    contracts, body_ast, _ = extract_contracts(source, target)

    # Body: PyIR -> SnakeletIR -> ANF
    fn = PyIRTranslator().translate_function(target)
    user_dict = dict_params or set()
    lw = IrisLowerer(loc_map={}, func_name=fn.name, dict_params=user_dict)
    invs_iter = iter(contracts.loop_invariants) if contracts.loop_invariants else None
    body = _fold(fn.body, lw, invs_iter=iter(contracts.loop_invariants))
    list_params = _detect_list_params(body, set(fn.params))
    detected_dict = _detect_dict_params(body, set(fn.params))
    body = _subst_params(body, set(fn.params), set(),
                         set(list_params.keys()) | set(detected_dict.keys()))
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
        list_params=list_params,
        dict_params=detected_dict,
        raises=contracts.raises,
    )
