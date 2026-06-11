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
from dataclasses import dataclass
from typing import Optional

from oracle.contract_ir_iris import compile_postcondition, compile_precondition
from oracle.contract_linter import ContractLinter
from oracle.iris_lowerer import IrisLowerer
from oracle.iris_proof_gen import (
    FunTable, IrisGenError, IrisProof, generate,
)
from oracle.py_ir import (
    PyAssert, PyAssign, PyAugAssign, PyCall, PyConstant, PyExprStmt,
    PyFor, PyIf, PyName, PyRaise, PyReturn, PyStmt, PyTry, PyWhile,
)
from oracle.py_ir_translator import PyIRTranslator
from oracle.snakelet_ir import (
    SAlloc, SApp, SBinOp, SExpr, SIf, SLet, SLit, SLoad, SReturn, SStore,
    STry, SVar, SWhile,
)

# Binops supported by SnakeletLang's binop_eval on integers.
_SUPPORTED_OPS = {"add", "sub", "mul", "eq", "le", "lt", "gt", "ge"}


# -- Contract extraction ----------------------------------------------------

@dataclass
class Contracts:
    pre: Optional[str]
    post: str


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

    return Contracts(pre=pre, post=post), body, post_linter


# -- Statement folding (PyIR statements -> SnakeletIR) ---------------------

_AUG_OPS = {"+": "add", "-": "sub", "*": "mul"}


def _fold(stmts: list[PyStmt], lw: IrisLowerer) -> SExpr:
    """Continuation-style fold: each binding scopes over the rest.

    A conditional whose branches do not both return duplicates the
    continuation into each arm (path duplication, mirroring the staged
    generator's case splits).
    """
    if not stmts:
        return SLit(lit_type="unit", value="")
    s, rest = stmts[0], stmts[1:]

    if isinstance(s, PyAssert):
        return _fold(rest, lw)

    if isinstance(s, PyAssign):
        rhs = lw.lower_expr(s.value)
        if rhs is None:
            raise IrisGenError(
                f"cannot lower assignment to '{s.target}'")
        if not rest:
            return SLet(var=s.target, value=rhs, body=SVar(name=s.target))
        return SLet(var=s.target, value=rhs, body=_fold(rest, lw))

    if isinstance(s, PyAugAssign):
        if s.op not in _AUG_OPS:
            raise IrisGenError(f"unsupported augmented op: {s.op}")
        rhs = lw.lower_expr(s.value)
        if rhs is None:
            raise IrisGenError(
                f"cannot lower augmented assignment to '{s.target}'")
        binop = SBinOp(op=_AUG_OPS[s.op], left=SVar(name=s.target),
                       right=rhs)
        body = _fold(rest, lw) if rest else SVar(name=s.target)
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
        then_b = _fold(list(s.body) + rest, lw)
        else_b = _fold(list(s.orelse) + rest, lw)
        return SIf(cond=cond, then_branch=then_b, else_branch=else_b)

    if isinstance(s, PyWhile):
        cond = lw.lower_expr(s.test)
        if cond is None:
            raise IrisGenError("cannot lower while-condition")
        body = _fold(list(s.body), lw)
        rest_e = _fold(rest, lw)
        return SLet(var="_", value=SWhile(cond=cond, body=body),
                    body=rest_e)

    if isinstance(s, PyExprStmt):
        val = lw.lower_expr(s.expr)
        if val is None:
            raise IrisGenError("cannot lower expression statement")
        if not rest:
            return val
        return SLet(var="_", value=val, body=_fold(rest, lw))

    if isinstance(s, PyRaise):
        exc_val = SLit(lit_type="string", value=s.exc_type)
        if not rest:
            return SReturn(value=exc_val)
        return SLet(var="_", value=SReturn(value=exc_val),
                    body=_fold(rest, lw))

    if isinstance(s, PyTry):
        body_e = _fold(list(s.body), lw)
        if s.handlers:
            h = s.handlers[0]
            exc_name = h.exc_var or "_ex"
            handler_e = _fold(list(h.body), lw)
            if not rest:
                return STry(body=body_e, exc_var=exc_name,
                            handler=handler_e)
            return SLet(var="_", value=STry(body=body_e, exc_var=exc_name,
                                            handler=handler_e),
                        body=_fold(rest, lw))
        if not rest:
            return body_e
        return SLet(var="_", value=body_e, body=_fold(rest, lw))

    if isinstance(s, PyFor):
        # Desugar: for x in range(lo, hi): body
        #   → _i = lo; while _i < hi: x = _i; body; _i += 1
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
            raise IrisGenError(
                "for loop: only range(hi) or range(lo, hi) supported")
        ivar = f"_{s.var}_i"
        init = SLet(var=ivar, value=lo_val, body=_fold([], lw))
        body_stmts = [PyAssign(target=s.var,
                               value=PyName(name=ivar)),
                      *(list(s.body)),
                      PyAugAssign(target=ivar, op="+",
                                  value=PyConstant(value=1, py_type="int"))]
        body_e = _fold(body_stmts, lw)
        while_e = SWhile(
            cond=SBinOp(op="lt", left=SVar(name=ivar),
                        right=hi_val),
            body=body_e)
        return SLet(var="_", value=init,
                    body=SLet(var="_", value=while_e,
                              body=_fold(rest, lw)))

    raise IrisGenError(
        f"unsupported statement for Iris lowering: {type(s).__name__} "
        f"(break/continue: later phases)")


# -- Parameter substitution -------------------------------------------------

def _subst_params(e: SExpr, params: set[str], bound: set[str]) -> SExpr:
    """Replace free references to function parameters with Coq-level
    binders: SVar("x") -> SLit("int", "x") prints as (Val (LitInt x)).
    Respects shadowing by let-bound program variables."""
    if isinstance(e, SVar):
        if e.name in params and e.name not in bound:
            return SLit(lit_type="int", value=e.name)
        return e
    if isinstance(e, SLit):
        return e
    if isinstance(e, SBinOp):
        return SBinOp(op=e.op,
                      left=_subst_params(e.left, params, bound),
                      right=_subst_params(e.right, params, bound))
    if isinstance(e, SLet):
        return SLet(var=e.var,
                    value=_subst_params(e.value, params, bound),
                    body=_subst_params(e.body, params, bound | {e.var}))
    if isinstance(e, SIf):
        return SIf(cond=_subst_params(e.cond, params, bound),
                   then_branch=_subst_params(e.then_branch, params, bound),
                   else_branch=_subst_params(e.else_branch, params, bound))
    if isinstance(e, SWhile):
        return SWhile(cond=_subst_params(e.cond, params, bound),
                      body=_subst_params(e.body, params, bound))
    if isinstance(e, SApp):
        return SApp(func=e.func,
                    args=[_subst_params(a, params, bound) for a in e.args])
    if isinstance(e, SAlloc):
        return SAlloc(value=_subst_params(e.value, params, bound))
    if isinstance(e, SStore):
        return SStore(loc=e.loc, value=_subst_params(e.value, params, bound))
    if isinstance(e, SLoad):
        return e
    if isinstance(e, SReturn):
        return _subst_params(e.value, params, bound)
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
        return SWhile(cond=cond, body=_anf(e.body, ctr))
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


# -- Entry point --------------------------------------------------------------

def python_to_iris_proof(source: str,
                         table: FunTable,
                         func_name: Optional[str] = None,
                         axioms: Optional[list[str]] = None,
                         pre_overrides: Optional[dict[str, str]] = None,
                         ) -> IrisProof:
    """Lower a Python function with assert contracts to a staged Iris proof.

    source: Python source containing the function definition.
    table: callee contract/definition table (FunTable).
    func_name: which function to verify (default: the first def).
    axioms / pre_overrides: SMT escalation inputs, passed through.
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
    lw = IrisLowerer(loc_map={}, func_name=fn.name)
    body = _fold(fn.body, lw)
    body = _subst_params(body, set(fn.params), set())
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
    )
