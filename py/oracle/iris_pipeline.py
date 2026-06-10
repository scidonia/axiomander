"""Python source -> staged Iris proof wiring.

End-to-end pipeline for the Iris backend on the pure-integer fragment:

    Python ast
      -> PyIR                  (py_ir_translator)
      -> contract extraction   (positional asserts: leading = pre,
                                before-final-return = post)
      -> SnakeletIR            (continuation-folded statement lowering;
                                expressions via IrisLowerer)
      -> ANF normalization     (call args and binop operands become
                                atoms; SnakeletLang's ectx is
                                value-restricted on both binop sides, so
                                a binop with two non-value operands is
                                operationally stuck)
      -> staged proof          (iris_proof_gen.generate)

Contracts are plain assert statements, per the project ground rules:

    def chain(x):
        assert x >= 1            # precondition (leading assert)
        a = square(x)
        b = decr(a)
        assert b == x * x - 1    # postcondition (assert before return,
        return b                 #  over the returned variable)

The postcondition compiles to `exists z : Z, v = LitInt z /\\ (prop)`
with the returned variable renamed to z -- exactly the shape that
finish_pure's `eexists; split; [reflexivity | lia]` ladder closes.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass
from typing import Optional

from oracle.iris_lowerer import IrisLowerer
from oracle.iris_proof_gen import (
    FunTable, IrisGenError, IrisProof, generate,
)
from oracle.py_ir import (
    PyAssert, PyAssign, PyAugAssign, PyBinaryOp, PyBooleanOp, PyCompare,
    PyConstant, PyExpr, PyFunction, PyIf, PyName, PyReturn, PyStmt,
)
from oracle.py_ir_translator import PyIRTranslator
from oracle.snakelet_ir import (
    SApp, SBinOp, SExpr, SIf, SLet, SLit, SReturn, SVar,
)

# Binops supported by SnakeletLang's binop_eval on integers.
_SUPPORTED_OPS = {"add", "sub", "mul", "eq", "le", "lt", "gt", "ge"}


# -- Contract translation (PyIR contract exprs -> Coq Props) ---------------

def _zexpr(e: PyExpr, rename: dict[str, str]) -> str:
    """Print an integer contract expression as a Coq Z term."""
    if isinstance(e, PyName):
        return rename.get(e.name, e.name)
    if isinstance(e, PyConstant) and e.py_type == "int":
        return str(e.value)
    if isinstance(e, PyBinaryOp) and e.op in ("+", "-", "*"):
        return f"({_zexpr(e.left, rename)} {e.op} {_zexpr(e.right, rename)})"
    raise IrisGenError(
        f"unsupported contract arithmetic: {type(e).__name__}"
        f"{' op ' + getattr(e, 'op', '') if hasattr(e, 'op') else ''}")


_PROP_OPS = {"==": "=", "<=": "<=", "<": "<", ">=": ">=", ">": ">",
             "!=": "<>"}


def _prop(e: PyExpr, rename: dict[str, str]) -> str:
    """Print a contract expression as a Coq Prop."""
    if isinstance(e, PyCompare):
        if e.op not in _PROP_OPS:
            raise IrisGenError(f"unsupported contract comparison: {e.op}")
        return (f"{_zexpr(e.left, rename)} {_PROP_OPS[e.op]} "
                f"{_zexpr(e.right, rename)}")
    if isinstance(e, PyBooleanOp) and e.op == "and":
        return " /\\ ".join(f"({_prop(o, rename)})" for o in e.operands)
    raise IrisGenError(
        f"unsupported contract expression: {type(e).__name__}")


@dataclass
class Contracts:
    pre: Optional[str]       # Coq Prop over the parameters, or None
    post: str                # Coq Prop over v (the WP result)
    ret_var: Optional[str]   # name of the returned variable, if any


def extract_contracts(fn: PyFunction) -> tuple[Contracts, list[PyStmt]]:
    """Split positional asserts out of the body.

    Leading asserts are the precondition.  An assert immediately before
    the final return, mentioning the returned variable, is the
    postcondition.  Returns the contracts plus the body with contract
    asserts removed (other asserts are dropped too: they are redundant
    for the staged proof).
    """
    body = list(fn.body)

    pres: list[str] = []
    while body and isinstance(body[0], PyAssert):
        pres.append(_prop(body[0].test, {}))
        body = body[1:]
    pre = None
    if len(pres) == 1:
        pre = pres[0]
    elif pres:
        pre = " /\\ ".join(f"({p})" for p in pres)

    post = "True"
    ret_var = None
    if body and isinstance(body[-1], PyReturn):
        ret = body[-1]
        if isinstance(ret.value, PyName):
            ret_var = ret.value.name
        if (len(body) >= 2 and isinstance(body[-2], PyAssert)
                and ret_var is not None):
            prop = _prop(body[-2].test, {ret_var: "z"})
            post = f"exists z : Z, v = LitInt z /\\ ({prop})"
            body = body[:-2] + [ret]
    return Contracts(pre=pre, post=post, ret_var=ret_var), body


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

    raise IrisGenError(
        f"unsupported statement for Iris lowering: {type(s).__name__} "
        f"(loops/heap: later phases)")


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
    if isinstance(e, SApp):
        return SApp(func=e.func,
                    args=[_subst_params(a, params, bound) for a in e.args])
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
    elif isinstance(e, SApp):
        for a in e.args:
            _validate_ops(a)
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

    fn = PyIRTranslator().translate_function(target)
    contracts, body_stmts = extract_contracts(fn)

    lw = IrisLowerer(loc_map={}, func_name=fn.name)
    body = _fold(body_stmts, lw)
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
