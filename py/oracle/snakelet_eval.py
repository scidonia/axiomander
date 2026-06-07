"""SnakeletLang interpreter in Python — mirrors Coq SnakeletLang semantics.

Used for testing: Python expr → SnakeletIR → eval → compare with Python eval.
Conservative: if SnakeletLang produces the same result as Python, the lowering
is correct. If they differ, SnakeletLang is wrong.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Any
import struct


# ── Value types (mirrors Coq val inductive) ──────────────────────

class Val:
    pass

@dataclass
class VInt(Val): v: int
@dataclass
class VFloat(Val):
    v: float
    def __eq__(self, other):
        if isinstance(other, VFloat):
            return struct.pack('d', self.v) == struct.pack('d', other.v)
        return False
@dataclass
class VBool(Val): v: bool
@dataclass
class VString(Val): v: str
@dataclass
class VUnit(Val): pass
@dataclass
class VTuple(Val): vs: list[Val]
@dataclass
class VLoc(Val): l: int


# ── Interpreter ──────────────────────────────────────────────────

@dataclass
class State:
    heap: dict[int, Val] = field(default_factory=dict)
    next_loc: int = 1


def alloc(s: State, v: Val) -> VLoc:
    l = s.next_loc
    s.next_loc += 1
    s.heap[l] = v
    return VLoc(l=l)


def load(s: State, l: int) -> Val:
    return s.heap.get(l, VUnit())


def store(s: State, l: int, v: Val) -> None:
    s.heap[l] = v


# ── Expression evaluator ─────────────────────────────────────────

def eval_expr(e: Any, s: State, env: dict[str, Val]) -> Val:
    """Evaluate a SnakeletIR SExpr node."""
    from oracle.snakelet_ir import (
        SLit, SVar, SBinOp, SLoad, SStore, SLet, SIf, SReturn,
        SSeq, SApp, SFork, SFAA, SDictGet, SDictSet,
    )

    if isinstance(e, SLit):
        t = e.lit_type
        v = e.value
        if t == "int": return VInt(int(v))
        if t == "bool": return VBool(v.lower() == "true")
        if t == "string": return VString(v)
        if t == "unit": return VUnit()
        return VUnit()

    if isinstance(e, SVar):
        return env.get(e.name, VUnit())

    if isinstance(e, SLet):
        v = eval_expr(e.value, s, env)
        new_env = dict(env)
        new_env[e.var] = v
        return eval_expr(e.body, s, new_env)

    if isinstance(e, SBinOp):
        l = eval_expr(e.left, s, env)
        r = eval_expr(e.right, s, env)
        return _binop(e.op, l, r)

    if isinstance(e, SLoad):
        loc_str = e.loc
        if isinstance(loc_str, str):
            loc_val = env.get(loc_str)
            if isinstance(loc_val, VLoc):
                return load(s, loc_val.l)
        return VUnit()

    if isinstance(e, SStore):
        v = eval_expr(e.value, s, env)
        loc_str = e.loc
        # Resolve string loc name from env or use directly
        if isinstance(loc_str, str):
            loc_val = env.get(loc_str)
            if isinstance(loc_val, VLoc):
                store(s, loc_val.l, v)
                return VUnit()
            # Try evaluating loc as expression
            l = eval_expr(SLit("string", loc_str), s, env)
            if isinstance(l, VLoc):
                store(s, l.l, v)
                return VUnit()
        return VUnit()

    if isinstance(e, SIf):
        c = eval_expr(e.cond, s, env)
        if isinstance(c, VBool) and c.v:
            return eval_expr(e.then_branch, s, env)
        return eval_expr(e.else_branch, s, env)

    if isinstance(e, SReturn):
        return eval_expr(e.value, s, env)

    if isinstance(e, SSeq):
        result = VUnit()
        for expr in e.exprs:
            result = eval_expr(expr, s, env)
        return result

    if isinstance(e, SDictGet):
        # Stub — dict lookup from heap
        loc = eval_expr(e.loc, s, env)
        key = eval_expr(e.key, s, env)
        if isinstance(loc, VLoc):
            d = load(s, loc.l)
            if isinstance(d, dict):
                return d.get(str(key), VUnit())
        return VUnit()

    if isinstance(e, SDictSet):
        loc = eval_expr(e.loc, s, env)
        key = eval_expr(e.key, s, env)
        v = eval_expr(e.value, s, env)
        if isinstance(loc, VLoc):
            d = load(s, loc.l)
            if isinstance(d, dict):
                d[str(key)] = v
                store(s, loc.l, d)
        return VUnit()

    return VUnit()


def _binop(op: str, l: Val, r: Val) -> Val:
    """Python-side binop_eval — mirrors Coq SnakeletLang.binop_eval."""
    # int + int
    if isinstance(l, VInt) and isinstance(r, VInt):
        a, b = l.v, r.v
        if op == "add": return VInt(a + b)
        if op == "sub": return VInt(a - b)
        if op == "mul": return VInt(a * b)
        if op == "div": return VFloat(a / b)
        if op == "eq": return VBool(a == b)
        if op == "le": return VBool(a <= b)
        if op == "lt": return VBool(a < b)
        if op == "gt": return VBool(a > b)
        if op == "ge": return VBool(a >= b)

    # float ops
    if isinstance(l, VFloat) or isinstance(r, VFloat):
        a = l.v if isinstance(l, VFloat) else float(getattr(l, 'v', 0))
        b = r.v if isinstance(r, VFloat) else float(getattr(r, 'v', 0))
        if op == "add": return VFloat(a + b)
        if op == "sub": return VFloat(a - b)
        if op == "mul": return VFloat(a * b)
        if op == "div": return VFloat(a / b)
        if op == "eq": return VBool(a == b)  # IEEE 754 exact
        if op == "le": return VBool(a <= b)
        if op == "lt": return VBool(a < b)
        if op == "gt": return VBool(a > b)
        if op == "ge": return VBool(a >= b)

    # bool eq
    if isinstance(l, VBool) and isinstance(r, VBool):
        if op == "eq": return VBool(l.v == r.v)

    return VUnit()


# ── Python expression → SnakeletIR lowering (inline for tests) ───

def py_to_val(v: Any) -> Val:
    if isinstance(v, bool): return VBool(v)
    if isinstance(v, int): return VInt(v)
    if isinstance(v, float): return VFloat(v)
    if isinstance(v, str): return VString(v)
    if v is None: return VUnit()
    return VUnit()


def val_to_py(v: Val) -> Any:
    if isinstance(v, VInt): return v.v
    if isinstance(v, VFloat): return v.v
    if isinstance(v, VBool): return v.v
    if isinstance(v, VString): return v.v
    if isinstance(v, VUnit): return None
    return str(v)
