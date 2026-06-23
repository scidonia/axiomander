"""SnakeletLang interpreter in Python — mirrors Coq SnakeletLang semantics.

Conservative: TypeError/ValueError produced precisely when Python would.
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
class VFloat(Val): v: float
@dataclass
class VBool(Val): v: bool
@dataclass
class VString(Val): v: str
@dataclass
class VUnit(Val): pass
@dataclass
class VTuple(Val): vs: list[Val]
@dataclass
class VDict(Val): d: dict[str, Val]
@dataclass
class VLoc(Val): l: int

@dataclass
class VError(Val):
    kind: str    # "TypeError", "ValueError", "KeyError", etc.
    msg: str = ""

    @staticmethod
    def type_error(msg: str = "") -> "VError":
        return VError("TypeError", msg)

    @staticmethod
    def value_error(msg: str = "") -> "VError":
        return VError("ValueError", msg)

    @staticmethod
    def key_error(msg: str = "") -> "VError":
        return VError("KeyError", msg)


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


# ── Binary operations (mirrors Coq binop_eval with Python coercions) ──

def _binop(op: str, l: Val, r: Val) -> Val:
    """Python-side binop_eval. Conservative: errors match Python precisely."""

    # bool → int coercion (Python: True→1, False→0 in arithmetic)
    if isinstance(l, VBool):
        l = VInt(1 if l.v else 0)
    if isinstance(r, VBool):
        r = VInt(1 if r.v else 0)

    # String operations
    if isinstance(l, VString) and isinstance(r, VString):
        if op == "add": return VString(l.v + r.v)
        if op == "eq":  return VBool(l.v == r.v)
        if op == "starts_with": return VBool(l.v.startswith(r.v))
        if op == "ends_with": return VBool(l.v.endswith(r.v))
        if op == "str_contains": return VBool(r.v in l.v)
        if op == "in": return VBool(r.v in l.v)
        return VError.type_error(f"unsupported string op: {op}")

    if isinstance(l, VString) and isinstance(r, VInt) and op == "mul":
        return VString(l.v * r.v)

    if isinstance(l, VString) and op == "len":
        return VInt(len(l.v))

    if isinstance(l, VString) and op == "to_lower":
        return VString(l.v.lower())

    if isinstance(l, VString) and op == "to_upper":
        return VString(l.v.upper())

    if isinstance(l, VString) and isinstance(r, VInt) and op == "str_index":
        i = r.v
        if 0 <= i < len(l.v):
            return VString(l.v[i])
        return VError.value_error(f"string index out of range")

    # Dict operations
    if isinstance(l, VDict) and isinstance(r, VString):
        if op == "dict_get_int":
            val = l.d.get(r.v)
            if isinstance(val, VInt):
                return val
            return VError.key_error(r.v)
        if op == "in":
            return VBool(r.v in l.d)

    # Integer operations
    if isinstance(l, VInt) and isinstance(r, VInt):
        return _int_binop(op, l.v, r.v)

    # Float coercion: int+float → float, int/float → float
    # Only convert numerics, not strings
    if isinstance(l, (VInt, VFloat)) and isinstance(r, (VInt, VFloat)):
        a = l.v if isinstance(l, VFloat) else float(getattr(l, 'v', 0))
        b = r.v if isinstance(r, VFloat) else float(getattr(r, 'v', 0))
        return _float_binop(op, a, b)

    return VError.type_error(
        f"unsupported operand types for {op}: {type(l).__name__} and {type(r).__name__}"
    )


def _to_float(v: Val) -> Val:
    if isinstance(v, VInt): return VFloat(float(v.v))
    if isinstance(v, VFloat): return v
    return v


def _int_binop(op: str, a: int, b: int) -> Val:
    if op == "add": return VInt(a + b)
    if op == "sub": return VInt(a - b)
    if op == "mul": return VInt(a * b)
    if op == "div": return VFloat(a / b)       # Python: int/int → float
    if op == "eq":  return VBool(a == b)
    if op == "le":  return VBool(a <= b)
    if op == "lt":  return VBool(a < b)
    if op == "gt":  return VBool(a > b)
    if op == "ge":  return VBool(a >= b)
    return VError.type_error(f"unknown int op: {op}")


def _float_binop(op: str, a: Val, b: Val) -> Val:
    fa = a.v if isinstance(a, VFloat) else float(getattr(a, 'v', 0))
    fb = b.v if isinstance(b, VFloat) else float(getattr(b, 'v', 0))
    if op == "add": return VFloat(fa + fb)
    if op == "sub": return VFloat(fa - fb)
    if op == "mul": return VFloat(fa * fb)
    if op == "div": return VFloat(fa / fb)
    if op == "eq":  return VBool(fa == fb)
    if op == "le":  return VBool(fa <= fb)
    if op == "lt":  return VBool(fa < fb)
    if op == "gt":  return VBool(fa > fb)
    if op == "ge":  return VBool(fa >= fb)
    return VError.type_error(f"unknown float op: {op}")


# ── Expression evaluator ─────────────────────────────────────────

def eval_expr(e: Any, s: State, env: dict[str, Val]) -> Val:
    from axiomander.oracle.snakelet_ir import (
        SLit, SVar, SBinOp, SLoad, SStore, SLet, SIf, SReturn,
        SSeq, SFAA, SDictGet, SDictSet,
    )

    if isinstance(e, SLit):
        t = e.lit_type
        v = e.value
        if t == "int": return VInt(int(v))
        if t == "bool": return VBool(v.lower() == "true")
        if t == "string": return VString(v)
        if t == "unit": return VUnit()
        if t == "dict":
            d: dict[str, Val] = {}
            if e.elements:
                elems = list(e.elements)
                for i in range(0, len(elems), 2):
                    if i + 1 < len(elems):
                        key_val = eval_expr(elems[i], s, env)
                        val_val = eval_expr(elems[i + 1], s, env)
                        key_str = str(key_val.v) if hasattr(key_val, 'v') else str(key_val)
                        d[key_str] = val_val
            return VDict(d)
        return VUnit()

    if isinstance(e, SVar):
        return env.get(e.name, VError("NameError", f"{e.name} not defined"))

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
        return VError.value_error(f"invalid load location: {loc_str}")

    if isinstance(e, SStore):
        v = eval_expr(e.value, s, env)
        loc_str = e.loc
        if isinstance(loc_str, str):
            loc_val = env.get(loc_str)
            if isinstance(loc_val, VLoc):
                store(s, loc_val.l, v)
                return VUnit()
        return VError.value_error(f"invalid store location: {loc_str}")

    if isinstance(e, SIf):
        c = eval_expr(e.cond, s, env)
        if isinstance(c, VBool) and c.v:
            return eval_expr(e.then_branch, s, env)
        return eval_expr(e.else_branch, s, env)

    if isinstance(e, SReturn):
        return eval_expr(e.value, s, env)

    if isinstance(e, SSeq):
        result: Val = VUnit()
        for expr in e.exprs:
            result = eval_expr(expr, s, env)
        return result

    if isinstance(e, SFAA):
        loc_val = env.get(e.loc)
        if isinstance(loc_val, VLoc):
            cell = load(s, loc_val.l)
            if isinstance(cell, VInt):
                v = eval_expr(e.value, s, env)
                if isinstance(v, VInt):
                    store(s, loc_val.l, VInt(cell.v + v.v))
                    return cell  # FAA returns OLD value
        return VError.type_error("FAA requires integer heap cell")

    if isinstance(e, SDictGet):
        loc_val = env.get(e.loc) if isinstance(e.loc, str) else eval_expr(e.loc, s, env)
        key = eval_expr(e.key, s, env)
        if isinstance(loc_val, VLoc):
            d = load(s, loc_val.l)
            if isinstance(d, dict):
                k = str(key)
                return d.get(k, VError("KeyError", k))
        return VError.type_error("DictGet on non-dict")

    if isinstance(e, SDictSet):
        loc_val = env.get(e.loc) if isinstance(e.loc, str) else eval_expr(e.loc, s, env)
        key = eval_expr(e.key, s, env)
        v = eval_expr(e.value, s, env)
        if isinstance(loc_val, VLoc):
            d = load(s, loc_val.l)
            if isinstance(d, dict):
                d[str(key)] = v
                store(s, loc_val.l, d)
                return VUnit()
            store(s, loc_val.l, {str(key): v})
            return VUnit()
        return VError.type_error("DictSet on non-dict heap cell")

    return VUnit()
