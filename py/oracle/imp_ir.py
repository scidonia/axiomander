"""
IMP Verification IR -- proof-oriented Pydantic models for IMP commands.

Every IMP constructor is a node with a .to_coq() method.
No string manipulation -- the renderer is the single source of Coq syntax.
"""

from __future__ import annotations
from typing import Literal, Union, Optional
from pydantic import BaseModel, Field


# ── AExp (arithmetic expressions) ────────────────────────────────


class ImpAExp(BaseModel):
    """Base for arithmetic expressions."""

    def to_coq(self) -> str: ...


class ImpANum(ImpAExp):
    """Integer literal: ANum n."""

    kind: Literal["anum"] = "anum"
    value: int

    def to_coq(self) -> str:
        v = self.value
        return f"(ANum {v})" if v >= 0 else f"(ANum ({v}))"


class ImpAVar(ImpAExp):
    """Variable read from state: AVar x."""

    kind: Literal["avar"] = "avar"
    name: str

    def to_coq(self) -> str:
        return f'(AVar "{self.name}"%string)'


class ImpAPlus(ImpAExp):
    """Addition: APlus a1 a2."""

    kind: Literal["aplus"] = "aplus"
    left: ImpAExp
    right: ImpAExp

    def to_coq(self) -> str:
        return f"(APlus {self.left.to_coq()} {self.right.to_coq()})"


class ImpAMinus(ImpAExp):
    """Subtraction: AMinus a1 a2."""

    kind: Literal["aminus"] = "aminus"
    left: ImpAExp
    right: ImpAExp

    def to_coq(self) -> str:
        return f"(AMinus {self.left.to_coq()} {self.right.to_coq()})"


class ImpAMult(ImpAExp):
    """Multiplication: AMult a1 a2."""

    kind: Literal["amult"] = "amult"
    left: ImpAExp
    right: ImpAExp

    def to_coq(self) -> str:
        return f"(AMult {self.left.to_coq()} {self.right.to_coq()})"


class ImpAMod(ImpAExp):
    """Modulo: AMod a1 a2."""

    kind: Literal["amod"] = "amod"
    left: ImpAExp
    right: ImpAExp

    def to_coq(self) -> str:
        return f"(AMod {self.left.to_coq()} {self.right.to_coq()})"


class ImpADiv(ImpAExp):
    """Integer division: ADiv a1 a2."""

    kind: Literal["adiv"] = "adiv"
    left: ImpAExp
    right: ImpAExp

    def to_coq(self) -> str:
        return f"(ADiv {self.left.to_coq()} {self.right.to_coq()})"


class ImpABool(ImpAExp):
    """Boolean to Z: ABool b -> VZ 1 or VZ 0."""

    kind: Literal["abool"] = "abool"
    bexp: ImpBExp

    def to_coq(self) -> str:
        return f"(ABool {self.bexp.to_coq()})"


class ImpALen(ImpAExp):
    """List/string length: ALen "lst"."""

    kind: Literal["alen"] = "alen"
    name: str

    def to_coq(self) -> str:
        return f'(ALen "{self.name}"%string)'


class ImpAIndex(ImpAExp):
    """Array/dict index: AIndex arr idx."""

    kind: Literal["aindex"] = "aindex"
    name: str
    index: ImpAExp

    def to_coq(self) -> str:
        return f'(AIndex "{self.name}"%string {self.index.to_coq()})'


class ImpAString(ImpAExp):
    """String literal: AString value."""

    kind: Literal["astring"] = "astring"
    value: str

    def to_coq(self) -> str:
        escaped = self.value.replace("\\", "\\\\").replace('"', '\\"')
        return f'(AString "{escaped}"%string)'


class ImpAFloat(ImpAExp):
    """Float literal (Z-encoded): AFloat f."""

    kind: Literal["afloat"] = "afloat"
    value: int

    def to_coq(self) -> str:
        return f"(AFloat {self.value})"


class ImpANone(ImpAExp):
    """None literal: ANone."""

    kind: Literal["anone"] = "anone"

    def to_coq(self) -> str:
        return "ANone"


class ImpATuple(ImpAExp):
    """Tuple literal: ATuple [e1; e2; ...]."""

    kind: Literal["atuple"] = "atuple"
    elements: list[ImpAExp] = Field(default_factory=list)

    def to_coq(self) -> str:
        els = " :: ".join(e.to_coq() for e in self.elements)
        return f"(ATuple ({els} :: nil))" if els else "(ATuple nil)"


class ImpAList(ImpAExp):
    """List literal: AList [e1; e2; ...]."""

    kind: Literal["alist"] = "alist"
    elements: list[ImpAExp] = Field(default_factory=list)

    def to_coq(self) -> str:
        els = " :: ".join(e.to_coq() for e in self.elements)
        return f"(AList ({els} :: nil))" if els else "(AList nil)"


class ImpADict(ImpAExp):
    """Dict literal: ADict [(k1, v1); (k2, v2); ...]."""

    kind: Literal["adict"] = "adict"
    pairs: list[tuple[ImpAExp, ImpAExp]] = Field(default_factory=list)

    def to_coq(self) -> str:
        if not self.pairs:
            return "(ADict nil)"
        pair_strs = [f"({k.to_coq()}, {v.to_coq()})" for k, v in self.pairs]
        return f"(ADict ({' :: '.join(pair_strs)} :: nil))"


class ImpABytes(ImpAExp):
    """Bytes literal: ABytes [e1; e2; ...]."""

    kind: Literal["abytes"] = "abytes"
    elements: list[ImpAExp] = Field(default_factory=list)

    def to_coq(self) -> str:
        els = " :: ".join(e.to_coq() for e in self.elements)
        return f"(ABytes ({els} :: nil))" if els else "(ABytes nil)"


class ImpASetLit(ImpAExp):
    """Set literal: ASetLit [e1; e2; ...]."""

    kind: Literal["asetlit"] = "asetlit"
    elements: list[ImpAExp] = Field(default_factory=list)

    def to_coq(self) -> str:
        els = " :: ".join(e.to_coq() for e in self.elements)
        return f"(ASetLit ({els} :: nil))" if els else "(ASetLit nil)"


class ImpAAppend(ImpAExp):
    """List append expression: AAppend a e."""

    kind: Literal["aappend"] = "aappend"
    list_expr: ImpAExp
    elem: ImpAExp

    def to_coq(self) -> str:
        return f"(AAppend {self.list_expr.to_coq()} {self.elem.to_coq()})"


class ImpAPop(ImpAExp):
    """List pop expression: APop a."""

    kind: Literal["apop"] = "apop"
    list_expr: ImpAExp

    def to_coq(self) -> str:
        return f"(APop {self.list_expr.to_coq()})"


class ImpASet(ImpAExp):
    """List set expression: ASet a idx val."""

    kind: Literal["aset"] = "aset"
    list_expr: ImpAExp
    idx: ImpAExp
    val: ImpAExp

    def to_coq(self) -> str:
        return f"(ASet {self.list_expr.to_coq()} {self.idx.to_coq()} {self.val.to_coq()})"


class ImpADictLen(ImpAExp):
    """Dict membership check: ADictLen name key."""

    kind: Literal["adictlen"] = "adictlen"
    name: str
    key: ImpAExp

    def to_coq(self) -> str:
        return f'(ADictLen "{self.name}"%string {self.key.to_coq()})'


class ImpADictCount(ImpAExp):
    """Dict key count: ADictCount name."""

    kind: Literal["adictcount"] = "adictcount"
    name: str

    def to_coq(self) -> str:
        return f'(ADictCount "{self.name}"%string)'


class ImpASetMem(ImpAExp):
    """String-keyed set membership: ASetMem name key_e.
    Evaluates to VZ 1 if the string key is a member, VZ 0 otherwise."""

    kind: Literal["asetmem"] = "asetmem"
    name: str
    key: ImpAExp

    def to_coq(self) -> str:
        return f'(ASetMem "{self.name}"%string {self.key.to_coq()})'


# ── BExp (boolean expressions) ───────────────────────────────────


class ImpBExp(BaseModel):
    """Base for boolean expressions."""

    def to_coq(self) -> str: ...


class ImpBTrue(ImpBExp):
    kind: Literal["btrue"] = "btrue"

    def to_coq(self) -> str:
        return "BTrue"


class ImpBFalse(ImpBExp):
    kind: Literal["bfalse"] = "bfalse"

    def to_coq(self) -> str:
        return "BFalse"


class ImpBEq(ImpBExp):
    """Value equality: BEq a1 a2."""

    kind: Literal["beq"] = "beq"
    left: ImpAExp
    right: ImpAExp

    def to_coq(self) -> str:
        return f"(BEq {self.left.to_coq()} {self.right.to_coq()})"


class ImpBLe(ImpBExp):
    """Less-or-equal: BLe a1 a2."""

    kind: Literal["ble"] = "ble"
    left: ImpAExp
    right: ImpAExp

    def to_coq(self) -> str:
        return f"(BLe {self.left.to_coq()} {self.right.to_coq()})"


class ImpBNot(ImpBExp):
    """Negation: BNot b."""

    kind: Literal["bnot"] = "bnot"
    operand: ImpBExp

    def to_coq(self) -> str:
        return f"(BNot {self.operand.to_coq()})"


class ImpBAnd(ImpBExp):
    """Conjunction: BAnd b1 b2."""

    kind: Literal["band"] = "band"
    left: ImpBExp
    right: ImpBExp

    def to_coq(self) -> str:
        return f"(BAnd {self.left.to_coq()} {self.right.to_coq()})"


class ImpBOr(ImpBExp):
    """Disjunction: BOr b1 b2."""

    kind: Literal["bor"] = "bor"
    left: ImpBExp
    right: ImpBExp

    def to_coq(self) -> str:
        return f"(BOr {self.left.to_coq()} {self.right.to_coq()})"


class ImpBIsVZ(ImpBExp):
    """Type guard: BIsVZ x - is the heap value at x a VZ?"""

    kind: Literal["bisvz"] = "bisvz"
    var: str

    def to_coq(self) -> str:
        return f'(BIsVZ "{self.var}"%string)'


class ImpBIsVString(ImpBExp):
    """Type guard: BIsVString x."""

    kind: Literal["bisvstring"] = "bisvstring"
    var: str

    def to_coq(self) -> str:
        return f'(BIsVString "{self.var}"%string)'


class ImpBIsNone(ImpBExp):
    """Type guard: BIsNone x."""

    kind: Literal["bisnone"] = "bisnone"
    var: str

    def to_coq(self) -> str:
        return f'(BIsNone "{self.var}"%string)'


class ImpBIsVFloat(ImpBExp):
    """Type guard: BIsVFloat x."""

    kind: Literal["bisvfloat"] = "bisvfloat"
    var: str

    def to_coq(self) -> str:
        return f'(BIsVFloat "{self.var}"%string)'


# ── Commands ────────────────────────────────────────────────────


class ImpCom(BaseModel):
    """Base for IMP commands."""

    def to_coq(self) -> str: ...


class ImpCSkip(ImpCom):
    """No-op."""

    kind: Literal["cskip"] = "cskip"

    def to_coq(self) -> str:
        return "CSkip"


class ImpCAss(ImpCom):
    """Assignment: CAss x aexp."""

    kind: Literal["cass"] = "cass"
    target: str
    value: ImpAExp

    def to_coq(self) -> str:
        return f'(CAss "{self.target}"%string {self.value.to_coq()})'


class ImpCSeq(ImpCom):
    """Sequential composition: CSeq c1 c2."""

    kind: Literal["cseq"] = "cseq"
    commands: list[ImpCom] = Field(default_factory=list)

    def to_coq(self) -> str:
        if not self.commands:
            return "CSkip"
        result = self.commands[0].to_coq()
        for cmd in self.commands[1:]:
            result = f"(CSeq {result} {cmd.to_coq()})"
        return result


class ImpCIf(ImpCom):
    """Conditional: CIf b c1 c2."""

    kind: Literal["cif"] = "cif"
    condition: ImpBExp
    then_branch: ImpCom
    else_branch: ImpCom = ImpCSkip()

    def to_coq(self) -> str:
        return f"(CIf {self.condition.to_coq()} {self.then_branch.to_coq()} {self.else_branch.to_coq()})"


class ImpCWhile(ImpCom):
    """While loop: CWhile b inv body."""

    kind: Literal["cwhile"] = "cwhile"
    condition: ImpBExp
    invariant: str = "(fun _ => True)"  # Coq assertion string
    body: ImpCom = ImpCSkip()

    def to_coq(self) -> str:
        return (
            f"(CWhile {self.condition.to_coq()} {self.invariant} {self.body.to_coq()})"
        )


class ImpCCall(ImpCom):
    """Function call: CCall name args pre post writes target."""

    kind: Literal["ccall"] = "ccall"
    name: str
    args: list[ImpAExp] = Field(default_factory=list)
    precondition: str  # Coq assertion string: (fun s => ...)
    postcondition: str  # Coq assertion string: (fun s => ...)
    writes: list[str] = Field(default_factory=list)
    target: str = ""
    frame_vars: list[str] = Field(default_factory=list)

    def to_coq(self) -> str:
        args_str = (
            "(" + " :: ".join(a.to_coq() for a in self.args) + " :: nil)"
            if self.args
            else "nil"
        )
        writes_str = (
            "(" + " :: ".join(f'"{w}"%string' for w in self.writes) + " :: nil)"
            if self.writes
            else "nil"
        )
        return (
            f'(CCall "{self.name}"%string {args_str} '
            f"{self.precondition} {self.postcondition} "
            f'{writes_str} "{self.target}"%string)'
        )


class ImpCListNew(ImpCom):
    """List creation: CListNew lst."""

    kind: Literal["clistnew"] = "clistnew"
    name: str

    def to_coq(self) -> str:
        return f'(CListNew "{self.name}"%string)'


class ImpCListAppend(ImpCom):
    """List append: CListAppend lst val."""

    kind: Literal["clistappend"] = "clistappend"
    name: str
    value: ImpAExp

    def to_coq(self) -> str:
        return f'(CListAppend "{self.name}"%string {self.value.to_coq()})'


class ImpCListPop(ImpCom):
    """List pop (discard): CListPop name. Does not capture the removed element."""

    kind: Literal["clistpop"] = "clistpop"
    name: str

    def to_coq(self) -> str:
        return f'(CListPop "{self.name}"%string)'


class ImpCListPopTo(ImpCom):
    """List pop and capture: CListPopTo name target.
    Removes the last element from heap list [name] and assigns it to [target]."""

    kind: Literal["clistpopto"] = "clistpopto"
    name: str
    target: str

    def to_coq(self) -> str:
        return f'(CListPopTo "{self.name}"%string "{self.target}"%string)'


class ImpCHeapUpdate(ImpCom):
    """Core: write to heap.  CHeapUpdate name field value.
    hupd s name field (aeval value s).
    Replaces CListAppend, CDictSet, CSetAdd etc. which are now
    compound definitions in Coq built from CHeapUpdate. """

    kind: Literal["cheapupdate"] = "cheapupdate"
    name: str
    field: ImpAExp    # heap key, e.g. len_f, elem_f i, smem_f key
    value: ImpAExp

    def to_coq(self) -> str:
        return f'(CHeapUpdate "{self.name}"%string {self.field.to_coq()} {self.value.to_coq()})'


class ImpCSetAdd(ImpCom):
    """Set insert — desugars to CHeapUpdate on smem_f(key)."""

    kind: Literal["csetadd"] = "csetadd"
    name: str
    key: ImpAExp

    def to_coq(self) -> str:
        from .imp_ir import ImpANum, ImpAString, ImpAVar
        field = ImpAString(value=self.key.to_coq()) if isinstance(self.key, ImpAVar) else self.key
        return (
            f'(CHeapUpdate "{self.name}"%string '
            f'(smem_f (asString (aeval {self.key.to_coq()} s))) '
            f'(ANum 1))'
        )


class ImpCSetDiscard(ImpCom):
    """String-keyed set remove (no-op if absent): CSetDiscard name key."""

    kind: Literal["csetdiscard"] = "csetdiscard"
    name: str
    key: ImpAExp

    def to_coq(self) -> str:
        return f'(CSetDiscard "{self.name}"%string {self.key.to_coq()})'


class ImpCListSet(ImpCom):
    """List set element: CListSet name idx val."""

    kind: Literal["clistset"] = "clistset"
    name: str
    idx: ImpAExp
    val: ImpAExp

    def to_coq(self) -> str:
        return f'(CListSet "{self.name}"%string {self.idx.to_coq()} {self.val.to_coq()})'


class ImpCDictSet(ImpCom):
    """Dict set key-value: CDictSet name key val."""

    kind: Literal["cdictset"] = "cdictset"
    name: str
    key: ImpAExp
    val: ImpAExp

    def to_coq(self) -> str:
        return f'(CDictSet "{self.name}"%string {self.key.to_coq()} {self.val.to_coq()})'


class ImpCDictGet(ImpCom):
    """Dict get: CDictGet name key target."""

    kind: Literal["cdictget"] = "cdictget"
    name: str
    key: ImpAExp
    target: str

    def to_coq(self) -> str:
        return f'(CDictGet "{self.name}"%string {self.key.to_coq()} "{self.target}"%string)'


class ImpCDictEnsureList(ImpCom):
    """Dict ensure list: CDictEnsureList name key."""

    kind: Literal["cdictensurelist"] = "cdictensurelist"
    name: str
    key: ImpAExp

    def to_coq(self) -> str:
        return f'(CDictEnsureList "{self.name}"%string {self.key.to_coq()})'


class ImpCDictAppend(ImpCom):
    """Dict append to list: CDictAppend name key val."""

    kind: Literal["cdictappend"] = "cdictappend"
    name: str
    key: ImpAExp
    val: ImpAExp

    def to_coq(self) -> str:
        return f'(CDictAppend "{self.name}"%string {self.key.to_coq()} {self.val.to_coq()})'


class ImpCDictAppendKv(ImpCom):
    """Dict key-value store: CDictAppendKv d key val."""

    kind: Literal["cdictappendkv"] = "cdictappendkv"
    name: str
    key: ImpAExp
    value: ImpAExp

    def to_coq(self) -> str:
        return f'(CDictAppendKv "{self.name}"%string {self.key.to_coq()} {self.value.to_coq()})'


class ImpCAssume(ImpCom):
    """Assumption: CAssume P — constrains non-determinism with a trusted property."""

    kind: Literal["cassume"] = "cassume"
    condition: str  # Coq assertion string: (fun s => ...)

    def to_coq(self) -> str:
        return f"(CAssume {self.condition})"


class ImpCHavoc(ImpCom):
    """Havoc: CHavoc [vars] - conservative unknown mutation."""

    kind: Literal["chavoc"] = "chavoc"
    vars: list[str] = Field(default_factory=list)

    def to_coq(self) -> str:
        vars_str = " ".join(f'"{v}"%string' for v in self.vars)
        return f"(CHavoc [{vars_str}])"


class ImpCRaise(ImpCom):
    """Raise: CRaise e -- terminates with ORaise (aeval e s) s.

    The exception value is typically AString "ExcTypeName" so that
    outcome predicates can match on the exception class by name.
    """

    kind: Literal["craise"] = "craise"
    exc: ImpAExp  # the exception value expression

    def to_coq(self) -> str:
        return f"(CRaise {self.exc.to_coq()})"


class ImpCTry(ImpCom):
    """Try/except: CTry body exc handler.

    body   -- the command that may raise.
    exc    -- variable name that receives the exception value on catch.
    handler -- command executed if body raises; exc is bound in scope.
    """

    kind: Literal["ctry"] = "ctry"
    body: "ImpCom"
    exc: str       # variable name for the caught exception
    handler: "ImpCom"

    def to_coq(self) -> str:
        return f'(CTry {self.body.to_coq()} "{self.exc}"%string {self.handler.to_coq()})'


# ── Helpers ─────────────────────────────────────────────────────


def seq(*commands: ImpCom) -> ImpCom:
    """Build a CSeq from multiple commands."""
    cmds = [c for c in commands if not isinstance(c, ImpCSkip)]
    if not cmds:
        return ImpCSkip()
    if len(cmds) == 1:
        return cmds[0]
    return ImpCSeq(commands=cmds)
