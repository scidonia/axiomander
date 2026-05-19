"""
IMP Verification IR — proof-oriented Pydantic models for IMP commands.

Every IMP constructor is a node with a .to_coq() method.
No string manipulation — the renderer is the single source of Coq syntax.
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
        return f"(ANum {self.value})"


class ImpAVar(ImpAExp):
    """Variable read from state: AVar "x".""
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


class ImpABool(ImpAExp):
    """Boolean to Z: ABool b → VZ 1 or VZ 0."""
    kind: Literal["abool"] = "abool"
    bexp: ImpBExp

    def to_coq(self) -> str:
        return f"(ABool {self.bexp.to_coq()})"


class ImpALen(ImpAExp):
    """List/string length: ALen "lst".""
    kind: Literal["alen"] = "alen"
    name: str

    def to_coq(self) -> str:
        return f'(ALen "{self.name}"%string)'


class ImpAIndex(ImpAExp):
    """Array/dict index: AIndex "arr" idx."""
    kind: Literal["aindex"] = "aindex"
    name: str
    index: ImpAExp

    def to_coq(self) -> str:
        return f'(AIndex "{self.name}"%string {self.index.to_coq()})'


class ImpAString(ImpAExp):
    """String literal: AString "hello"."""
    kind: Literal["astring"] = "astring"
    value: str

    def to_coq(self) -> str:
        escaped = self.value.replace('\\', '\\\\').replace('"', '\\"')
        return f'(AString "{escaped}"%string)'


# ── BExp (boolean expressions) ───────────────────────────────────

class ImpBExp(BaseModel):
    """Base for boolean expressions."""
    def to_coq(self) -> str: ...


class ImpBTrue(ImpBExp):
    kind: Literal["btrue"] = "btrue"
    def to_coq(self) -> str: return "BTrue"


class ImpBFalse(ImpBExp):
    kind: Literal["bfalse"] = "bfalse"
    def to_coq(self) -> str: return "BFalse"


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
    """Type guard: BIsVZ "x" — is the heap value at x a VZ?"""
    kind: Literal["bisvz"] = "bisvz"
    var: str

    def to_coq(self) -> str:
        return f'(BIsVZ "{self.var}"%string)'


class ImpBIsVString(ImpBExp):
    """Type guard: BIsVString "x"."""
    kind: Literal["bisvstring"] = "bisvstring"
    var: str

    def to_coq(self) -> str:
        return f'(BIsVString "{self.var}"%string)'


# ── Commands ────────────────────────────────────────────────────

class ImpCom(BaseModel):
    """Base for IMP commands."""
    def to_coq(self) -> str: ...


class ImpCSkip(ImpCom):
    """No-op."""
    kind: Literal["cskip"] = "cskip"
    def to_coq(self) -> str: return "CSkip"


class ImpCAss(ImpCom):
    """Assignment: CAss "x" aexp."""
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
        return f"(CWhile {self.condition.to_coq()} {self.invariant} {self.body.to_coq()})"


class ImpCCall(ImpCom):
    """Function call: CCall "name" args pre post writes target."""
    kind: Literal["ccall"] = "ccall"
    name: str
    args: list[ImpAExp] = Field(default_factory=list)
    precondition: str   # Coq assertion string: (fun s => ...)
    postcondition: str  # Coq assertion string: (fun s => ...)
    writes: list[str] = Field(default_factory=list)
    target: str = ""

    def to_coq(self) -> str:
        args_str = "(" + " :: ".join(a.to_coq() for a in self.args) + " :: nil)" if self.args else "nil"
        writes_str = "(" + " :: ".join(f'"{w}"%string' for w in self.writes) + " :: nil)" if self.writes else "nil"
        return (f'(CCall "{self.name}"%string {args_str} '
                f'{self.precondition} {self.postcondition} '
                f'{writes_str} "{self.target}"%string)')


class ImpCListNew(ImpCom):
    """List creation: CListNew "lst"."""
    kind: Literal["clistnew"] = "clistnew"
    name: str

    def to_coq(self) -> str:
        return f'(CListNew "{self.name}"%string)'


class ImpCListAppend(ImpCom):
    """List append: CListAppend "lst" val."""
    kind: Literal["clistappend"] = "clistappend"
    name: str
    value: ImpAExp

    def to_coq(self) -> str:
        return f'(CListAppend "{self.name}"%string {self.value.to_coq()})'


class ImpCDictAppendKv(ImpCom):
    """Dict key-value store: CDictAppendKv "d" key val."""
    kind: Literal["cdictappendkv"] = "cdictappendkv"
    name: str
    key: ImpAExp
    value: ImpAExp

    def to_coq(self) -> str:
        return f'(CDictAppendKv "{self.name}"%string {self.key.to_coq()} {self.value.to_coq()})'


class ImpCHavoc(ImpCom):
    """Havoc: CHavoc [vars] — conservative unknown mutation."""
    kind: Literal["chavoc"] = "chavoc"
    vars: list[str] = Field(default_factory=list)

    def to_coq(self) -> str:
        vars_str = " ".join(f'"{v}"%string' for v in self.vars)
        return f"(CHavoc [{vars_str}])"


# ── Helpers ─────────────────────────────────────────────────────

def seq(*commands: ImpCom) -> ImpCom:
    """Build a CSeq from multiple commands."""
    cmds = [c for c in commands if not isinstance(c, ImpCSkip)]
    if not cmds:
        return ImpCSkip()
    if len(cmds) == 1:
        return cmds[0]
    return ImpCSeq(commands=cmds)
