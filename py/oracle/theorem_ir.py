"""
Theorem Intermediate Representation — Pydantic models for Coq theorems.

Replaces string templates in _generate_coq with a composable IR.
Every node has a .to_coq() method. No regex on Coq strings.
"""

from __future__ import annotations
from typing import Literal, Union, Optional
from pydantic import BaseModel, Field


# ── Core types ───────────────────────────────────────────────────

class CoqVar(BaseModel):
    """A Coq variable: (name : type)."""
    name: str
    coq_type: str = "Z"

    def to_coq(self) -> str:
        return f"({self.name} : {self.coq_type})"


class CoqProp(BaseModel):
    """A Coq proposition (expression)."""
    text: str

    def to_coq(self) -> str:
        return self.text


# ── Theorem structure ────────────────────────────────────────────

class TheoremIR(BaseModel):
    """A complete Coq theorem with body, pre/post, and proof."""
    name: str
    params: list[CoqVar] = Field(default_factory=list)
    pre: CoqProp = CoqProp(text="True")
    post: CoqProp = CoqProp(text="True")
    # Exception postconditions: exc_type -> Coq condition over raise-point state s.
    # E.g. {"ValueError": CoqProp("asZ (s \"n\"%string) < 0")}
    raises_clauses: dict[str, CoqProp] = Field(default_factory=dict)
    imp_body: str = "CSkip"
    init_state: str = "empty_state"
    proof: str = "  intros.\n  wp_prove."
    ghost_vars: dict[str, str] = Field(default_factory=dict)
    vcg_section: str = ""
    comments: list[str] = Field(default_factory=list)
    extra_imports: list[str] = Field(default_factory=list)  # e.g. "From Hammer Require Import Hammer."
    record_section: str = ""
    bool_import: str = ""

    def _build_phi(self) -> str:
        """Build the Coq outcome predicate Phi.

        If there are no raises clauses, uses wp_normal for the ensures cond.
        If there are raises clauses, emits a full match on outcome:

            fun o =>
              match o with
              | OReturn s => <ensures>
              | ORaise (VString "ExcType") s => <raises_cond>
              | _ => True
              end
        """
        if not self.raises_clauses:
            return f"(wp_normal (fun s => {self.post.to_coq()}))"
        # Full match form
        arms = [f"              | OReturn s => {self.post.to_coq()}"]
        for exc_type, cond in self.raises_clauses.items():
            arms.append(f'              | ORaise (VString "{exc_type}"%string) s => {cond.to_coq()}')
        arms.append("              | _ => True")
        arms_str = "\n".join(arms)
        return f"(fun o =>\n              match o with\n{arms_str}\n              end)"

    def to_coq(self) -> str:
        """Render the complete Coq file."""
        parts = []
        for c in self.comments:
            parts.append(f"(* {c} *)")
        for imp in self.extra_imports:
            parts.append(imp)
        parts.append("")
        parts.append("Require Import ZArith String List Lia.")
        if self.bool_import:
            parts.append(self.bool_import)
        parts.append("Require Import Imp Wp Pydantic WpTactics.")
        parts.append("Import ListNotations.")
        parts.append("Open Scope Z_scope.")
        if self.record_section:
            parts.append("")
            parts.append(self.record_section)
        parts.append("")
        parts.append(f"Definition {self.name}_body : com :=")
        parts.append(f"  {self.imp_body}.")
        parts.append("")

        # Theorem header
        params_str = " ".join(p.to_coq() for p in self.params)
        header = f"Theorem {self.name}_correct"
        if params_str:
            header += f" : forall {params_str},"
        else:
            header += " :"
        parts.append(header)

        # Body: pre -> wp body Phi init (with ghost existentials)
        phi = self._build_phi()
        inner = f"  (({self.pre.to_coq()}) ->\n" \
                f"  wp {self.name}_body\n" \
                f"     {phi}\n" \
                f"     ({self.init_state}))"
        for v, init in reversed(list(self.ghost_vars.items())):
            inner = f"(exists ({v} : Z), (({v} = {init}) /\\\n  {inner}))"
        parts.append(f"{inner}.")
        parts.append("Proof.")
        parts.append(self.proof)
        parts.append("Qed.")
        if self.vcg_section:
            parts.append(self.vcg_section)
        return "\n".join(parts)


# ── Proof builders ───────────────────────────────────────────────

def build_proof_wp_prove() -> str:
    return "  intros.\n  wp_prove."

def build_proof_wp_reduce_lia() -> str:
    return "  intros.\n  wp_reduce.\n  lia."

def build_proof_wp_true() -> str:
    return "  intros.\n  apply wp_True."

def build_proof_with_ghost(ghost_vars: dict[str, str], base_proof: str) -> str:
    """Insert ghost exists/split after intros."""
    prefix = ""
    for v, init in reversed(list(ghost_vars.items())):
        prefix += f"  exists {init}.\n  split.\n  - reflexivity.\n  - "
    return base_proof.replace("intros.", "intros.\n" + prefix, 1)
