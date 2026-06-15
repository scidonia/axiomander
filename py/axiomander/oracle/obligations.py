"""
Per-obligation data model for the Axiomander verification pipeline.

Each verification condition (pre, post, frame-per-variable, CCall stage, loop)
is a standalone Obligation with its own tactic ladder, residual capture,
and caching.

Replaces the monolithic foo_correct + wp_prove pattern for CCall functions.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional, Literal


class ObligationKind(Enum):
    PRE = "pre"
    POST = "post"
    FRAME = "frame"
    CCALL_STAGE = "ccall_stage"
    LOOP_INV = "loop_inv"
    LOOP_EXIT = "loop_exit"
    COMPOSITION = "composition"


class ObligationStatus(Enum):
    PROVED = "proved"
    RESIDUAL = "residual"
    COUNTEREXAMPLE = "counterexample"
    PENDING = "pending"


@dataclass
class ProofAttempt:
    tactic: str
    outcome: Literal["closed", "no_progress", "error"] = "no_progress"
    elapsed_ms: float = 0.0
    error: Optional[str] = None


@dataclass
class ResidualGoal:
    hypotheses: list[str] = field(default_factory=list)
    goal: str = ""
    coq_fragment: str = ""


@dataclass
class Obligation:
    id: str
    kind: ObligationKind
    theorem_name: str
    theorem_statement: str
    proof_attempts: list[ProofAttempt] = field(default_factory=list)
    status: ObligationStatus = ObligationStatus.PENDING
    residual: Optional[ResidualGoal] = None
    dependencies: list[str] = field(default_factory=list)

    def is_proved(self) -> bool:
        return self.status == ObligationStatus.PROVED

    @property
    def coq_block(self) -> str:
        preamble = self.theorem_statement + "\nProof.\n"
        tactics = "\n".join(a.tactic for a in self.proof_attempts)
        if self.is_proved():
            return preamble + (tactics + "\n" if tactics else "") + "Qed.\n"
        return preamble + (tactics + "\n" if tactics else "") + "Admitted.\n"
