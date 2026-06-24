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


def _spec_coq_block_ending(is_proved: int) -> int:
    """Scalar specification of Obligation.coq_block's Qed/Admitted decision.

    Encoding: 0 = Qed ending, 1 = Admitted ending.

    axiomander:
        requires:
            is_proved >= 0
            is_proved <= 1
        ensures:
            implies(is_proved == 1, result == 0)
            implies(is_proved == 0, result == 1)
    """
    if is_proved == 1:
        result = 0
    else:
        result = 1
    return result
