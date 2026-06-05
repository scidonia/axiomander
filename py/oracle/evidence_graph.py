"""
Evidence-asset graph: compositional contract verification.

Each contract carries evidence — the proof that it holds assuming its
callee contracts are valid.  The graph is a DAG; leaf nodes have
standalone evidence (WP, SMT axiom, Coq lemma).  Internal nodes are
valid iff all out-edges have evidence and all callee leaves are valid.

Trust base: leaf evidence → all contracts.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Optional


# ── Evidence types ────────────────────────────────────────────────

class EvidenceKind(Enum):
    LTAC          = "ltac"        # wp_reduce, lia — no external asset
    SMT           = "smt"         # SMT script (.smt2) + solver output
    SMT_THEORY    = "smt_theory"  # theory-SMT oracle (AxiomRecord)
    COQ_LEMMA     = "coq_lemma"   # Coq Lemma with Proof (in a .v file)
    COQ_FIXPOINT  = "coq_fixpoint"  # Coq Fixpoint (inductive def)
    UNROLLING     = "unrolling"   # bounded-unrolling SMT check


@dataclass
class Evidence:
    """One proof asset for a contract or dependency edge.

    At minimum carries a kind and status.  Specific evidence types
    carry additional routing information (e.g. query hash for SMT).
    """
    kind: EvidenceKind
    status: str = "proved"  # "proved" | "counterexample" | "unknown" | "pending"

    # ── SMT / theory-SMT ──
    query_hash: str = ""
    solver: str = ""
    smt2_path: str = ""      # path to the .smt2 script (for re-verification)

    # ── Coq ──
    coq_file: str = ""       # .v file containing the proof
    lemma_name: str = ""     # Lemma name within the .v file

    # ── Unrolling ──
    depth: int = 0
    predicate_name: str = ""

    # ── Generic ──
    notes: str = ""


# ── Contracts ─────────────────────────────────────────────────────

@dataclass
class ContractSpec:
    """A function's behavioural contract."""
    name: str
    params: list[str] = field(default_factory=list)
    pre_coq: str = "True"
    post_coq: str = "True"
    reads: list[str] = field(default_factory=list)
    writes: list[str] = field(default_factory=list)


# ── Graph nodes / edges ───────────────────────────────────────────

@dataclass
class ContractEdge:
    """A dependency: caller → callee.

    The edge carries evidence proving that the caller's body respects
    the callee's contract (pre/post/reads/writes) for this call site.

    For CCall frame conditions, the edge evidence is the per-variable
    frame lemma.  For theory-SMT, it's the per-call-site axiom.
    """
    callee_name: str
    callee_spec: ContractSpec
    target: str = ""              # CCall target variable
    evidence: list[Evidence] = field(default_factory=list)

    @property
    def proved(self) -> bool:
        return all(e.status == "proved" for e in self.evidence) if self.evidence else False


@dataclass
class ContractNode:
    """A verified function with its contract and evidence."""
    spec: ContractSpec
    evidence: list[Evidence] = field(default_factory=list)
    edges: list[ContractEdge] = field(default_factory=list)

    @property
    def proved(self) -> bool:
        """A node is proved iff it has standalone evidence OR all edges
        are proved and all callee nodes are proved (checked at graph level)."""
        has_own_evidence = any(e.status == "proved" for e in self.evidence)
        all_edges_proved = all(e.proved for e in self.edges) if self.edges else True
        return has_own_evidence or (all_edges_proved and not self.edges)

    @property
    def depends_on(self) -> list[str]:
        """Return the callees this node depends on via edges."""
        return [e.callee_name for e in self.edges]


# ── Evidence graph ────────────────────────────────────────────────

@dataclass
class EvidenceGraph:
    """A DAG of contracts with evidence.

    Invariants:
      - No cycles (enforced at construction).
      - Leaf nodes (no edges) MUST have standalone evidence.
      - Internal nodes are valid iff all out-edges have evidence AND
        all callee leaf nodes are proved.
    """
    nodes: dict[str, ContractNode] = field(default_factory=dict)

    def add_node(self, node: ContractNode) -> None:
        name = node.spec.name
        if name in self.nodes:
            raise ValueError(f"Duplicate node: {name}")
        self._check_no_cycles(name, node)
        self.nodes[name] = node

    def _check_no_cycles(self, new_name: str, node: ContractNode) -> None:
        """Raise if adding [node] would create a cycle."""
        for edge in node.edges:
            callee = edge.callee_name
            if callee == new_name:
                raise ValueError(f"Self-loop: {new_name} → {new_name}")
            if callee in self.nodes:
                if self._path_exists(callee, new_name):
                    raise ValueError(f"Cycle: {new_name} → ... → {callee} → {new_name}")

    def _path_exists(self, source: str, target: str) -> bool:
        """Check if there's a path from source to target in the graph."""
        visited: set[str] = set()
        def dfs(name: str) -> bool:
            if name == target:
                return True
            if name in visited:
                return False
            visited.add(name)
            node = self.nodes.get(name)
            if node:
                for edge in node.edges:
                    if dfs(edge.callee_name):
                        return True
            return False
        return dfs(source)

    def validate_all(self) -> dict[str, list[str]]:
        """Check composition: every internal node's callee edges are proved,
        and leaves have standalone evidence.  Returns {node: [issues]}."""
        issues: dict[str, list[str]] = {}
        for name, node in self.nodes.items():
            node_issues: list[str] = []

            # Leaf check: must have standalone evidence
            if not node.edges and not any(e.status == "proved" for e in node.evidence):
                node_issues.append("leaf node has no standalone evidence")

            # Edge check: all edges must be proved
            for edge in node.edges:
                if not edge.proved:
                    node_issues.append(f"edge to {edge.callee_name} unproved")
                # Callee must exist and be proved
                callee = self.nodes.get(edge.callee_name)
                if callee is None:
                    node_issues.append(f"callee {edge.callee_name} not in graph")
                elif not callee.proved:
                    node_issues.append(f"callee {edge.callee_name} not proved")

            if node_issues:
                issues[name] = node_issues

        return issues

    def composition_theorem_holds(self) -> bool:
        """True iff the graph is well-founded and all contracts are valid
        under the assumption that leaf evidence is sound."""
        return not bool(self.validate_all())

    def root_names(self) -> list[str]:
        """Return nodes that are not callees of any other node."""
        callees: set[str] = set()
        for node in self.nodes.values():
            for edge in node.edges:
                callees.add(edge.callee_name)
        return [n for n in self.nodes if n not in callees]

    def leaf_names(self) -> list[str]:
        """Return nodes with no outgoing edges."""
        return [n for n, node in self.nodes.items() if not node.edges]

    # ── Serialisation ───────────────────────────────────────────

    def to_dict(self) -> dict:
        return {
            "nodes": {
                name: {
                    "spec": {
                        "params": node.spec.params,
                        "pre": node.spec.pre_coq,
                        "post": node.spec.post_coq,
                        "reads": node.spec.reads,
                        "writes": node.spec.writes,
                    },
                    "evidence": [
                        {"kind": e.kind.value, "status": e.status,
                         "query_hash": e.query_hash, "lemma": e.lemma_name}
                        for e in node.evidence
                    ],
                    "edges": [
                        {"callee": e.callee_name, "target": e.target,
                         "evidence": [{"kind": ev.kind.value, "status": ev.status} for ev in e.evidence]}
                        for e in node.edges
                    ],
                }
                for name, node in self.nodes.items()
            }
        }
