"""
Specification Graph + Proof Provenance — Phase 1 of the Roadmap.

Implements a persistent DAG of contracts with annotated evidence.
Every function, type, model, and proof obligation is a node.
Edges represent dependency (caller → callee, lemma → axiom).
Evidence records provenance: how proved, under which assumptions,
which trust boundary.

Proof status follows the roadmap model:
  PROVED_L1_LTAC       — wp_reduce, lia (no external asset)
  PROVED_L2_SMT         — coq-hammer / cvc4 / eprover
  PROVED_L2B_THEORY     — theory-SMT oracle (QF_SLIA string/float)
  PROVED_L3_ORACLE      — LLM oracle (coq-lsp / coqpyt)
  ASSUMED_STUB          — library stub, contract assumed from .pyi
  USER_AXIOM            — hand-written Coq Axiom
  COUNTEREXAMPLE_FOUND  — SMT found a violation
  STALE                 — cache invalidated (callee changed)
  UNKNOWN               — not yet checked

Persistence: SQLite (suggested by roadmap).  The graph is the
primary artefact — implementations satisfy contracts, verification
maintains consistency, AI agents operate on specifications.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Optional
import json, os, hashlib


# ── Proof status (roadmap model) ──────────────────────────────────

class ProofStatus(Enum):
    PROVED_L1_LTAC       = "proved_l1_ltac"
    PROVED_L2_SMT         = "proved_l2_smt"
    PROVED_L2B_THEORY     = "proved_l2b_theory"
    PROVED_L3_ORACLE      = "proved_l3_oracle"
    ASSUMED_STUB          = "assumed_stub"
    USER_AXIOM            = "user_axiom"
    COUNTEREXAMPLE_FOUND  = "counterexample_found"
    STALE                 = "stale"
    UNKNOWN               = "unknown"

    @property
    def is_proved(self) -> bool:
        return self in (
            ProofStatus.PROVED_L1_LTAC,
            ProofStatus.PROVED_L2_SMT,
            ProofStatus.PROVED_L2B_THEORY,
            ProofStatus.PROVED_L3_ORACLE,
        )

    @property
    def is_assumed(self) -> bool:
        return self in (
            ProofStatus.ASSUMED_STUB,
            ProofStatus.USER_AXIOM,
        )

    @property
    def is_terminal(self) -> bool:
        """Terminal statuses — no further verification expected."""
        return self.is_proved or self == ProofStatus.COUNTEREXAMPLE_FOUND


# ── Evidence kind (provenance asset type) ─────────────────────────

class EvidenceKind(Enum):
    LTAC          = "ltac"           # wp_reduce, lia — no external asset
    SMT_SCRIPT    = "smt_script"     # SMT script (.smt2) + solver output
    SMT_THEORY    = "smt_theory"     # theory-SMT oracle (AxiomRecord)
    COQ_LEMMA     = "coq_lemma"      # Coq Lemma with Proof (in .v file)
    COQ_FIXPOINT  = "coq_fixpoint"   # Coq Fixpoint (inductive definition)
    UNROLLING     = "unrolling"      # bounded-unrolling SMT check
    STUB_CONTRACT = "stub_contract"  # library stub (.pyi file)


@dataclass
class Evidence:
    """One proof asset for a contract or dependency edge.

    Records provenance: how proved, under which assumptions, when
    last validated, and which trust boundary was used.

    Multiple Evidence entries can exist per node (e.g. a stub contract
    ASSUMED + a Coq lemma USER_AXIOM + an SMT unrolling check).
    The [active] flag distinguishes the currently-operative proof;
    historical evidence keeps [active=False].
    """
    kind: EvidenceKind
    status: ProofStatus = ProofStatus.UNKNOWN

    # ── Provenance ──
    validated_at: str = ""     # ISO timestamp of last successful check
    assumptions: list[str] = field(default_factory=list)  # callee names assumed proved

    # ── SMT / theory-SMT ──
    query_hash: str = ""
    solver: str = ""
    smt2_path: str = ""       # path to .smt2 script (for re-verification)

    # ── Coq ──
    coq_file: str = ""        # .v file containing the proof
    lemma_name: str = ""      # Lemma name within the .v file

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
        return all(e.status.is_proved for e in self.evidence) if self.evidence else False


@dataclass
class ContractNode:
    """A verified function with its contract and evidence."""
    spec: ContractSpec
    evidence: list[Evidence] = field(default_factory=list)
    edges: list[ContractEdge] = field(default_factory=list)

    # Hash keys for incremental verification (replaces cache.py FunctionHashes)
    body_hash: str = ""
    contract_hash: str = ""
    local_assert_hash: str = ""
    callee_contract_hashes: dict[str, str] = field(default_factory=dict)
    timestamp: float = 0.0  # when last verified

    @property
    def cache_key(self) -> str:
        """Deterministic key combining all hash dimensions."""
        parts = [
            self.body_hash,
            self.contract_hash,
            self.local_assert_hash,
            json.dumps(dict(sorted(self.callee_contract_hashes.items()))),
        ]
        return hashlib.sha256("|".join(parts).encode()).hexdigest()

    @property
    def proved(self) -> bool:
        """A node is proved iff it has standalone evidence OR all edges
        are proved and all callee nodes are proved (checked at graph level).

        Stub/axiom nodes count as proved (trusted assumptions)."""
        has_standalone = any(e.status.is_proved for e in self.evidence)
        is_trusted = any(e.status.is_assumed for e in self.evidence)
        if is_trusted:
            return True
        all_edges_proved = all(e.proved for e in self.edges) if self.edges else True
        return has_standalone or (all_edges_proved and not self.edges)

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
        and leaves have standalone evidence or are trusted assumptions.
        Returns {node: [issues]}."""
        issues: dict[str, list[str]] = {}
        for name, node in self.nodes.items():
            node_issues: list[str] = []

            # Leaf check
            if not node.edges:
                has_proof = any(e.status.is_proved for e in node.evidence)
                is_trusted = any(e.status.is_assumed for e in node.evidence)
                if not has_proof and not is_trusted:
                    node_issues.append("leaf node has no evidence (neither proved nor assumed)")

            # Edge check
            for edge in node.edges:
                if not edge.proved:
                    node_issues.append(f"edge to {edge.callee_name} unproved")
                callee = self.nodes.get(edge.callee_name)
                if callee is None:
                    node_issues.append(f"callee {edge.callee_name} missing from graph")
                elif not callee.proved:
                    node_issues.append(f"callee {edge.callee_name} not proved")

            if node_issues:
                issues[name] = node_issues

        return issues

    def trust_base(self) -> list[str]:
        """Return the set of assumptions — all nodes whose contract is
        assumed rather than proved (stubs, user axioms)."""
        return [
            name for name, node in self.nodes.items()
            if any(e.status.is_assumed for e in node.evidence)
        ]

    # ── STALE propagation ──────────────────────────────────────

    def get_callers(self, callee_name: str) -> list[str]:
        """Return all nodes that have an edge to [callee_name]."""
        callers: list[str] = []
        for name, node in self.nodes.items():
            for edge in node.edges:
                if edge.callee_name == callee_name:
                    callers.append(name)
                    break
        return callers

    def get_transitive_callers(self, name: str) -> list[str]:
        """Return all transitive callers (direct + indirect). Excludes [name]."""
        visited: set[str] = set()
        stack = list(self.get_callers(name))
        while stack:
            current = stack.pop()
            if current in visited:
                continue
            visited.add(current)
            for caller in self.get_callers(current):
                if caller not in visited:
                    stack.append(caller)
        return list(visited)

    def get_callees(self, name: str) -> list[str]:
        """Return direct callees of [name]."""
        node = self.nodes.get(name)
        return [e.callee_name for e in node.edges] if node else []

    def mark_stale(self, name: str) -> set[str]:
        """Mark all transitive callers of [name] as STALE (not [name] itself).
        Returns the set of node names that were affected."""
        affected: set[str] = set()
        for caller in self.get_callers(name):
            self._mark_stale_recursive(caller, affected)
        return affected

    def _mark_stale_recursive(self, name: str, affected: set[str]) -> None:
        if name in affected:
            return
        affected.add(name)
        node = self.nodes.get(name)
        if node:
            for e in node.evidence:
                if e.status.is_proved:
                    e.status = ProofStatus.STALE
            for e in node.edges:
                for ev in e.evidence:
                    if ev.status.is_proved:
                        ev.status = ProofStatus.STALE
        for caller in self.get_callers(name):
            self._mark_stale_recursive(caller, affected)

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

    # ── Serialisation / Persistence ─────────────────────────────

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
                        {"kind": e.kind.value, "status": e.status.value,
                         "query_hash": e.query_hash, "lemma": e.lemma_name,
                         "coq_file": e.coq_file, "notes": e.notes}
                        for e in node.evidence
                    ],
                    "edges": [
                        {"callee": e.callee_name, "target": e.target,
                         "evidence": [{"kind": ev.kind.value, "status": ev.status.value} for ev in e.evidence]}
                        for e in node.edges
                    ],
                    "hashes": {
                        "body": node.body_hash,
                        "contract": node.contract_hash,
                        "local_assert": node.local_assert_hash,
                        "callee_contracts": node.callee_contract_hashes,
                    },
                    "timestamp": node.timestamp,
                }
                for name, node in self.nodes.items()
            }
        }

    def save(self, path: str | Path) -> None:
        """Persist to a JSON file."""
        with open(path, 'w') as f:
            json.dump(self.to_dict(), f, indent=2)

    @classmethod
    def load(cls, path: str | Path) -> "EvidenceGraph":
        """Load from a JSON file.  Returns empty graph if file missing."""
        graph = cls()
        if not os.path.exists(path):
            return graph
        with open(path) as f:
            data = json.load(f)
        for name, nd in data.get("nodes", {}).items():
            spec_data = nd["spec"]
            spec = ContractSpec(
                name=name,
                params=spec_data.get("params", []),
                pre_coq=spec_data.get("pre", "True"),
                post_coq=spec_data.get("post", "True"),
                reads=spec_data.get("reads", []),
                writes=spec_data.get("writes", []),
            )
            evidence = [
                Evidence(
                    kind=EvidenceKind(e["kind"]),
                    status=ProofStatus(e["status"]),
                    query_hash=e.get("query_hash", ""),
                    lemma_name=e.get("lemma", ""),
                    coq_file=e.get("coq_file", ""),
                    notes=e.get("notes", ""),
                )
                for e in nd.get("evidence", [])
            ]
            edges = [
                ContractEdge(
                    callee_name=e["callee"],
                    callee_spec=ContractSpec(name=e["callee"]),
                    target=e.get("target", ""),
                    evidence=[
                        Evidence(
                            kind=EvidenceKind(ev["kind"]),
                            status=ProofStatus(ev["status"]),
                        )
                        for ev in e.get("evidence", [])
                    ],
                )
                for e in nd.get("edges", [])
            ]
            hashes = nd.get("hashes", {})
            node = ContractNode(
                spec=spec, evidence=evidence, edges=edges,
                body_hash=hashes.get("body", ""),
                contract_hash=hashes.get("contract", ""),
                local_assert_hash=hashes.get("local_assert", ""),
                callee_contract_hashes=hashes.get("callee_contracts", {}),
                timestamp=nd.get("timestamp", 0.0),
            )
            graph.nodes[name] = node
        return graph


# ── Project-scoped graph registry ─────────────────────────────────

_GRAPHS: dict[str, EvidenceGraph] = {}

_ROOT_MARKERS = ["pyproject.toml"]

def find_project_root(start: str | Path = ".") -> Path:
    """Walk up from [start] until a project-root marker is found.
    Falls back to the starting directory if no marker found."""
    current = Path(start).resolve()
    # If start is a file, begin search from its parent directory
    if current.is_file():
        current = current.parent
    for _ in range(20):  # max depth
        for marker in _ROOT_MARKERS:
            if (current / marker).exists():
                return current
        parent = current.parent
        if parent == current:  # filesystem root
            break
        current = parent
    return Path(start).resolve()

def get_graph(project_root: str | Path = ".") -> EvidenceGraph:
    """Return the evidence graph for [project_root], loading from disk if
    a persisted copy exists at <root>/.axiomander/evidence_graph.json.
    If [project_root] is not a known project (no pyproject.toml above it),
    returns an in-memory-only graph (not persisted)."""
    root = find_project_root(project_root)
    is_project = (root / "pyproject.toml").exists()
    cache_key = str(root) if is_project else f"_mem_{id(root)}"
    if cache_key not in _GRAPHS:
        if is_project:
            path = root / ".axiomander" / "evidence_graph.json"
            _GRAPHS[cache_key] = EvidenceGraph.load(path)
        else:
            _GRAPHS[cache_key] = EvidenceGraph()
    return _GRAPHS[cache_key]

def save_graph(project_root: str | Path = ".") -> None:
    """Persist the evidence graph to disk.  No-op for non-project roots."""
    root = find_project_root(project_root)
    if not (root / "pyproject.toml").exists():
        return  # temporary / outside project — not persisted
    cache_key = str(root)
    graph = _GRAPHS.get(cache_key)
    if graph is None:
        return
    dir_path = root / ".axiomander"
    dir_path.mkdir(parents=True, exist_ok=True)
    graph.save(dir_path / "evidence_graph.json")
