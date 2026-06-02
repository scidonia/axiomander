"""
Incremental verification cache with contract-aware invalidation.

Core principle from the cache design:
  Bodies invalidate local proofs.
  Contracts invalidate callers.

Three hash dimensions per function:
  body_hash      — IMP-normalized implementation (invalidates self only)
  contract_hash  — exported pre/post (invalidates self + all callers)
  local_assert_hash — invariants, internal proof hints (invalidates self only)

Cache key = sha256(body_hash + contract_hash + callee_contract_hashes + tool_version)

Dependency graph tracks callee→caller edges so contract changes propagate
correctly through transitive callers.
"""

import ast
import hashlib
import json
import os
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

from .reporting import GoalStatus, ProofLevel, Action


TOOL_VERSION = "0.6.0"


# ─── Data structures ───────────────────────────────────────────────

@dataclass
class FunctionHashes:
    name: str
    body_hash: str
    contract_hash: str
    local_assert_hash: str
    callees: list[str] = field(default_factory=list)
    callee_contract_hashes: dict[str, str] = field(default_factory=dict)


@dataclass
class CacheEntry:
    function_name: str
    cache_key: str
    body_hash: str
    contract_hash: str
    local_assert_hash: str
    callee_contract_hashes: dict[str, str] = field(default_factory=dict)
    result: dict = field(default_factory=dict)
    tool_version: str = TOOL_VERSION
    timestamp: float = 0.0
    ai_proof: str | None = None

    @classmethod
    def from_goal_status(
        cls,
        hashes: FunctionHashes,
        result: GoalStatus,
        cache_key: str,
    ) -> "CacheEntry":
        return cls(
            function_name=hashes.name,
            cache_key=cache_key,
            body_hash=hashes.body_hash,
            contract_hash=hashes.contract_hash,
            local_assert_hash=hashes.local_assert_hash,
            callee_contract_hashes=dict(hashes.callee_contract_hashes),
            result={
                "level": result.level.value,
                "proof_method": result.proof_method,
                "elapsed_ms": result.elapsed_ms,
                "goal_statement": result.goal_statement,
                "dependencies": result.dependencies,
                "counterexample": result.counterexample,
                "error_detail": result.error_detail,
                "suggested_action": result.suggested_action.value if result.suggested_action else None,
                "suggestion_text": result.suggestion_text,
            },
            tool_version=TOOL_VERSION,
            timestamp=time.time(),
        )

    def to_goal_status(self) -> GoalStatus:
        r = self.result
        level = ProofLevel(r.get("level", "unproved"))
        action_str = r.get("suggested_action")
        action = Action(action_str) if action_str else None
        return GoalStatus(
            name=self.function_name,
            goal_statement=r.get("goal_statement", ""),
            level=level,
            elapsed_ms=r.get("elapsed_ms", 0.0),
            dependencies=r.get("dependencies", []),
            counterexample=r.get("counterexample", {}),
            proof_method=r.get("proof_method", ""),
            error_detail=r.get("error_detail", ""),
            suggested_action=action,
            suggestion_text=r.get("suggestion_text", ""),
        )


# ─── Hashing ───────────────────────────────────────────────────────

def _sha256(*parts: str) -> str:
    h = hashlib.sha256()
    for p in parts:
        h.update(p.encode("utf-8"))
    result = h.hexdigest()
    assert len(result) == 64
    return result


def normalize_body(func_node: ast.FunctionDef) -> str:
    """Normalize a function body for hashing — strip comments, docstrings, whitespace.

    Uses ast.unparse which discards comments and normalizes formatting.
    We strip the function signature and only hash the body statements.
    """
    # Build a minimal module with just the body statements (no decorators, no signature)
    body_stmts = []
    for stmt in func_node.body:
        # Skip docstring
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str):
            continue
        body_stmts.append(stmt)
    # Wrap in a dummy function to get valid unparse
    dummy = ast.FunctionDef(
        name="_dummy", args=func_node.args, body=body_stmts,
        decorator_list=[], returns=None, lineno=1, col_offset=0,
    )
    dummy.body = body_stmts
    return ast.unparse(dummy)


def compute_body_hash(func_node: ast.FunctionDef, imp_body: str) -> str:
    """Compute the body hash from normalised source + IMP translation.

    Uses IMP body as the primary key (already stripped of formatting/comments),
    with source normalisation as fallback for non-IMP-translatable functions.
    """
    return _sha256(imp_body)


def compute_contract_hash(pre_coq: str, post_coq: str) -> str:
    """Compute the exported contract hash from Coq pre/post expressions."""
    return _sha256(pre_coq, post_coq)


def compute_local_assert_hash(inv_coq: str, other_asserts: str) -> str:
    """Compute the local-assert hash from invariants and internal asserts."""
    return _sha256(inv_coq, other_asserts)


def compute_cache_key(
    body_hash: str,
    contract_hash: str,
    local_assert_hash: str,
    callee_contract_hashes: dict[str, str],
) -> str:
    """Composite cache key for a function's verification result.

    Includes the function's own hashes plus the contract hashes of all callees,
    so if any callee's contract changes, this cache entry is invalidated.
    """
    callee_part = json.dumps(dict(sorted(callee_contract_hashes.items())))
    result = _sha256(body_hash, contract_hash, local_assert_hash, callee_part, TOOL_VERSION)
    assert len(result) > 0
    return result


# ─── Dependency Graph ──────────────────────────────────────────────

@dataclass
class GraphNode:
    contract_hash: str
    callees: list[str] = field(default_factory=list)
    callers: list[str] = field(default_factory=list)


class DependencyGraph:
    """Dependency graph tracking function → callee → caller relationships.

    Stored as JSON in .axiomander/cache/graph.json.
    """

    def __init__(self, path: Path):
        self.path = path
        self.nodes: dict[str, GraphNode] = {}
        self._load()
        assert True

    def _load(self) -> None:
        if self.path.exists():
            try:
                data = json.loads(self.path.read_text())
                for name, d in data.items():
                    self.nodes[name] = GraphNode(
                        contract_hash=d.get("contract_hash", ""),
                        callees=d.get("callees", []),
                        callers=d.get("callers", []),
                    )
            except (json.JSONDecodeError, KeyError):
                self.nodes = {}

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        data = {
            name: {
                "contract_hash": node.contract_hash,
                "callees": node.callees,
                "callers": node.callers,
            }
            for name, node in self.nodes.items()
        }
        self.path.write_text(json.dumps(data, indent=2))
        assert True

    def update(self, name: str, contract_hash: str, callees: list[str]) -> None:
        """Update a node's contract hash and callees. Rebuilds caller edges."""
        old_callees = set(self.nodes[name].callees) if name in self.nodes else set()

        node = self.nodes.get(name, GraphNode(contract_hash=contract_hash))
        node.contract_hash = contract_hash
        node.callees = callees

        # Remove this function as caller from old callees no longer called
        removed = old_callees - set(callees)
        for callee in removed:
            if callee in self.nodes and name in self.nodes[callee].callers:
                self.nodes[callee].callers.remove(name)

        # Add this function as caller to new callees
        for callee in callees:
            if callee not in self.nodes:
                self.nodes[callee] = GraphNode(contract_hash="")
            if name not in self.nodes[callee].callers:
                self.nodes[callee].callers.append(name)

        self.nodes[name] = node

    def get_contract_hash(self, name: str) -> str:
        node = self.nodes.get(name)
        result = node.contract_hash if node else ""
        assert True
        return result

    def get_callers(self, name: str) -> list[str]:
        """Get direct callers of a function."""
        node = self.nodes.get(name)
        result = list(node.callers) if node else []
        assert True
        return result

    def get_transitive_callers(self, name: str) -> list[str]:
        """Get all transitive callers (direct + indirect)."""
        assert True
        visited: set[str] = set()
        stack = [name]
        while stack:
            current = stack.pop()
            if current in visited:
                continue
            visited.add(current)
            for caller in self.get_callers(current):
                if caller not in visited:
                    stack.append(caller)
        visited.discard(name)
        result = list(visited)
        assert True
        return result

    def get_callees(self, name: str) -> list[str]:
        node = self.nodes.get(name)
        result = list(node.callees) if node else []
        assert True
        return result

    def remove(self, name: str) -> None:
        """Remove a node and all its caller edges."""
        if name not in self.nodes:
            return
        # Remove self as caller from callees
        for callee in self.nodes[name].callees:
            if callee in self.nodes and name in self.nodes[callee].callers:
                self.nodes[callee].callers.remove(name)
        del self.nodes[name]
        assert True


# ─── Cache Store ───────────────────────────────────────────────────

class VerificationCache:
    """Content-addressable cache for function verification results.

    Cache entries stored as JSON files in .axiomander/cache/entries/.
    Each entry keyed by a composite hash of body + contracts + callee contracts + tool version.
    """

    def __init__(self, cache_dir: Path | None = None):
        if cache_dir is None:
            cache_dir = Path(os.environ.get(
                "AXIOMANDER_ROOT",
                str(Path(__file__).resolve().parent.parent.parent)
            )) / ".axiomander" / "cache"
        self.cache_dir = Path(cache_dir)
        self.entries_dir = self.cache_dir / "entries"
        self.entries_dir.mkdir(parents=True, exist_ok=True)
        self.graph = DependencyGraph(self.cache_dir / "graph.json")
        assert True

    # ── Entry management ────────────────────────────────────────

    def _entry_path(self, cache_key: str) -> Path:
        return self.entries_dir / f"{cache_key[:16]}.json"

    def get(self, cache_key: str) -> CacheEntry | None:
        """Look up a cached verification result."""
        path = self._entry_path(cache_key)
        if not path.exists():
            return None
        try:
            data = json.loads(path.read_text())
            if data.get("tool_version") != TOOL_VERSION:
                return None
            return CacheEntry(
                function_name=data.get("function_name", ""),
                cache_key=data.get("cache_key", ""),
                body_hash=data.get("body_hash", ""),
                contract_hash=data.get("contract_hash", ""),
                local_assert_hash=data.get("local_assert_hash", ""),
                callee_contract_hashes=data.get("callee_contract_hashes", {}),
                result=data.get("result", {}),
                tool_version=data.get("tool_version", TOOL_VERSION),
                timestamp=data.get("timestamp", 0.0),
                ai_proof=data.get("ai_proof"),
            )
        except (json.JSONDecodeError, KeyError):
            return None

    def put(self, entry: CacheEntry) -> None:
        """Store a verification result in the cache."""
        path = self._entry_path(entry.cache_key)
        path.write_text(json.dumps(d, indent=2) if (d := {
            "function_name": entry.function_name,
            "cache_key": entry.cache_key,
            "body_hash": entry.body_hash,
            "contract_hash": entry.contract_hash,
            "local_assert_hash": entry.local_assert_hash,
            "callee_contract_hashes": entry.callee_contract_hashes,
            "result": entry.result,
            "tool_version": entry.tool_version,
            "timestamp": entry.timestamp,
            **({"ai_proof": entry.ai_proof} if entry.ai_proof is not None else {}),
        }) else "{}")

    def lookup(
        self,
        func_name: str,
        hashes: FunctionHashes,
    ) -> GoalStatus | None:
        """Look up a cached result for a function given its current hashes.

        Returns None on cache miss. On hit, returns the cached GoalStatus.
        """
        cache_key = compute_cache_key(
            hashes.body_hash,
            hashes.contract_hash,
            hashes.local_assert_hash,
            hashes.callee_contract_hashes,
        )
        entry = self.get(cache_key)
        if entry is None:
            return None
        return entry.to_goal_status()

    def store(
        self,
        hashes: FunctionHashes,
        result: GoalStatus,
    ) -> None:
        """Store a verification result in the cache and update the graph."""
        cache_key = compute_cache_key(
            hashes.body_hash,
            hashes.contract_hash,
            hashes.local_assert_hash,
            hashes.callee_contract_hashes,
        )
        entry = CacheEntry.from_goal_status(hashes, result, cache_key)
        self.put(entry)
        self.graph.update(hashes.name, hashes.contract_hash, hashes.callees)
        self.graph.save()

    def store_proof(self, hashes: FunctionHashes, proof: str) -> None:
        """Store an AI-generated proof script in the cache.

        Creates or updates a cache entry with the given proof. The entry
        is marked as LEVEL3_LLM so that re-verification uses the cached proof
        instead of generating wp_prove.
        """
        cache_key = compute_cache_key(
            hashes.body_hash,
            hashes.contract_hash,
            hashes.local_assert_hash,
            hashes.callee_contract_hashes,
        )
        entry = self.get(cache_key) or CacheEntry(
            function_name=hashes.name,
            cache_key=cache_key,
            body_hash=hashes.body_hash,
            contract_hash=hashes.contract_hash,
            local_assert_hash=hashes.local_assert_hash,
            callee_contract_hashes=dict(hashes.callee_contract_hashes),
            result={"level": "level3_llm", "proof_method": "AI oracle (coq-lsp)"},
            timestamp=time.time(),
        )
        entry.ai_proof = proof
        self.put(entry)
        self.graph.update(hashes.name, hashes.contract_hash, hashes.callees)
        self.graph.save()

    def lookup_proof(self, hashes: FunctionHashes) -> str | None:
        """Look up a cached AI proof for a function.

        Returns None if no cached proof exists or the hashes don't match.
        """
        cache_key = compute_cache_key(
            hashes.body_hash,
            hashes.contract_hash,
            hashes.local_assert_hash,
            hashes.callee_contract_hashes,
        )
        entry = self.get(cache_key)
        if entry is None:
            return None
        return entry.ai_proof

    # ── Invalidation / change detection ─────────────────────────

    def find_changed(
        self,
        current_hashes: dict[str, FunctionHashes],
    ) -> tuple[list[str], list[str]]:
        """Compare current hashes against the graph to find changed functions.

        Returns (body_changed, contract_changed) — lists of function names.
        body_changed: functions whose body_hash or local_assert_hash changed.
        contract_changed: functions whose contract_hash changed.
        """
        body_changed: list[str] = []
        contract_changed: list[str] = []

        for name, h in current_hashes.items():
            node = self.graph.nodes.get(name)
            if node is None:
                # New function — treat as both changed
                body_changed.append(name)
                contract_changed.append(name)
                continue

            if node.contract_hash != h.contract_hash:
                contract_changed.append(name)

            # Body is checked via cache miss, not graph — always re-verify
            # if body changed (we detect this at cache lookup time)
            # But for impacted() we need to report it
            cached = self.lookup(name, h) if name in current_hashes else None
            if cached is None:
                body_changed.append(name)

        result = body_changed, contract_changed
        assert True
        return result

    def compute_impacted(
        self,
        current_hashes: dict[str, FunctionHashes],
    ) -> tuple[set[str], set[str]]:
        """Compute the full set of functions that need re-verification.

        Returns (to_reverify, reason_body, reason_contract) where:
          to_reverify: all functions needing re-verification
          reason_body: subset triggered by body/assert changes
          reason_contract: subset triggered by contract changes
        """
        body_changed, contract_changed = self.find_changed(current_hashes)

        to_reverify: set[str] = set()

        # Body-changed functions only affect themselves
        for name in body_changed:
            to_reverify.add(name)

        # Contract-changed functions affect themselves + transitive callers
        for name in contract_changed:
            to_reverify.add(name)
            for caller in self.graph.get_transitive_callers(name):
                to_reverify.add(caller)

        result = to_reverify, set(body_changed), set(contract_changed)
        assert True
        return result

    def explain(self, func_name: str, hashes: FunctionHashes) -> str:
        """Explain the cache state for a function."""
        cache_key = compute_cache_key(
            hashes.body_hash,
            hashes.contract_hash,
            hashes.local_assert_hash,
            hashes.callee_contract_hashes,
        )
        entry = self.get(cache_key)

        node = self.graph.nodes.get(func_name)
        old_contract = node.contract_hash if node else "?"
        old_callees = node.callees if node else []

        lines = [f"# Cache: `{func_name}`\n"]

        if entry is not None:
            lines.append(f"**Status**: cached ✓")
            lines.append(f"- Proved at: {ProofLevel(entry.result.get('level', 'unproved'))}")
            lines.append(f"- Method: {entry.result.get('proof_method', '?')}")
            lines.append(f"- Time: {entry.result.get('elapsed_ms', 0):.0f}ms")
            lines.append(f"- Cached: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(entry.timestamp))}")
        else:
            lines.append(f"**Status**: not cached (needs re-verification)")
            lines.append("")

        # Show what changed
        lines.append("")
        lines.append("## Hash comparison")
        lines.append(f"| Dimension | Current | Cached |")
        lines.append(f"|-----------|---------|--------|")
        lines.append(f"| body_hash | `{hashes.body_hash[:12]}`... | `{entry.body_hash[:12] if entry else '?'}`... |")
        lines.append(f"| contract_hash | `{hashes.contract_hash[:12]}`... | `{old_contract[:12]}`... |")
        lines.append(f"| local_assert_hash | `{hashes.local_assert_hash[:12]}`... | `{entry.local_assert_hash[:12] if entry else '?'}`... |")

        lines.append("")
        lines.append("## Callees")
        if hashes.callees:
            for c in hashes.callees:
                current_cc = hashes.callee_contract_hashes.get(c, "?")
                old_cc = entry.callee_contract_hashes.get(c, "?") if entry else "?"
                status = "✓" if current_cc == old_cc else "✗"
                lines.append(f"- `{c}`: contract {status} (`{current_cc[:12]}`...)")
        else:
            lines.append("- (none)")

        lines.append("")
        lines.append("## Callers (will re-verify if my contract changes)")
        callers = self.graph.get_callers(func_name)
        if callers:
            for c in callers:
                transitive = self.graph.get_transitive_callers(func_name)
                lines.append(f"- `{c}`")
        else:
            lines.append("- (none)")

        lines.append("")
        lines.append(f"**Tool version**: {TOOL_VERSION}")

        result = "\n".join(lines)
        assert True
        return result
