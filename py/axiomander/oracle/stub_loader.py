"""
Library stub loader — parses .pyi stub files to extract contracts for external functions.

Stubs use docstring-based contracts in .pyi files. The pipeline reads these
to provide pre/post conditions for external functions, enabling cross-module
verification without black holes.

Stub format::

    # stubs/math.pyi
    def sqrt(x: float) -> float:
        \"\"\"requires: x >= 0
        ensures: result >= 0\"\"\"
        ...
"""

import ast
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


@dataclass
class StubContract:
    name: str
    params: list[str]
    pre_raw: str       # raw Python expression from "requires:" section
    post_raw: str      # raw Python expression from "ensures:" section
    reads: list[str] = field(default_factory=list)   # variables/f_fields the function reads
    writes: list[str] = field(default_factory=list)  # variables/f_fields the function may mutate
    source_file: str = ""


def _parse_docstring_contract(docstring: str) -> tuple[str, str, list[str], list[str]]:
    """Extract 'requires:', 'ensures:', 'reads:', 'writes:' sections from a docstring.

    Returns (pre_raw, post_raw, reads_list, writes_list).
    """
    pre_raw = "True"
    post_raw = "True"
    reads_list: list[str] = []
    writes_list: list[str] = []

    # Match "requires: <expr>" — handles optional indentation
    requires_match = re.search(r'requires:\s*(.+?)(?=\n\s*\n|\n\s*ensures:|\n\s*reads:|\n\s*writes:|\Z)', docstring, re.DOTALL)
    if requires_match:
        pre_raw = requires_match.group(1).strip()

    ensures_match = re.search(r'ensures:\s*(.+?)(?=\n\s*\n|\n\s*reads:|\n\s*writes:|\Z)', docstring, re.DOTALL)
    if ensures_match:
        post_raw = ensures_match.group(1).strip()

    reads_match = re.search(r'reads:\s*(.+?)(?=\n\s*\n|\n\s*writes:|\Z)', docstring, re.DOTALL)
    if reads_match:
        reads_str = reads_match.group(1).strip()
        if reads_str and reads_str != "(none)":
            reads_list = [r.strip() for r in reads_str.split(",")]

    writes_match = re.search(r'writes:\s*(.+?)(?=\n\s*\n|\Z)', docstring, re.DOTALL)
    if writes_match:
        writes_str = writes_match.group(1).strip()
        if writes_str and writes_str != "(none)":
            writes_list = [w.strip() for w in writes_str.split(",")]

    return pre_raw, post_raw, reads_list, writes_list


def _parse_py_expression_to_coq(expr_str: str, params: list[str], is_post: bool = False) -> str:
    """Parse a Python expression string (contract language subset) to a Coq expression.

    Uses the contract_linter to validate and translate.
    Falls back to raw string with manual scoping if parsing fails.
    """
    if expr_str == "True":
        return "True"

    try:
        expr_node = ast.parse(expr_str.strip(), mode='eval').body
    except SyntaxError:
        return _manual_scope(expr_str, params, is_post)

    from .contract_linter import ContractLinter
    role = "postcondition" if is_post else "precondition"
    linter = ContractLinter(params, role)
    result = linter.lint_expression(expr_node)
    if result.is_valid and result.coq_translation:
        return result.coq_translation

    return _manual_scope(expr_str, params, is_post)


def _manual_scope(expr_str: str, params: list[str], is_post: bool = False) -> str:
    """Fallback: manually scope variables in a Coq expression."""
    import re
    result = expr_str
    for p in params:
        result = re.sub(
            rf'(?<![a-zA-Z0-9_"%]){re.escape(p)}(?![a-zA-Z0-9_"%])',
            f's "{p}"%string', result
        )
    if is_post:
        result = re.sub(
            r'(?<![a-zA-Z0-9_"%])result(?![a-zA-Z0-9_"%])',
            's "result"%string', result
        )
    return result


class StubLoader:
    """Loads and caches contracts from .pyi stub files.

    Usage::

        loader = StubLoader([path_to_stubs])
        contracts = loader.get_contract("sqrt")
        # → (["x"], "x >= 0", "result >= 0")
    """

    def __init__(self, stub_dirs: list[Path] | None = None):
        """Initialize the loader.

        If stub_dirs is None, looks for 'stubs/' directories in:
        - AXIOMANDER_ROOT/stubs/
        - Current working directory
        - The project's py/ directory
        """
        self._contracts: dict[str, StubContract] = {}
        self._search_dirs: list[Path] = []

        if stub_dirs:
            self._search_dirs = [Path(d) for d in stub_dirs if Path(d).exists()]
        else:
            import os
            root = Path(os.environ.get(
                "AXIOMANDER_ROOT",
                str(Path(__file__).resolve().parent.parent.parent.parent),
            ))
            candidates = [
                root / "stubs",
                Path.cwd() / "stubs",
                root / "py" / "stubs",
            ]
            for d in candidates:
                if d.exists():
                    self._search_dirs.append(d)

        self._load_all()

    def _load_all(self) -> None:
        """Load all .pyi files from search directories."""
        for stub_dir in self._search_dirs:
            for pyi_file in stub_dir.glob("*.pyi"):
                self._load_file(pyi_file)

    def _load_file(self, path: Path) -> None:
        """Load contracts from a single .pyi file."""
        try:
            tree = ast.parse(path.read_text())
        except SyntaxError:
            return

        for node in ast.iter_child_nodes(tree):
            if isinstance(node, ast.FunctionDef):
                contract = self._extract_contract(node, str(path))
                if contract:
                    self._contracts[contract.name] = contract

    def _extract_contract(self, node: ast.FunctionDef, source_file: str) -> StubContract | None:
        """Extract contract from a function definition in a stub file."""
        params = [arg.arg for arg in node.args.args]
        pre_raw = "True"
        post_raw = "True"
        reads: list[str] = []
        writes: list[str] = []

        # Check for docstring with requires/ensures
        if node.body:
            first = node.body[0]
            if isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant):
                if isinstance(first.value.value, str):
                    pre_raw, post_raw, reads, writes = _parse_docstring_contract(first.value.value)

        if pre_raw == "True" and post_raw == "True" and not reads and not writes:
            return None

        return StubContract(
            name=node.name,
            params=params,
            pre_raw=pre_raw,
            post_raw=post_raw,
            reads=reads,
            writes=writes,
            source_file=source_file,
        )

    def get_contract(self, func_name: str) -> tuple[list[str], str, str] | None:
        """Get (params, pre_coq, post_coq) for a function.

        Returns None if the function has no stub contract.
        """
        sc = self._contracts.get(func_name)
        if sc is None:
            return None

        pre_coq = _parse_py_expression_to_coq(sc.pre_raw, sc.params, is_post=False)
        post_coq = _parse_py_expression_to_coq(sc.post_raw, sc.params, is_post=True)
        return (sc.params, pre_coq, post_coq)

    def get_contract_info(self, func_name: str) -> StubContract | None:
        """Get the full StubContract object (includes reads/writes frame info)."""
        return self._contracts.get(func_name)

    def all_contracts(self) -> dict[str, tuple[list[str], str, str]]:
        """Return all known stub contracts."""
        result: dict[str, tuple[list[str], str, str]] = {}
        for name, sc in self._contracts.items():
            pre = _parse_py_expression_to_coq(sc.pre_raw, sc.params, is_post=False)
            post = _parse_py_expression_to_coq(sc.post_raw, sc.params, is_post=True)
            result[name] = (sc.params, pre, post)
        return result

    def has_contract(self, func_name: str) -> bool:
        return func_name in self._contracts

    @property
    def known_functions(self) -> list[str]:
        return sorted(self._contracts.keys())


# Singleton instance for the pipeline
_stub_loader: StubLoader | None = None


def get_stub_loader() -> StubLoader:
    global _stub_loader
    if _stub_loader is None:
        _stub_loader = StubLoader()
    return _stub_loader
