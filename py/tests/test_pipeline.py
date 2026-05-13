"""Test harness — exercises the verification pipeline directly (no MCP).

Run with: eval $(opam env); PYTHONPATH=py .venv/bin/python -m pytest py/tests/ -v
"""

import ast
import os
import sys
import textwrap
from pathlib import Path

# Make oracle/ importable directly
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import pytest

from oracle.contract_linter import ContractLinter, AssertInfo
from oracle.python_to_imp import python_to_imp
from oracle.mcp_server import (
    _generate_coq, _classify_assert, _expand_params,
    _verify_function,
)
from oracle.reporting import GoalStatus, ProofLevel


BUILD_DIR = Path(__file__).resolve().parent.parent.parent / "_build" / "default" / "coq"


def run_verification(source: str, func_name: str) -> GoalStatus | None:
    tree = ast.parse(source)
    func_node = next(
        n for n in ast.walk(tree)
        if isinstance(n, ast.FunctionDef) and n.name == func_name
    )
    params = [arg.arg for arg in func_node.args.args]
    expanded, _, _, _, _ = _expand_params(tree, params, func_node)
    linter_pre = ContractLinter(expanded, "precondition")
    linter_post = ContractLinter(expanded, "postcondition")
    lint_results = []
    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Assert):
            cls = _classify_assert(func_node, stmt)
            linter = linter_pre if cls == "precondition" else linter_post
            lr = linter.lint_expression(stmt.test)
            lint_results.append(AssertInfo(
                node=stmt, lineno=stmt.lineno, col_offset=stmt.col_offset,
                classification=cls, lint_result=lr,
            ))
    os.environ.setdefault("REFACTORING_ROBOTS_ROOT", str(BUILD_DIR.parent.parent))
    return _verify_function(source, func_name, None)


EXAMPLES = [
    # ── Core examples ──────────────────────────────────────────────
    ("add", "def add(a,b):\n assert True\n result = a+b\n assert result == a+b\n return result"),
    ("max_of_two", "def max_of_two(a,b):\n assert a>=0; assert b>=0\n if a>=b: result=a\n else: result=b\n assert result>=a; assert result>=b\n return result"),
    ("clamp", "def clamp(val,lo,hi):\n assert lo<=hi\n if val<lo: result=lo\n elif val>hi: result=hi\n else: result=val\n assert lo<=result<=hi\n return result"),
    ("sum_to", "def sum_to(n):\n assert n>=0\n acc=0; i=0\n while i<n:\n  assert acc==i*(i+1)//2; assert i<=n\n  i=i+1; acc=acc+i\n assert acc==n*(n+1)//2; assert i==n\n return acc"),
    ("count_to", "def count_to(n):\n assert n>=0\n i=0\n for _ in range(n): i=i+1\n assert i==n\n return i"),
    ("fill_list", "def fill_list(n):\n assert n>=0\n xs=[]; i=0\n while i<n:\n  assert len(xs)==i; assert i<=n\n  xs.append(i); i=i+1\n result=len(xs)\n assert result==n\n return result"),
    ("count_append", "def count_append(x):\n assert x>0\n items=[]; items.append(x)\n result=len(items)\n assert result==1\n return result"),
    ("range_build", "def range_build(n):\n assert n>=0\n xs=[]\n for i in range(n):\n  xs.append(i)\n assert len(xs)==n\n return xs"),

    # ── Bookwyrm patterns ──────────────────────────────────────────
    ("filter_items", "class Item: value: int\ndef filter_items(items: list[Item], threshold: int):\n assert True\n count=0;i=0\n while i<len(items):\n  assert count<=i;assert i<=len(items)\n  if items[i].value>threshold:count+=1\n  i+=1\n result=count\n assert result<=len(items)\n return result"),
    ("total_chars", "def total_chars(text: str):\n assert len(text)>0\n total=0;i=0\n while i<len(text):\n  assert total==i;assert i<=len(text)\n  total+=1;i+=1\n result=total\n assert result==len(text)\n return result"),
    ("first_char", "def first_char(text: str):\n assert len(text)>0\n result=text[0]\n assert True\n return result"),
    # Pattern: for-range list copy with indexing
    ("list_copy", '''def list_copy(src):
    assert True
    dest = []
    for i in range(5):
        dest.append(i)
    result = len(dest)
    assert result == 5
    return result'''),

    # ── Augmented assignment ───────────────────────────────────────
    ("inc_loop", '''def inc_loop(n):
    assert n >= 0
    i = 0
    while i < n:
        assert i <= n
        i += 1
    assert i == n
    return i'''),
]


@pytest.mark.parametrize("name,source", EXAMPLES)
def test_verification_passes(name, source):
    goal = run_verification(source, name)
    assert goal is not None, f"None return for {name}"
    assert goal.is_proved(), f"Not proved ({goal.level}): {goal.error_detail[:200]}"
    assert goal.level == ProofLevel.LEVEL1_LTAC
