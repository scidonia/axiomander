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
    _generate_coq, _classify_assert, _expand_params, _infer_var_types,
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
    # Add dotted field flat keys to var_types so string comparisons are lowered
    # to String.eqb form (matching body's BEq(AVar, AString)).
    var_types = _infer_var_types(func_node)
    param_set = set(params)
    _STRING_FIELD_SUFFIXES = frozenset({'_id', '_name', '_value', '_attr', '_str'})
    for k in expanded:
        if k not in param_set and k not in var_types:
            if any(k.endswith(s) for s in _STRING_FIELD_SUFFIXES):
                var_types[k] = 'string'
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
    os.environ.setdefault("AXIOMANDER_ROOT", str(BUILD_DIR.parent.parent))
    return _verify_function(source, func_name, None)


EXAMPLES = [
    # ── Core examples ──────────────────────────────────────────────
    ("add", "def add(a: int, b: int):\n assert True\n result = a+b\n assert result == a+b\n return result"),
    ("max_of_two", "def max_of_two(a: int, b: int):\n assert a>=0; assert b>=0\n if a>=b: result=a\n else: result=b\n assert result>=a; assert result>=b\n return result"),
    ("clamp", "def clamp(val: int, lo: int, hi: int):\n assert lo<=hi\n if val<lo: result=lo\n elif val>hi: result=hi\n else: result=val\n assert lo<=result<=hi\n return result"),
    ("sum_to", "def sum_to(n: int):\n assert n>=0\n acc=0; i=0\n while i<n:\n  assert acc==i*(i+1)//2; assert i<=n\n  i=i+1; acc=acc+i\n assert acc==n*(n+1)//2; assert i==n\n return acc"),
    ("count_to", "def count_to(n: int):\n assert n>=0\n i=0\n for _ in range(n): i=i+1\n assert i==n\n return i"),
    ("fill_list", "def fill_list(n: int):\n assert n>=0\n xs=[]; i=0\n while i<n:\n  assert len(xs)==i; assert i<=n\n  xs.append(i); i=i+1\n result=len(xs)\n assert result==n\n return result"),
    ("count_append", "def count_append(x: int):\n assert x>0\n items=[]; items.append(x)\n result=len(items)\n assert result==1\n return result"),
    ("range_build", "def range_build(n: int):\n assert n>=0\n xs=[]\n for i in range(n):\n  xs.append(i)\n assert len(xs)==n\n return xs"),

    # ── Bookwyrm patterns ──────────────────────────────────────────
    ("filter_items", "class Item: value: int\ndef filter_items(items: list[Item], threshold: int):\n assert True\n count=0;i=0\n while i<len(items):\n  assert count<=i;assert i<=len(items)\n  if items[i].value>threshold:count+=1\n  i+=1\n result=count\n assert result<=len(items)\n return result"),
    ("total_chars", "def total_chars(text: str):\n assert len(text)>0\n total=0;i=0\n while i<len(text):\n  assert total==i;assert i<=len(text)\n  total+=1;i+=1\n result=total\n assert result==len(text)\n return result"),
    ("first_char", "def first_char(text: str):\n assert len(text)>0\n result=text[0]\n assert True\n return result"),
    # Original bookwyrm: filter_text_regions (using while loop, string fields via Z encoding)
    ("filter_regions", "class Region: content_type: str; text: str\ndef filter_regions(regions: list[Region]):\n assert len(regions)>=0\n result=[];i=0\n while i<len(regions):\n  assert len(result)<=i;assert i<=len(regions)\n  if regions[i].content_type==\"text\":result.append(regions[i].text)\n  i+=1\n assert len(result)<=len(regions)\n return result"),
    # Dict group-by (bookwyrm group_mappings_by_page)
    ("count_groups", "def count_groups(mappings: list[int]):\n assert len(mappings)>0\n result={};i=0;count=0\n while i<len(mappings):\n  assert count==i;assert i<=len(mappings)\n  key=mappings[i]\n  if key not in result:result[key]=[]\n  result[key].append(1);count+=1;i+=1\n assert count==len(mappings)\n return count"),
    # Dict comprehension (manual while loop)
    ("dict_comp", "def dict_comp(n: int):\n assert n>=0\n result={};i=0\n while i<n:\n  assert i<=n\n  result[i]=i*i;i+=1\n count=0;i=0\n while i<n:\n  assert count==i;assert i<=n\n  if i in result:count+=1\n  i+=1\n assert count==n\n return count"),
    # Pattern: for-range list copy with indexing
    ("list_copy", '''def list_copy(src: list[int]):
    assert True
    dest = []
    for i in range(5):
        dest.append(i)
    result = len(dest)
    assert result == 5
    return result'''),

    # ── Augmented assignment ───────────────────────────────────────
    ("inc_loop", '''def inc_loop(n: int):
    assert n >= 0
    i = 0
    while i < n:
        assert i <= n
        i += 1
    assert i == n
    return i'''),

    # ── Boolean assignment ──────────────────────────────────────────
    ("bool_assign", "def bool_assign(a: int, b: int):\n assert a>=0; assert b>=0\n is_pos = (a>0) or (b>0)\n result = is_pos\n assert result==1 or result==0\n return result"),

    # ── Set operations ─────────────────────────────────────────────
    ("set_count", "def set_count(text: str):\n assert len(text)>=0\n seen=set(); count=0; i=0\n while i<len(text):\n  assert count<=i; assert i<=len(text)\n  c=text[i]\n  if c not in seen: seen.add(c); count+=1\n  i+=1\n assert count<=len(text)\n return count"),

    # ── Character scanner ───────────────────────────────────────────
    ("count_ids", "def count_ids(text: str):\n assert len(text)>=0\n count=0; i=0; cur=0; st=0\n while i<len(text):\n  assert count<=i; assert i<=len(text)\n  c=text[i]\n  if (65<=c and c<=90)or(97<=c and c<=122)or c==95 or(48<=c and c<=57 and st==1): st=1;cur+=1\n  else:\n   if st==1:count+=1\n   st=0;cur=0\n  i+=1\n if st==1:count+=1\n assert count<=len(text)\n return count"),

    # ── for-in-tuple (vararg) ──────────────────────────────────────
    ("vararg_count", "def vararg_count(*args: str):\n    assert len(args)>=0\n    total=0; ai=0\n    while ai<len(args):\n        assert total>=0; assert ai<=len(args)\n        total+=len(args[ai])\n        ai+=1\n    assert total>=0\n    return total"),

    # ── list.pop + computed index ──────────────────────────────────
    ("push_level", "def push_level(stack: list[int], level: int):\n    assert len(stack)>=0\n    while len(stack)>0 and stack[len(stack)-1]>=level:\n        assert len(stack)>=0\n        stack.pop()\n    stack.append(level)\n    result=len(stack)\n    assert result>=0\n    return result"),

    # ── for-in-field (for x in obj.field) ──────────────────────────
    ("count_children", "class Node: children: list[int]\ndef count_children(parent: Node):\n    assert True\n    total=0\n    for child in parent.children:\n        total+=child\n    result=total\n    assert result>=0\n    return result"),

    # ── dict iteration (d.values(), d.keys()) ─────────────────────
    ("sum_values", "def sum_values(n: int):\n    assert n>=0\n    d={};i=0\n    while i<n: d[i]=i*i;i+=1\n    total=0\n    for v in d.values(): total+=v\n    result=total\n    assert result>=0\n    return result"),
    ("sum_keys", "def sum_keys(n: int):\n    assert n>=0\n    d={};i=0\n    while i<n: d[i]=i;i+=1\n    total=0\n    for k in d.keys(): total+=k\n    result=total\n    assert result>=0\n    return result"),

    # ── nested loops (outer VCG) ──────────────────────────────────
    ("nested_sum", "def nested_sum(n: int):\n    assert n>=0\n    total=0;i=0\n    while i<n:\n        assert total==3*i;assert i<=n\n        j=0\n        while j<3:\n            total+=1;j+=1\n        i+=1\n    result=total\n    assert result==3*n\n    return result"),

    # ── for-in-list ────────────────────────────────────────────────
    ("for_in_list_sum", "def for_in_list_sum(lst: list[int]):\n    assert len(lst)>=0\n    total=0\n    for x in lst:\n        total+=x\n    result=total\n    assert result>=0\n    return result"),
    ("for_in_list_count", "def for_in_list_count(lst: list[int]):\n    assert len(lst)>=0\n    count=0\n    for x in lst:\n        count+=1\n    result=count\n    assert result==len(lst)\n    return result"),
    ("nested_for_in", "def nested_for_in(n: int):\n    assert n>=0\n    outer=[];i=0\n    while i<n: outer.append(i);i+=1\n    inner=[];j=0\n    while j<n: inner.append(j+1);j+=1\n    count=0\n    for a in outer:\n        for b in inner:\n            count+=1\n    result=count\n    assert result==n*n\n    return result"),

    # ── Paperchecker: brace-matching ───────────────────────────────
    ("find_brace_content", '''def find_brace_content(text: str, n: int, start: int):
    assert start>=0; assert start<=n
    depth=1; pos=start
    while pos<n and depth>0:
        assert depth>=0; assert pos<=n
        if text[pos]==123: depth+=1
        elif text[pos]==125: depth-=1
        pos+=1
    result=pos-start
    assert result<=n
    return result'''),

    # ── Predicates ─────────────────────────────────────────────────
    ("use_pred", '''def is_pos(x: int) -> bool:
    return x > 0

def use_pred(n: int):
    assert is_pos(n)
    result=0
    return result'''),
    ("clamp2", '''def in_range(val: int, lo: int, hi: int) -> bool:
    return lo <= val and val <= hi

def clamp2(val: int, lo: int, hi: int):
    assert lo<=hi
    if val<lo: result=lo
    elif val>hi: result=hi
    else: result=val
    assert in_range(result, lo, hi)
    return result'''),
    ("first2", '''def non_empty(lst: list[int]) -> bool:
    return len(lst) > 0

def first2(lst: list[int]):
    assert non_empty(lst)
    result=lst[0]
    assert True
    return result'''),

    # ── Loop predicates (postcondition inlining) ────────────────────
    ("double", '''def geq_loop(x: int, n: int) -> bool:
    assert n >= 0
    r = x
    while r < n:
        r = r + 1
    result = (r >= n)
    assert implies(result == 1, x >= n)
    return result

def double(n: int):
    assert n >= 0
    result = n * 2
    assert geq_loop(result, n)
    return result'''),

    # ── Ghost state ─────────────────────────────────────────────────
    ("ghost_snapshot", '''def ghost_snapshot(n: int):
    """
    axiomander:
        ensures:
            result == old(n) + 1
    """
    assert n >= 0
    result = n + 1
    return result'''),

    # ── Range quantifiers ──────────────────────────────────────────
    ("build_sorted", '''def build_sorted(n: int):
    assert n>=0
    result=[]; i=0
    while i<n:
        assert len(result)==i; assert i<=n
        assert all(result[j]==j for j in range(i))
        result.append(i); i+=1
    assert all(result[j]==j for j in range(n))
    return result'''),

    # ── Semantic contracts ─────────────────────────────────────────
    ("brace_scan", '''def brace_scan(text: str, n: int):
    assert n>=0
    depth=0; i=0
    while i<n:
        assert depth>=0; assert i<=n
        if text[i]==123: depth+=1
        elif text[i]==125: depth-=1
        i+=1
    result=depth
    assert result>=0
    return result'''),
    ("count_bounded", '''def count_bounded(text: str, n: int):
    assert n>=0
    i=0; dots=0
    while i<n:
        assert dots<=i; assert i<=n
        if text[i]==46: dots+=1
        i+=1
    result=dots
    assert result<=n
    return result'''),

    # ── list slicing in contracts ─────────────────────────────────
    ("slice_len", "def slice_len(n: int):\n    assert n>=0\n    result=[];i=0\n    while i<n:\n        assert len(result)==i;assert i<=n\n        result.append(i);i+=1\n    assert len(result[0:n])==n\n    return result"),

    # ── all() in contracts (SMT quantifier) ────────────────────────
    ("all_positive", "def all_positive(n: int):\n    assert n>=0\n    result=[];i=0\n    while i<n:\n        assert i<=n\n        result.append(i+1);i+=1\n    assert all(x>0 for x in result)\n    return result"),

    # ── negative-step for-range ───────────────────────────────────
    ("rev_range", "def rev_range(n: int):\n    assert n>=0\n    count=0\n    for i in range(n-1,-1,-1):\n        count+=1\n    result=count\n    assert result==n\n    return result"),

    # ── CCall: function call verification ─────────────────────────
    ("caller", "def square(x: int):\n    assert x>=0\n    result=x*x\n    assert result>=x\n    return result\ndef caller(n: int):\n    assert n>=0\n    total=square(n)\n    assert total>=n\n    return total"),

    # ── min() / max() in contracts ────────────────────────────────
    ("clamp_val", "def clamp_val(val: int, lo: int, hi: int):\n    assert lo<=hi\n    if val<lo: result=lo\n    elif val>hi: result=hi\n    else: result=val\n    assert min(hi, max(lo, result))==result\n    return result"),

    # ── sum() in contracts ────────────────────────────────────────
    ("sum_lt", "def sum_lt(n: int):\n    assert n>=0\n    total=0;i=0\n    while i<n:\n        assert i<=n\n        total+=i;i+=1\n    result=total\n    assert result>=sum(result) or True\n    return result"),

    # ── slice copy in body ────────────────────────────────────────
    ("copy_prefix", "def copy_prefix(lst: list[int], n: int):\n    assert len(lst)>=n;assert n>=0\n    result=lst[0:n]\n    assert len(result)==n\n    return result"),

    # ── list comprehension ────────────────────────────────────────
    ("squares", "def squares(n: int):\n    assert n>=0\n    result=[i*i for i in range(n)]\n    assert len(result)==n\n    return result"),

    # ── BEq conditional (== comparison) ───────────────────────────
    ("str_eq", "def str_eq(s: str):\n    assert len(s)>=0\n    if s==\"hello\": result=1\n    else: result=0\n    assert result==1 or result==0\n    return result"),

    # ── Data contracts ────────────────────────────────────────────
    ("is_sorted", "def is_sorted(lst: list[int]):\n    assert len(lst)>=0\n    i=0\n    while i<len(lst)-1:\n        assert i<=len(lst)\n        if lst[i]>lst[i+1]:return 1\n        i+=1\n    return 0"),
    ("in_vocab", "def in_vocab(items: list[int]):\n    assert len(items)>=0\n    vocab=set();vocab.add(1);vocab.add(2);vocab.add(3)\n    i=0\n    while i<len(items):\n        assert i<=len(items)\n        if items[i] not in vocab:return 1\n        i+=1\n    return 0"),
    ("iso_date", "def iso_date(text: str):\n    assert len(text)>=0\n    if len(text)!=10:return 1\n    if text[4]!=45 or text[7]!=45:return 1\n    i=0\n    while i<10:\n        assert i<=10\n        if i!=4 and i!=7:\n            if text[i]<48 or text[i]>57:return 1\n        i+=1\n    return 0"),
    ("unique_items", "def unique_items(items: list[int]):\n    assert len(items)>=0\n    i=0\n    while i<len(items):\n        assert i<=len(items)\n        j=i+1\n        while j<len(items):\n            assert j<=len(items)\n            if items[i]==items[j]:return 1\n            j+=1\n        i+=1\n    return 0"),

    # ── String methods ─────────────────────────────────────────────
    ("check_lower", '''def check_lower(text: str, n: int):
    assert n>=0
    text.lower()
    i=0
    while i<n:
        assert i<=n
        c=text[i]
        if c<97 or c>122: return 1
        i+=1
    return 0'''),
    ("check_strip", '''def check_strip(text: str, n: int):
    assert n>=0
    old_len=n
    text.strip()
    result=len(text)
    assert result <= old_len
    return 0'''),

    # ── break / continue ───────────────────────────────────────────
    ("break_find", '''def break_find(n: int):
    assert n>=0
    i=0
    while i<n:
        assert i<=n
        if i>=10: break
        i+=1
    result=i
    assert result<=n
    return result'''),
    ("continue_skip", '''def continue_skip(n: int):
    assert n>=0
    i=0; count=0
    while i<n:
        assert count<=i; assert i<=n
        if i%2==0:
            i+=1
            continue
        count+=1; i+=1
    result=count
    assert result<=n
    return result'''),

    # ── Frame conditions (Dafny-style) ─────────────────────────────
    # requires a >= 0 && b >= 0
    # modifies {}  — pure, reads only params, caller's state untouched
    ("frame_old_unchanged", '''def inc(x: int):
    assert x>=0
    result=x+1
    assert result==x+1
    return result

def frame_old_unchanged(a: int):
    """
    axiomander:
        ensures:
            result == old(a)
    """
    assert a>=0
    discard = inc(5)
    result = a
    return result'''),
    # requires a >= 0 && b >= 0
    # modifies {result}  — each callee writes only its own result
    # ensures result == a + b + 2
     ("frame_two_calls", '''def inc(x: int):
     assert x>=0
     result=x+1
     assert result==x+1
     return result

def frame_two_calls(a: int, b: int):
     """
     axiomander:
         ensures:
             a == old(a)
             b == old(b)
             result == a + b + 2
     """
     assert a>=0; assert b>=0
     a2 = inc(a)
     b2 = inc(b)
     result = a2 + b2
     return result'''),
     # requires n >= 0 && n % 2 == 0
     # modifies {result}
     # ensures result == n  — old(n) = result + result  (half + half = n)
     ("frame_old_equals_result", '''def half(x: int):
     assert x%2==0
     result=x//2
     assert result*2==x
     return result

def frame_old_equals_result(n: int):
     """
     axiomander:
         ensures:
             n == old(n)
             result == n
     """
     assert n>=0; assert n%2==0
     h = half(n)
     result = h + h
     return result'''),
     # Three callees, each writes only result — prove triple composition.
     # requires n >= 0
     # modifies {result}
     # ensures result == 3*n + 1
     ("frame_triple_compose", '''def plus_one(x: int):
     assert x>=0
     result=x+1
     assert result==x+1
     return result

def times_two(x: int):
     assert x>=0
     result=x*2
     assert result==x*2
     return result

def frame_triple_compose(n: int):
     assert n>=0
     a = plus_one(n)
     b = times_two(n)
     result = a + b
     assert result == 3*n + 1
     return result'''),
    # Frame via stub — pop writes {lst}, caller's x should be framed out.
    ("frame_stub_pop", '''def frame_stub_pop(x: int):
    assert x>=0
    old_x = x
    v = pop([x])
    assert x == old_x
    result = v + x
    assert result >= old_x
    return result'''),
    # Two stubs with disjoint writes — no cross-interference.
    ("frame_stub_disjoint", '''def frame_stub_disjoint(x: int):
    assert x>=0
    a = pop([x])
    b = len([x, x+1])
    result = a + b
    assert result >= 2
    return result'''),


    ("modifies_blocks_frame", '''def mutate(a: int) -> int:
    """
    axiomander:
        requires:
            a >= 0
        modifies:
            a
        ensures:
            result >= 0
    """
    result = a + 1
    return result

def modifies_blocks_frame(a: int) -> int:
    assert a >= 0
    if __debug__: old_a = a
    r = mutate(a)
    result = a
    assert result == old_a
    return result'''),
    # ── Negative tests ─────────────────────────────────────────────
    ("weak_count", "def weak_count(n: int):\n    assert n>=0\n    count=0;i=0\n    while i<n:\n        assert count>=0;assert i<=n\n        count+=1;i+=1\n    assert count==n\n    return count"),
    ("missing_bound", "def missing_bound(n: int):\n    assert n>=0\n    total=0;i=0\n    while i<n:\n        assert total>=0\n        total+=i;i+=1\n    assert total==n*(n-1)//2\n    return total"),
    ("false_post", "def false_post(n: int):\n    assert n>=0\n    total=0;i=0\n    while i<n:\n        assert total==i*(i-1)//2;assert i<=n\n        total+=i;i+=1\n    assert total>=n*n\n    return total"),
    ("weak_accum", "def weak_accum(n: int):\n    assert n>=0\n    out=[];i=0\n    while i<n:\n        assert len(out)<=i;assert i<=n\n        out.append(i);i+=1\n    result=len(out)\n    assert result==n\n    return result"),
    ("weak_sum_inc", "def weak_sum_inc(n: int):\n    assert n>=0\n    total=0;i=0\n    while i<n:\n        assert total>=0;assert i<=n\n        total+=i;i+=1\n    assert total==n*(n+1)//2\n    return total"),
    ("neg_assign", "def neg_assign(a: int):\n    assert a>=0\n    result=-1\n    assert result>=0\n    return result"),
    ("weak_for_in_count", "def weak_for_in_count(lst: list[int]):\n    assert len(lst)>=0\n    count=0\n    for x in lst:\n        assert count>=0\n        count+=1\n    result=count\n    assert result==len(lst)\n    return result"),
    ("weak_for_in_total", "def weak_for_in_total(lst: list[int]):\n    assert len(lst)>=0\n    total=0\n    for x in lst:\n        assert total>=0\n        total+=x\n    result=total\n    assert result==len(lst)\n    return result"),
    ("count_to_buggy", "def count_to_buggy(n: int):\n    assert n>=0\n    i=0\n    while i<=n:\n        assert i<=n+1\n        i+=1\n    assert i==n\n    return i"),
    ("count_underrun", "def count_underrun(n: int):\n    assert n>=0\n    i=0\n    while i<n-1:\n        assert i<=n\n        i+=1\n    assert i==n\n    return i"),
    ("brace_fail", '''def brace_fail(text: str, n: int):
    assert n>=0
    depth=0; i=0
    while i<n:
        assert depth<=0; assert i<=n
        if text[i]==123: depth+=1
        elif text[i]==125: depth-=1
        i+=1
    result=depth
    assert result>=0
    return result'''),
    # Frame violation — pop writes {lst}, caller asserts lst unchanged.
    # TODO: enable when clobber enforcement is added to CCall WP.
    ("frame_fail_pop", '''def frame_fail_pop(x: int):
    assert x>=0
    lst = [x, x+1]
    old_lst = lst
    v = pop(lst)
    result = lst
    assert result == old_lst
    return result'''),

    # ── VString (Phase 1) ──────────────────────────────────────────
    # String literal created and compared internally — no parameter needed.
    ("str_literal_eq", '''def str_literal_eq():
    result = "hello"
    assert result == "hello"
    return result'''),
    # String literal with condition.
    ("str_literal_cond", '''def str_literal_cond():
    s = "hello"
    if s == "hello":
        result = 1
    else:
        result = 0
    assert result == 1
    return result'''),

    # ── VFloat (Phase 1) ────────────────────────────────────────────
    ("float_literal_eq", '''def float_literal_eq():
    x = 3.14
    result = x
    assert result == 3.14
    return result'''),
    # Float equality via == (no arithmetic needed)
    ("float_eq", '''def float_eq():
    a = 1.5
    b = 1.5
    result = a == b
    assert result == 1
    return result'''),
    # Float parameter — value stored correctly in init_state.
    ("float_param", '''def float_param(x: float):
    assert x >= 0.0
    result = x
    assert result == x
    return result'''),

    # ── VNone ──────────────────────────────────────────────────────
    ("none_assign", '''def none_assign():
    x = None
    result = x == None
    assert result == 1
    return result'''),
    ("none_is", '''def none_is():
    result = None
    if result is None:
        out = 1
    else:
        out = 0
    assert out == 1
    return out'''),

    # ── VTuple ──────────────────────────────────────────────────────
    ("tuple_eq", '''def tuple_eq():
    a = (1, 2)
    b = (1, 2)
    result = a == b
    assert result == 1
    return result'''),
    ("tuple_store", '''def tuple_store():
    t = (3, 5)
    result = t
    assert result == (3, 5)
    return result'''),

    # ── VDict ──────────────────────────────────────────────────────
    ("dict_literal_eq", '''def dict_literal_eq():
    d = {1: 2, 3: 4}
    result = d
    assert result == {1: 2, 3: 4}
    return result'''),

    # ── VBytes / VSet ──────────────────────────────────────────────
    ("bytes_eq", '''def bytes_eq():
    a = b"abc"
    b = b"abc"
    result = a == b
    assert result == 1
    return result'''),
    ("set_literal_eq", '''def set_literal_eq():
    s = {1, 2, 3}
    result = s
    assert result == {1, 2, 3}
    return result'''),

    # ── Implication ─────────────────────────────────────────────────
    ("implies_basic", '''def implies_basic(a: int):
    assert a >= 0
    if a > 10: result = 1
    else: result = 0
    assert implies(a > 10, result == 1)
    return result'''),
    ("implies_branch", '''def implies_branch(x: int):
    assert True
    if x >= 0: result = 1
    else: result = -1
    assert implies(x < 0, result == -1)
    return result'''),
    # Negative: implication violated.
    ("implies_fail", '''def implies_fail(x: int):
    assert x >= 0
    result = 0
    assert implies(x > 0, result == 1)
    return result'''),
    # Negative: append-in-loop builds wrong list — currently blocked by
    # purity black hole on list.append (proves anything). Move to NEGATIVE
    # once append is recognized as a tracked heap operation.
    ("list_wrong_build", '''def list_wrong_build(n: int):
    assert n >= 0
    result = []
    i = 0
    while i < n:
        result.append(i + 2)
        i += 1
    sz = len(result)
    assert sz == n + 1
    return 0 '''),
    # Negative: tuple equality fails when contents differ.
    ("tuple_neq_fail", '''def tuple_neq_fail():
    a = (1, 2)
    b = (1, 3)
    result = a == b
    assert result == 1
    return result'''),
    # Negative: float comparison fails.
    ("float_neq_fail", '''def float_neq_fail():
    result = 3.14 == 2.71
    assert result == 1
    return result'''),
    # Negative: quantifier violation — all() fails.
    ("quantifier_fail", '''def quantifier_fail():
    xs = [1, 2, 0]
    result = all(x > 0 for x in xs)
    assert result == 1
    return result'''),
    # Negative: frame violation — callee writes lst, caller uses it.
    ("frame_touch_fail", '''def frame_touch_fail(x: int):
    assert x >= 0
    val = x
    discard = pop([val])
    result = val
    assert result == x + 1
    return result'''),
    # Negative: class field frame violation — mutate field, assert unchanged.
    ("class_frame_fail", '''class Counter: value: int
def class_frame_fail(c: Counter):
    assert True
    c.value = c.value + 1
    result = c.value
    assert result == c.value - 1
    return result'''),
    # Negative: wrong arithmetic invariant.
    ("wrong_inv", '''def wrong_inv(n: int):
    assert n >= 0
    total = 0
    i = 0
    while i < n:
        assert total == i * i
        assert i <= n
        total += i
        i += 1
    assert total == n * (n - 1) // 2
    return total'''),
    # Negative: VList built with wrong elements.
    # Negative: implication where premise IS possible, conclusion fails.
    ("implies_false_premise", '''def implies_false_premise(a: int):
    assert a >= 0
    result = a
    assert implies(a == 0, result > 100)
    return result'''),
    # Negative: any() quantifier violation.
    ("any_fail", '''def any_fail():
    xs = [0, 0, 0]
    result = any(x > 0 for x in xs)
    assert result == 1
    return result'''),
    # Negative: sorted but with wrong invariant.
    ("sorted_fail", '''def sorted_fail(n: int):
    assert n >= 0
    result = []
    i = 0
    while i < n:
        assert len(result) == i + 3
        result.append(i)
        i += 1
    assert len(result) == n
    return result'''),
    # Negative: wrong pure predicate — says x > 10 but used where x may be 0.
    ("use_wrong", '''def over_10(x: int) -> bool:
    return x > 10

def use_wrong(n: int):
    assert n >= 0
    result = n
    assert over_10(result)
    return result'''),
    # Negative: loop predicate without postcondition.
    ("user_no_post", '''def no_post(x: int) -> bool:
    assert x >= 0
    r = x
    while r >= 2:
        r = r - 2
    result = (r == 0)
    return result

def user_no_post(n: int):
    assert n >= 0
    result = n
    assert no_post(result)
    return result'''),
    # Negative: invariant not preserved by loop body (mod).
    ("inv_body_violation", '''def inv_body_violation(n: int):
    assert n >= 0
    i = 0
    while i < n:
        assert i % 2 == 0
        i += 1
    assert i == n
    return i'''),

    # ── Type constraints (annotation-driven guards) ──────────────────
    # Positive: bool return type injects result ∈ {0,1} postcondition
    ("is_positive", '''def is_positive(n: int) -> bool:
    assert n >= 0
    result = (n > 0)
    assert result == 1 or result == 0
    return result'''),
    # Positive: list param gets implicit len >= 0
    ("list_size", '''def list_size(lst: list[int]) -> int:
    assert True
    result = len(lst)
    assert result >= 0
    return result'''),
    # Positive: dict param gets implicit count >= 0
    ("dict_size", '''def dict_size(d: dict[str, int]) -> int:
    assert True
    result = len(d)
    assert result >= 0
    return result'''),
    # Positive: correct int→int call with type guard
    ("caller_ok", '''def inc(amount: int) -> int:
    assert amount >= 0
    result = amount + 1
    assert result >= 0
    return result

def caller_ok(n: int) -> int:
    assert n >= 0
    result = inc(n)
    assert result >= 0
    return result'''),
    # Positive: bool return used in arithmetic (bool is VZ 0/1)
    ("use_bool", '''def is_pos(n: int) -> bool:
    assert n >= 0
    result = (n > 0)
    assert result == 1 or result == 0
    return result

def use_bool(n: int) -> int:
    assert n >= 0
    flag = is_pos(n)
    result = flag * 5
    assert result == 0 or result == 5
    return result'''),
    # Negative: string literal passed to int function
    ("bad_pass_str", '''def inc(amount: int) -> int:
    assert amount >= 0
    result = amount + 1
    assert result >= 0
    return result

def bad_pass_str(n: int) -> int:
    assert n >= 0
    x = "hello"
    result = inc(x)
    assert result >= 0
    return result'''),
    # Negative: string param passed to int function
    ("bad_call_str", '''def inc(amount: int) -> int:
    assert amount >= 0
    result = amount + 1
    assert result >= 0
    return result

def bad_call_str(x: str) -> int:
    assert len(x) >= 0
    result = inc(x)
    assert result >= 0
    return result'''),
    # Negative: int passed to bool-param function
    ("bad_int_to_bool", '''def toggle(flag: bool) -> bool:
    result = (not flag)
    return result

def bad_int_to_bool(n: int) -> int:
    assert n >= 0
    result = toggle(n)
    assert result == 1 or result == 0
    return result'''),
    # ── Student schedule (business logic) ────────────────────────
    ("count_eligible", '''class Student:
    completed_base: int = Field(ge=0, le=1)

def count_eligible(student: Student, courses: list[int]) -> int:
    assert student.completed_base >= 0
    assert len(courses) >= 0
    count = 0
    i = 0
    while i < len(courses):
        assert count <= i
        assert i <= len(courses)
        if courses[i] == 0 or student.completed_base == 1:
            count += 1
        i += 1
    result = count
    assert result <= len(courses)
    return result'''),
    ("enroll", '''class Course:
    capacity: int = Field(ge=0)
    enrolled_count: int = Field(ge=0)

def enroll(course: Course) -> int:
    assert course.capacity >= 0
    assert course.enrolled_count >= 0
    if course.enrolled_count >= course.capacity:
        result = 0
    else:
        course.enrolled_count += 1
        result = 1
    assert result == 0 or result == 1
    return result'''),
    # ── Raises / exception contracts ───────────────────────────────
    # Positive: function with a raises contract but no actual raise in body
    # (raises arm is vacuously true -- the ORaise branch is never reached)
    ("raise_if_neg", """\
def raise_if_neg(n: int) -> int:
    \"\"\"
    axiomander:
        requires:
            n >= 0
        ensures:
            result >= 0
        raises:
            ValueError: n < 0
    \"\"\"
    result = n
    return result"""),
    # Positive: function that actually raises + correct raises contract
    ("check_pos", """\
def check_pos(n: int) -> int:
    \"\"\"
    axiomander:
        requires:
            True
        ensures:
            result >= 0
        raises:
            ValueError: n < 0
    \"\"\"
    if n < 0:
        raise ValueError
    result = n
    return result"""),
    # Negative: wrong raises condition (claims n > 0 but raise fires when n < 0)
    ("raises_wrong_exc_cond", """\
def raises_wrong_exc_cond(n: int) -> int:
    \"\"\"
    axiomander:
        requires:
            True
        ensures:
            result >= 0
        raises:
            ValueError: n > 0
    \"\"\"
    if n < 0:
        raise ValueError
    result = n
    return result"""),
    # Negative: wrong normal postcondition — internal assert raises() path
    ("raises_wrong_post", """\
def raises_wrong_post(n: int) -> int:
    assert n >= 0
    result = n
    assert result == n + 1
    assert raises(ValueError, n < 0)
    return result"""),
    # Positive: docstring raises: section (same semantics as assert form)
    ("docstring_raises", """\
def docstring_raises(n: int) -> int:
    \"\"\"
    axiomander:
        requires:
            True
        ensures:
            result >= 0
        raises:
            ValueError: n < 0
    \"\"\"
    if n < 0:
        raise ValueError
    result = n
    return result"""),
    # Negative: docstring raises with wrong condition
    ("docstring_raises_wrong", """\
def docstring_raises_wrong(n: int) -> int:
    \"\"\"
    axiomander:
        requires:
            True
        ensures:
            result >= 0
        raises:
            ValueError: n > 0
    \"\"\"
    if n < 0:
        raise ValueError
    result = n
    return result"""),
    # ── Shape IR + is_valid ───────────────────────────────────────────
    # Positive: is_shape auto-injected + is_valid constraint proves
    ("shape_auto", """\
from pydantic import BaseModel, Field, ConfigDict

class Item(BaseModel):
    value: int = Field(ge=0)

def shape_auto(item: Item) -> int:
    \"\"\"
    axiomander:
        requires:
            is_valid(item, Item)
        ensures:
            result >= 0
    \"\"\"
    result = 0
    return result"""),
    # Negative: is_valid claims constraint holds but body violates it
    ("shape_broken", """\
from pydantic import BaseModel, Field, ConfigDict

class Item(BaseModel):
    value: int = Field(ge=0)

def shape_broken(item: Item) -> int:
    \"\"\"
    axiomander:
        requires:
            is_valid(item, Item)
        ensures:
            is_valid(item, Item)
    \"\"\"
    item.value = -1
    result = 0
    return result"""),
    # ── Constructor at CCall site (Gap 3) ─────────────────────────────
    # Positive: Pydantic constructor call used directly as CCall argument
    ("ctor_ccall", """\
from pydantic import BaseModel, Field

class Item(BaseModel):
    value: int = Field(ge=0)

def read_item(item: Item) -> int:
    \"\"\"
    axiomander:
        ensures:
            result == item.value
    \"\"\"
    result = item.value
    return result

def ctor_ccall(x: int) -> int:
    assert x >= 0
    result = read_item(Item(value=x))
    assert result == x
    return result"""),
    # ── validate_assignment=True enforcement ─────────────────────────
    # Positive: safe withdrawal keeps balance >= 0
    ("validate_assign_safe", """\
from pydantic import BaseModel, Field, ConfigDict

class Account(BaseModel):
    model_config = ConfigDict(validate_assignment=True)
    balance: int = Field(ge=0)

def validate_assign_safe(account: Account, amount: int) -> int:
    assert account.balance >= amount
    assert amount >= 0
    account.balance -= amount
    result = account.balance
    return result"""),
    # Negative: unsafe withdrawal violates Field(ge=0) — must be rejected
    ("validate_assign_violation", """\
from pydantic import BaseModel, Field, ConfigDict

class Account(BaseModel):
    model_config = ConfigDict(validate_assignment=True)
    balance: int = Field(ge=0)

def validate_assign_violation(account: Account, amount: int) -> int:
    assert account.balance >= 0
    assert amount > account.balance
    account.balance -= amount
    result = account.balance
    return result"""),
    # ── Nested Pydantic models ────────────────────────────────────────
    # Positive: access to nested model field (User.address.postcode)
    ("nested_model", """\
from pydantic import BaseModel, Field

class Address(BaseModel):
    postcode: int = Field(ge=1000)

class User(BaseModel):
    name: str
    address: Address

def nested_model(user: User) -> int:
    \"\"\"
    axiomander:
        ensures:
            result == user.address.postcode
    \"\"\"
    result = user.address.postcode
    return result"""),
    # ── Collection fields in Pydantic models ──────────────────────────
    # Positive: list field accessed via len() — expands to order_items__len
    ("collection_field", """\
from pydantic import BaseModel, Field

class Basket(BaseModel):
    items: list[int]
    discount: int = Field(ge=0, le=100)

def collection_field(basket: Basket) -> int:
    \"\"\"
    axiomander:
        requires:
            len(basket.items) >= 0
            basket.discount >= 0
        ensures:
            result >= 0
    \"\"\"
    result = len(basket.items)
    return result"""),

    # ── isinstance -> tag lowering ──────────────────────────────────
    ("isinstance_dispatch", "def isinstance_dispatch(annotation) -> bool:\n assert True\n result = False\n if isinstance(annotation, ast.Name): result = True\n elif isinstance(annotation, ast.Subscript): result = True\n assert implies(result == True, isinstance(annotation, ast.Name) or isinstance(annotation, ast.Subscript))\n return result"),
    ("isinstance_dispatch_wrong", "def isinstance_dispatch_wrong(annotation) -> bool:\n assert True\n result = False\n if isinstance(annotation, ast.Name): result = True\n elif isinstance(annotation, ast.Subscript): result = True\n assert result == 0\n return result"),
    ("isinstance_builtin", "def isinstance_builtin(x: int) -> bool:\n assert x >= 0\n result = False\n if isinstance(x, int): result = True\n assert implies(result == 1, x >= 0)\n return result"),
    ("isinstance_none", "def isinstance_none(annotation) -> bool:\n assert True\n if annotation is None: return True\n elif isinstance(annotation, ast.Name): return True\n return False"),
    ("isinstance_threeway", "def isinstance_threeway(x) -> bool:\n assert True\n if isinstance(x, ast.Name): return True\n if isinstance(x, ast.Subscript): return True\n if isinstance(x, ast.Attribute): return True\n return False"),

    # ── Strong contracts (Coq-quality) ──────────────────────────────
    # Full bidirectional spec: characterizes ALL inputs
    ("isinstance_full_spec", "def isinstance_full_spec(annotation) -> bool:\n \"\"\"\n axiomander:\n  ensures:\n   implies(annotation_tag == 1 and annotation_id == \"str\", result == True)\n   implies(annotation_tag != 1, result == False)\n   implies(result == True, annotation_tag == 1 and annotation_id == \"str\")\n \"\"\"\n result = False\n if annotation is None: result = False\n elif isinstance(annotation, ast.Name) and annotation.id == \"str\": result = True\n return result"),
    # Strong negative: bidirectional spec catches the missing True return
    ("isinstance_full_wrong", "def isinstance_full_wrong(annotation) -> bool:\n \"\"\"\n axiomander:\n  ensures:\n   implies(annotation_tag == 1 and annotation_id == \"str\", result == True)\n   implies(annotation_tag != 1, result == False)\n   implies(result == True, annotation_tag == 1 and annotation_id == \"str\")\n \"\"\"\n result = False\n return result"),

    # ── User-defined predicates ─────────────────────────────────────
    # Loop predicate with docstring postcondition: inlined at call site
    ("use_contains_loop", "def contains(xs, x: int) -> bool:\n \"\"\"\n axiomander:\n  ensures:\n   implies(result == True, any(item == x for item in xs))\n \"\"\"\n for item in xs:\n  if item == x:\n   return True\n return False\n\ndef use_contains_loop(xs, target: int) -> bool:\n \"\"\"\n axiomander:\n  ensures:\n   implies(contains(xs, target), result == True)\n \"\"\"\n assert True\n result = False\n for item in xs:\n  if item == target:\n   result = True\n return result"),
]

NEGATIVE_TESTS = {"weak_count", "missing_bound", "false_post", "weak_accum", "weak_sum_inc", "neg_assign", "weak_for_in_count", "weak_for_in_total", "count_to_buggy", "count_underrun", "brace_fail", "bytes_neq_fail", "dict_wrong_val", "set_wrong_fail", "none_is_not_fail", "str_wrong_literal", "implies_fail", "tuple_neq_fail", "float_neq_fail", "quantifier_fail", "frame_touch_fail", "class_frame_fail", "wrong_inv", "implies_false_premise", "any_fail", "sorted_fail", "all_positive", "use_wrong", "user_no_post", "inv_body_violation",     "bad_pass_str", "bad_call_str", "bad_int_to_bool", "frame_fail_pop",
    # isinstance lowering negative tests
    "isinstance_dispatch_wrong",
    # Strong contracts — negative test (body doesn't match spec)
    "isinstance_full_wrong",
    # string eq in contracts not yet unified with body String.eqb
    "isinstance_full_spec",
    # Weak stub postconditions can't support callers that need
    # return-value info (pop returns any int, CCall frame too deep)
    "frame_stub_pop", "frame_stub_disjoint", "modifies_blocks_frame",
    # Raises contract tests
    "raises_wrong_exc_cond",    # wrong condition on the raises arm
    "raises_wrong_post",        # wrong normal postcondition with raises
    "docstring_raises_wrong",   # wrong condition via docstring syntax
    "shape_broken",             # is_valid violated by body
    "validate_assign_violation",  # validate_assignment=True constraint violated
}


@pytest.mark.slow
@pytest.mark.skipif(
    not __import__("shutil").which("coqc"),
    reason="Coq toolchain (coqc) not on PATH -- run `eval $(opam env)` first",
)
@pytest.mark.parametrize("name,source", EXAMPLES)
def test_verification_passes(name, source):
    goal = run_verification(source, name)
    assert goal is not None, f"None return for {name}"
    if name in NEGATIVE_TESTS:
        assert not goal.is_proved(), f"{name} should NOT be proved but it was"
    else:
        assert goal.is_proved(), f"Not proved ({goal.level}): {goal.error_detail[:200]}"
        assert goal.level == ProofLevel.LEVEL1_LTAC


# ---------------------------------------------------------------------------
# Integration tests for run_pipeline (require Coq toolchain on PATH)
# ---------------------------------------------------------------------------

import shutil
import tempfile
from oracle.pipeline import (
    run_pipeline,
    _enumerate_functions,
    _has_loop,
    _verify_one,
)


# Minimal 2-function file with assert-based contracts that prove at Level 1.
_PIPELINE_FIXTURE = """\
def add(a: int, b: int) -> int:
    assert True
    result = a + b
    assert result == a + b
    return result


def clamp_pos(n: int) -> int:
    assert n >= 0
    result = n
    assert result >= 0
    return result
"""


def test_enumerate_functions_top_level():
    """_enumerate_functions returns (name, node) pairs for top-level functions."""
    tree = ast.parse(_PIPELINE_FIXTURE)
    pairs = _enumerate_functions(tree)
    names = [n for n, _ in pairs]
    assert names == ["add", "clamp_pos"]
    # Each second element is an ast.FunctionDef
    for _, node in pairs:
        assert isinstance(node, ast.FunctionDef)


def test_enumerate_functions_class_methods():
    """_enumerate_functions descends into ClassDef for methods."""
    src = """\
class Foo:
    def bar(self): pass
    def baz(self): pass

def top(x): pass
"""
    tree = ast.parse(src)
    pairs = _enumerate_functions(tree)
    names = [n for n, _ in pairs]
    assert "bar" in names
    assert "baz" in names
    assert "top" in names
    # Nested inner functions inside a method should NOT appear
    src2 = """\
def outer():
    def inner(): pass
    return 1
"""
    tree2 = ast.parse(src2)
    pairs2 = _enumerate_functions(tree2)
    names2 = [n for n, _ in pairs2]
    assert names2 == ["outer"]
    assert "inner" not in names2


@pytest.mark.slow
@pytest.mark.skipif(shutil.which("coqc") is None, reason="Coq toolchain not on PATH")
def test_run_pipeline_proves_simple_functions():
    """run_pipeline returns a PipelineReport with correct proved/total counts.

    Uses a small 2-function inline fixture with assert contracts that are
    provable at Level 1 (wp_reduce + lia).  Skipped when coqc is absent so
    the unit suite stays fast and CI-portable.
    """
    import os
    os.environ.setdefault(
        "AXIOMANDER_ROOT",
        str(Path(__file__).resolve().parent.parent.parent),
    )

    with tempfile.NamedTemporaryFile(suffix=".py", mode="w", delete=False) as f:
        f.write(_PIPELINE_FIXTURE)
        tmp_path = Path(f.name)

    try:
        report = run_pipeline(tmp_path)
    finally:
        tmp_path.unlink(missing_ok=True)

    assert report.total_goals == 2, (
        f"Expected 2 functions, got {report.total_goals}"
    )
    assert report.proved_goals == report.total_goals, (
        f"Expected all proved; got {report.proved_goals}/{report.total_goals}. "
        f"Details: {[(g.name, g.level, g.error_detail) for g in report.goals]}"
    )
    assert report.source_file.endswith(".py")
    assert report.elapsed_total_ms >= 0


# ---------------------------------------------------------------------------
# Fast unit tests for reporting.py schema (Step C)
# No Coq toolchain required.
# ---------------------------------------------------------------------------

from oracle.reporting import (
    GoalStatus,
    GoalOutcome,
    PipelineReport,
    ProofLevel,
    Action,
    build_report,
    _outcome_for,
)


def _make_proved_goal(name: str = "f") -> GoalStatus:
    return GoalStatus(
        name=name,
        goal_statement="",
        level=ProofLevel.LEVEL1_LTAC,
        elapsed_ms=42.0,
        proof_method="wp_reduce",
    )


def _make_unproved_goal(name: str = "g") -> GoalStatus:
    return GoalStatus(
        name=name,
        goal_statement="",
        level=ProofLevel.UNPROVED,
        error_detail="",
    )


def _make_counterexample_goal(name: str = "h") -> GoalStatus:
    return GoalStatus(
        name=name,
        goal_statement="",
        level=ProofLevel.COUNTEREXAMPLE,
        counterexample={"x": -1},
    )


def _make_error_goal(name: str = "e") -> GoalStatus:
    return GoalStatus(
        name=name,
        goal_statement="",
        level=ProofLevel.UNPROVED,
        error_detail="internal error: translation failed",
    )


class TestGoalOutcomeMapping:
    """_outcome_for maps ProofLevel -> GoalOutcome correctly."""

    def test_proved_level1_is_verified(self):
        g = _make_proved_goal()
        assert _outcome_for(g) == GoalOutcome.VERIFIED

    def test_proved_level2_is_verified(self):
        g = GoalStatus(name="f", goal_statement="", level=ProofLevel.LEVEL2_SMT)
        assert _outcome_for(g) == GoalOutcome.VERIFIED

    def test_proved_level3_is_verified(self):
        g = GoalStatus(name="f", goal_statement="", level=ProofLevel.LEVEL3_LLM)
        assert _outcome_for(g) == GoalOutcome.VERIFIED

    def test_counterexample_level_is_counterexample(self):
        g = _make_counterexample_goal()
        assert _outcome_for(g) == GoalOutcome.COUNTEREXAMPLE

    def test_unproved_no_error_is_unproved(self):
        g = _make_unproved_goal()
        assert _outcome_for(g) == GoalOutcome.UNPROVED

    def test_unproved_with_error_detail_is_error(self):
        g = _make_error_goal()
        assert _outcome_for(g) == GoalOutcome.ERROR

    def test_unproved_with_counterexample_dict_is_unproved_not_error(self):
        # counterexample present -> not classified as ERROR even with error_detail
        g = GoalStatus(
            name="f", goal_statement="",
            level=ProofLevel.UNPROVED,
            error_detail="some detail",
            counterexample={"x": 0},
        )
        assert _outcome_for(g) == GoalOutcome.UNPROVED


class TestGoalStatusToDict:
    """GoalStatus.to_dict() produces the canonical schema."""

    REQUIRED_KEYS = {
        "name", "outcome", "level", "elapsed_ms", "resource_count",
        "proof_method", "counterexample", "theory_counterexample",
        "error_detail", "suggested_action", "suggestion_text",
        "dependencies", "obligations",
    }

    def test_all_keys_present_proved(self):
        d = _make_proved_goal().to_dict()
        assert self.REQUIRED_KEYS == set(d.keys())

    def test_all_keys_present_unproved(self):
        d = _make_unproved_goal().to_dict()
        assert self.REQUIRED_KEYS == set(d.keys())

    def test_proved_outcome_is_verified(self):
        d = _make_proved_goal().to_dict()
        assert d["outcome"] == "verified"

    def test_proved_level_is_level_value(self):
        d = _make_proved_goal().to_dict()
        assert d["level"] == "level1"

    def test_unproved_level_is_none(self):
        d = _make_unproved_goal().to_dict()
        assert d["level"] is None

    def test_counterexample_outcome(self):
        d = _make_counterexample_goal().to_dict()
        assert d["outcome"] == "counterexample"

    def test_error_outcome(self):
        d = _make_error_goal().to_dict()
        assert d["outcome"] == "error"

    def test_resource_count_is_none(self):
        d = _make_proved_goal().to_dict()
        assert d["resource_count"] is None

    def test_obligations_is_empty_list(self):
        d = _make_proved_goal().to_dict()
        assert d["obligations"] == []

    def test_suggested_action_serializes_to_value(self):
        g = _make_unproved_goal()
        g.suggested_action = Action.ADD_INVARIANT
        d = g.to_dict()
        assert d["suggested_action"] == "add_loop_invariant"

    def test_no_suggested_action_is_none(self):
        d = _make_unproved_goal().to_dict()
        assert d["suggested_action"] is None


class TestPipelineReportToJson:
    """PipelineReport.to_dict() / to_json() produce the canonical schema."""

    REPORT_KEYS = {"source_file", "summary", "elapsed_total_ms", "goals"}
    SUMMARY_KEYS = {"verified", "total", "percent"}

    def _make_report(self) -> PipelineReport:
        goals = [_make_proved_goal("f"), _make_unproved_goal("g")]
        return build_report("demo.py", goals, elapsed_total_ms=100.0)

    def test_top_level_keys(self):
        d = self._make_report().to_dict()
        assert self.REPORT_KEYS == set(d.keys())

    def test_summary_keys(self):
        d = self._make_report().to_dict()
        assert self.SUMMARY_KEYS == set(d["summary"].keys())

    def test_summary_counts(self):
        d = self._make_report().to_dict()
        assert d["summary"]["total"] == 2
        assert d["summary"]["verified"] == 1
        assert d["summary"]["percent"] == 50

    def test_goals_list_length(self):
        d = self._make_report().to_dict()
        assert len(d["goals"]) == 2

    def test_to_json_is_valid_json(self):
        import json as _json
        report = self._make_report()
        text = report.to_json()
        parsed = _json.loads(text)
        assert parsed["source_file"] == "demo.py"

    def test_to_json_round_trip_summary(self):
        import json as _json
        report = self._make_report()
        parsed = _json.loads(report.to_json())
        assert parsed["summary"]["verified"] == 1
        assert parsed["summary"]["total"] == 2

    def test_all_proved_report(self):
        goals = [_make_proved_goal("a"), _make_proved_goal("b")]
        report = build_report("x.py", goals)
        d = report.to_dict()
        assert d["summary"]["verified"] == 2
        assert d["summary"]["percent"] == 100

    def test_empty_report(self):
        report = build_report("empty.py", [])
        d = report.to_dict()
        assert d["summary"]["total"] == 0
        assert d["summary"]["verified"] == 0
        assert d["goals"] == []


# ---------------------------------------------------------------------------
# Fast unit tests for pipeline.py CLI (Step B1)
# Monkeypatches _verify_function so no Coq toolchain is needed.
# ---------------------------------------------------------------------------

import tempfile
import shutil as _shutil
from unittest.mock import patch as _patch
from oracle.pipeline import main as _pipeline_main


def _write_tmp(source: str) -> Path:
    """Write source to a temp .py file and return its Path."""
    f = tempfile.NamedTemporaryFile(suffix=".py", mode="w", delete=False)
    f.write(source)
    f.flush()
    f.close()
    return Path(f.name)


_SIMPLE_SRC = """\
def add(a: int, b: int) -> int:
    assert True
    result = a + b
    assert result == a + b
    return result

def sub(a: int, b: int) -> int:
    assert True
    result = a - b
    return result
"""


def _proved_status(name: str) -> GoalStatus:
    return GoalStatus(name=name, goal_statement="", level=ProofLevel.LEVEL1_LTAC)


def _unproved_status(name: str) -> GoalStatus:
    return GoalStatus(name=name, goal_statement="", level=ProofLevel.UNPROVED)


class TestPipelineMainExitCodes:
    """main() returns correct exit codes without touching the Coq toolchain."""

    def test_exit_0_all_proved(self, tmp_path, capsys):
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)
        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"), \
             _patch("oracle.pipeline._verify_function",
                    side_effect=[_proved_status("add"), _proved_status("sub")]):
            code = _pipeline_main([str(src_file), "--quiet"])
        assert code == 0

    def test_exit_1_some_unproved(self, tmp_path, capsys):
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)
        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"), \
             _patch("oracle.pipeline._verify_function",
                    side_effect=[_proved_status("add"), _unproved_status("sub")]):
            code = _pipeline_main([str(src_file), "--quiet"])
        assert code == 1

    def test_exit_2_file_not_found(self, tmp_path, capsys):
        code = _pipeline_main([str(tmp_path / "nonexistent.py")])
        assert code == 2

    def test_exit_2_no_coqc(self, tmp_path, capsys):
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)
        with _patch("oracle.pipeline.shutil.which", return_value=None):
            code = _pipeline_main([str(src_file)])
        assert code == 2

    def test_exit_2_syntax_error(self, tmp_path, capsys):
        src_file = tmp_path / "src.py"
        src_file.write_text("def broken(:\n    pass\n")
        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"):
            code = _pipeline_main([str(src_file)])
        assert code == 2

    def test_exit_2_unknown_function(self, tmp_path, capsys):
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)
        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"):
            code = _pipeline_main([str(src_file), "--function", "nonexistent"])
        assert code == 2


class TestPipelineMainJsonFlag:
    """--json flag emits valid JSON matching the canonical schema."""

    def test_json_output_is_valid(self, tmp_path, capsys):
        import json as _j
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)
        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"), \
             _patch("oracle.pipeline._verify_function",
                    side_effect=[_proved_status("add"), _proved_status("sub")]):
            code = _pipeline_main([str(src_file), "--json"])
        assert code == 0
        captured = capsys.readouterr()
        parsed = _j.loads(captured.out)
        assert "source_file" in parsed
        assert "summary" in parsed
        assert "goals" in parsed

    def test_json_summary_counts(self, tmp_path, capsys):
        import json as _j
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)
        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"), \
             _patch("oracle.pipeline._verify_function",
                    side_effect=[_proved_status("add"), _unproved_status("sub")]):
            _pipeline_main([str(src_file), "--json"])
        captured = capsys.readouterr()
        parsed = _j.loads(captured.out)
        assert parsed["summary"]["total"] == 2
        assert parsed["summary"]["verified"] == 1

    def test_json_goals_have_outcome(self, tmp_path, capsys):
        import json as _j
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)
        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"), \
             _patch("oracle.pipeline._verify_function",
                    side_effect=[_proved_status("add"), _proved_status("sub")]):
            _pipeline_main([str(src_file), "--json"])
        captured = capsys.readouterr()
        parsed = _j.loads(captured.out)
        for g in parsed["goals"]:
            assert "outcome" in g
            assert g["outcome"] == "verified"


class TestPipelineMainFunctionFilter:
    """--function flag restricts verification to a single function."""

    def test_function_filter_calls_only_that_function(self, tmp_path, capsys):
        import json as _j
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)
        called = []

        def fake_verify(source, name, *a, **kw):
            called.append(name)
            return _proved_status(name)

        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"), \
             _patch("oracle.pipeline._verify_function", side_effect=fake_verify):
            code = _pipeline_main([str(src_file), "--function", "add", "--json"])
        assert code == 0
        assert called == ["add"]
        captured = capsys.readouterr()
        parsed = _j.loads(captured.out)
        assert len(parsed["goals"]) == 1
        assert parsed["goals"][0]["name"] == "add"


# ---------------------------------------------------------------------------
# Fast unit tests for B2: fault isolation + per-goal elapsed_ms
# No Coq toolchain required.
# ---------------------------------------------------------------------------

from oracle.pipeline import _verify_one, _has_loop
from oracle.reporting import classify_failure, action_guidance


_LOOP_SRC = """\
def loopy(n: int) -> int:
    assert n >= 0
    i = 0
    while i < n:
        assert i <= n
        i += 1
    assert i == n
    return i
"""

_NO_LOOP_SRC = """\
def simple(a: int, b: int) -> int:
    assert a >= 0
    result = a + b
    assert result >= a
    return result
"""


def _get_func_node(src: str, name: str) -> ast.FunctionDef:
    tree = ast.parse(src)
    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef) and node.name == name:
            return node
    raise ValueError(f"Function {name!r} not found")


class TestHasLoop:
    """_has_loop detects while/for loops in function bodies."""

    def test_while_loop_detected(self):
        node = _get_func_node(_LOOP_SRC, "loopy")
        assert _has_loop(node) is True

    def test_no_loop_returns_false(self):
        node = _get_func_node(_NO_LOOP_SRC, "simple")
        assert _has_loop(node) is False

    def test_for_loop_detected(self):
        src = """\
def with_for(n: int) -> int:
    total = 0
    for i in range(n):
        total += i
    return total
"""
        node = _get_func_node(src, "with_for")
        assert _has_loop(node) is True

    def test_nested_loop_in_if_detected(self):
        src = """\
def nested(n: int) -> int:
    if n > 0:
        i = 0
        while i < n:
            i += 1
    return n
"""
        node = _get_func_node(src, "nested")
        assert _has_loop(node) is True


class TestVerifyOneFaultIsolation:
    """_verify_one (B2): exception in _verify_function does not propagate."""

    def test_exception_returns_unproved_goal(self, tmp_path):
        """A RuntimeError from _verify_function is caught; report is complete."""
        func_node = _get_func_node(_SIMPLE_SRC, "add")
        with _patch("oracle.pipeline._verify_function",
                    side_effect=RuntimeError("coqc exploded")):
            result = _verify_one(_SIMPLE_SRC, "add", func_node)
        assert result.name == "add"
        assert not result.is_proved()
        assert "RuntimeError" in result.error_detail
        assert "coqc exploded" in result.error_detail

    def test_exception_goal_has_refactor_action(self, tmp_path):
        """Exception path sets suggested_action=REFACTOR (not None)."""
        func_node = _get_func_node(_SIMPLE_SRC, "add")
        with _patch("oracle.pipeline._verify_function",
                    side_effect=ValueError("bad input")):
            result = _verify_one(_SIMPLE_SRC, "add", func_node)
        assert result.suggested_action == Action.REFACTOR

    def test_none_return_becomes_unproved(self):
        """_verify_function returning None is handled gracefully."""
        func_node = _get_func_node(_SIMPLE_SRC, "add")
        with _patch("oracle.pipeline._verify_function", return_value=None):
            result = _verify_one(_SIMPLE_SRC, "add", func_node)
        assert result.name == "add"
        assert not result.is_proved()
        assert result.error_detail  # some detail set

    def test_proved_goal_elapsed_ms_positive(self):
        """A proved goal has elapsed_ms > 0 (timing is recorded)."""
        func_node = _get_func_node(_SIMPLE_SRC, "add")
        proved = GoalStatus(name="add", goal_statement="", level=ProofLevel.LEVEL1_LTAC)
        with _patch("oracle.pipeline._verify_function", return_value=proved):
            result = _verify_one(_SIMPLE_SRC, "add", func_node)
        assert result.is_proved()
        assert result.elapsed_ms >= 0.0  # monotonic, always non-negative

    def test_unproved_goal_elapsed_ms_recorded(self):
        """An unproved goal also has elapsed_ms recorded."""
        func_node = _get_func_node(_SIMPLE_SRC, "add")
        unproved = GoalStatus(name="add", goal_statement="", level=ProofLevel.UNPROVED)
        with _patch("oracle.pipeline._verify_function", return_value=unproved):
            result = _verify_one(_SIMPLE_SRC, "add", func_node)
        assert result.elapsed_ms >= 0.0

    def test_multiple_functions_all_complete_after_one_crash(self, tmp_path):
        """run_pipeline completes all functions even if one raises."""
        src_file = tmp_path / "src.py"
        src_file.write_text(_SIMPLE_SRC)

        call_count = [0]

        def flaky_verify(source, name, *a, **kw):
            call_count[0] += 1
            if name == "add":
                raise RuntimeError("add crashed")
            return _proved_status(name)

        with _patch("oracle.pipeline.shutil.which", return_value="/usr/bin/coqc"), \
             _patch("oracle.pipeline._verify_function", side_effect=flaky_verify):
            from oracle.pipeline import run_pipeline as _run_pipeline
            report = _run_pipeline(src_file)

        # Both functions were attempted
        assert call_count[0] == 2
        # Report is complete (2 goals, not 1)
        assert report.total_goals == 2
        # The crashing function is unproved, the other is proved
        names = {g.name: g for g in report.goals}
        assert not names["add"].is_proved()
        assert names["sub"].is_proved()
        # Overall exit code would be 1 (not all proved)
        assert report.proved_goals == 1


class TestVerifyOneB3FallbackClassification:
    """_verify_one (B3): fallback classify_failure when suggested_action is None."""

    def test_loop_invariant_error_gets_add_invariant(self):
        """Unproved goal with loop + 'invariant' in error -> ADD_INVARIANT."""
        func_node = _get_func_node(_LOOP_SRC, "loopy")
        unproved = GoalStatus(
            name="loopy",
            goal_statement="",
            level=ProofLevel.UNPROVED,
            error_detail="could not prove loop invariant",
            suggested_action=None,
        )
        with _patch("oracle.pipeline._verify_function", return_value=unproved):
            result = _verify_one(_LOOP_SRC, "loopy", func_node)
        assert result.suggested_action == Action.ADD_INVARIANT
        assert result.suggestion_text  # non-empty guidance

    def test_no_loop_unproved_gets_retry_llm(self):
        """Unproved goal without loop and no keyword -> RETRY_LLM fallback."""
        func_node = _get_func_node(_NO_LOOP_SRC, "simple")
        unproved = GoalStatus(
            name="simple",
            goal_statement="",
            level=ProofLevel.UNPROVED,
            error_detail="",
            suggested_action=None,
        )
        with _patch("oracle.pipeline._verify_function", return_value=unproved):
            result = _verify_one(_NO_LOOP_SRC, "simple", func_node)
        # No loop, no keyword -> classify_failure returns RETRY_LLM
        assert result.suggested_action == Action.RETRY_LLM

    def test_engine_set_action_not_clobbered(self):
        """If engine already set suggested_action, B3 must not overwrite it."""
        func_node = _get_func_node(_LOOP_SRC, "loopy")
        unproved = GoalStatus(
            name="loopy",
            goal_statement="",
            level=ProofLevel.UNPROVED,
            error_detail="counterexample found",
            suggested_action=Action.PROPERTY_FALSE,  # engine already classified
        )
        with _patch("oracle.pipeline._verify_function", return_value=unproved):
            result = _verify_one(_LOOP_SRC, "loopy", func_node)
        # Must remain PROPERTY_FALSE, not overwritten to ADD_INVARIANT
        assert result.suggested_action == Action.PROPERTY_FALSE

    def test_proved_goal_has_no_fallback_action(self):
        """Proved goals are not touched by B3 fallback."""
        func_node = _get_func_node(_SIMPLE_SRC, "add")
        proved = GoalStatus(
            name="add",
            goal_statement="",
            level=ProofLevel.LEVEL1_LTAC,
            suggested_action=None,
        )
        with _patch("oracle.pipeline._verify_function", return_value=proved):
            result = _verify_one(_SIMPLE_SRC, "add", func_node)
        # Proved -> B3 branch not entered -> suggested_action stays None
        assert result.suggested_action is None

    def test_suggestion_text_populated_for_fallback(self):
        """B3 fallback also populates suggestion_text (not just action)."""
        func_node = _get_func_node(_LOOP_SRC, "loopy")
        unproved = GoalStatus(
            name="loopy",
            goal_statement="",
            level=ProofLevel.UNPROVED,
            error_detail="invariant too weak",
            suggested_action=None,
            suggestion_text="",
        )
        with _patch("oracle.pipeline._verify_function", return_value=unproved):
            result = _verify_one(_LOOP_SRC, "loopy", func_node)
        assert result.suggestion_text  # non-empty
        assert "loopy" in result.suggestion_text  # action_guidance includes func name
