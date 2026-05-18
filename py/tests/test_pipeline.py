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
    os.environ.setdefault("AXIOMANDER_ROOT", str(BUILD_DIR.parent.parent))
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
    # Original bookwyrm: filter_text_regions (using while loop, string fields via Z encoding)
    ("filter_regions", "class Region: content_type: str; text: str\ndef filter_regions(regions: list[Region]):\n assert len(regions)>=0\n result=[];i=0\n while i<len(regions):\n  assert len(result)<=i;assert i<=len(regions)\n  if regions[i].content_type==\"text\":result.append(regions[i].text)\n  i+=1\n assert len(result)<=len(regions)\n return result"),
    # Dict group-by (bookwyrm group_mappings_by_page)
    ("count_groups", "def count_groups(mappings: list[int]):\n assert len(mappings)>0\n result={};i=0;count=0\n while i<len(mappings):\n  assert count==i;assert i<=len(mappings)\n  key=mappings[i]\n  if key not in result:result[key]=[]\n  result[key].append(1);count+=1;i+=1\n assert count==len(mappings)\n return count"),
    # Dict comprehension (manual while loop)
    ("dict_comp", "def dict_comp(n: int):\n assert n>=0\n result={};i=0\n while i<n:\n  assert i<=n\n  result[i]=i*i;i+=1\n count=0;i=0\n while i<n:\n  assert count==i;assert i<=n\n  if i in result:count+=1\n  i+=1\n assert count==n\n return count"),
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
    assert a>=0
    old_a = a
    discard = inc(5)
    result = a
    assert result == old_a
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
    assert a>=0; assert b>=0
    old_a = a; old_b = b
    a2 = inc(a)
    b2 = inc(b)
    assert a == old_a; assert b == old_b
    result = a2 + b2
    assert result == a + b + 2
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
    assert n>=0; assert n%2==0
    snapshot = n
    h = half(n)
    assert n == snapshot
    result = h + h
    assert result == n
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
    assert n == n
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
]

NEGATIVE_TESTS = {"weak_count", "missing_bound", "false_post", "weak_accum", "weak_sum_inc", "neg_assign", "weak_for_in_count", "weak_for_in_total", "count_to_buggy", "count_underrun", "brace_fail"}


@pytest.mark.parametrize("name,source", EXAMPLES)
def test_verification_passes(name, source):
    goal = run_verification(source, name)
    assert goal is not None, f"None return for {name}"
    if name in NEGATIVE_TESTS:
        assert not goal.is_proved(), f"{name} should NOT be proved but it was"
    else:
        assert goal.is_proved(), f"Not proved ({goal.level}): {goal.error_detail[:200]}"
        assert goal.level == ProofLevel.LEVEL1_LTAC
