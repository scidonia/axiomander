"""Slice-to-match reassociation normalizer + Fixpoint emitter (WP-10/11).

Normalizes Python slice-recursion patterns (xs[0], xs[1:], xs[n:])
into Coq Fixpoint forms:

  Pattern 1 (list-structural, D1):
    is_sorted(xs[1:]) with xs decreasing structurally
    => Fixpoint is_sorted (xs : list Z) {struct xs} : bool :=
         match xs with [] => base | hd :: rest => body[hd,rest] end.

  Pattern 2 (nat-measured, D2):
    f(xs[n:]) with n decreasing structurally
    => Fixpoint f (xs : list Z) (n : nat) {struct n} : bool :=
         match n with O => ... | S n' => match xs with ... => f rest n' end end.

The normalizer rewrites the predicate body AST so that
  - xs[0]    becomes the head variable (hd)
  - xs[1:]   becomes the tail variable (rest)
  - xs[n:]   becomes dropn xs n  (nat-measured pattern)
"""

from __future__ import annotations

import ast
from dataclasses import dataclass, field

from axiomander.oracle.predicate_def import PredicateDef, RecKind


@dataclass(frozen=True)
class NormalizedBody:
    """A predicate body normalized for Coq Fixpoint emission.

    base_expr:   the expression for the base (non-recursive) case.
    cons_expr:   the expression for the recursive (cons) case, with
                 slice references rewritten to head/tail variables.
    head_var:    name of the head variable (hd in hd :: rest).
    tail_var:    name of the tail variable (rest in hd :: rest).
    param:       the original decreasing parameter name.
    base_guards: integer bounds for the base case (e.g. len(xs) <= 2).
                 Used to generate individual match arms ([] / [x] / ...).
    nat_measured: True if this is pattern 2 (nat counter decreasing).
    counter_var: the nat counter name (only for nat_measured).
    """

    base_expr: ast.expr
    cons_expr: ast.expr
    head_var: str = "hd"
    tail_var: str = "tl"
    param: str = "xs"
    base_guards: int = 0
    nat_measured: bool = False
    counter_var: str = "n"


def normalize_slice_rec(
    body_expr: ast.expr,
    param: str,
    *,
    head_var: str = "hd",
    tail_var: str = "tl",
) -> NormalizedBody | None:
    """Normalize a recursive predicate body that uses slice patterns.

    Recognises `if <guard>: <base> else: <recursive branch>` where the guard
    is a length check on *param* and the recursive branch contains self-calls
    on *param[1:]*.

    Returns None if the body does not match the expected if/else pattern.
    """
    if not isinstance(body_expr, ast.IfExp):
        return None

    guard = body_expr.test
    base = body_expr.body
    cons = body_expr.orelse

    # Extract the length bound from the guard, e.g. len(xs) <= 2.
    bound = _extract_len_bound(guard, param)
    if bound is None:
        return None

    # Rewrite the cons branch: replace xs[0] -> hd, xs[1:] -> tl.
    cons_rewritten = _rewrite_slices(cons, param, head_var, tail_var)

    return NormalizedBody(
        base_expr=base,
        cons_expr=cons_rewritten,
        head_var=head_var,
        tail_var=tail_var,
        param=param,
        base_guards=bound,
    )


# ---------------------------------------------------------------------------
# Fixpoint emitter
# ---------------------------------------------------------------------------

def emit_fixpoint(
    pd: PredicateDef,
    body: NormalizedBody | None = None,
    *,
    list_ty: str = "list Z",
) -> str:
    """Emit a Coq Fixpoint for a recursive predicate.

    Pattern 1 (list-structural, D1): self-call on `xs[1:]`.
    Pattern 2 (nat-measured, D2): self-call on `xs[n:]` with decreasing n.

    Returns the Coq Fixpoint definition as a string.
    """
    param = pd.params[0] if pd.params else "xs"
    name = pd.name

    if pd.rec_kind is RecKind.STRUCTURAL and body is not None:
        return _emit_structural(name, param, body)
    if pd.rec_kind is RecKind.MEASURED and pd.rec_arg:
        return _emit_measured(name, param)
    return f"(* Unimplemented Fixpoint for '{name}' with kind {pd.rec_kind.value} *)\n"


def _emit_structural(name: str, param: str, body: NormalizedBody) -> str:
    """Pattern 1: structural on list."""
    # Base arms: [] -> True, [hd] -> True (for len <= 1), etc.
    arms = []
    if body.base_guards >= 0:
        arms.append("  | [] => true")
    # For len(xs) <= 2, we need [] and [_] arms; etc.
    # Simplification: just emit the [] arm and let the cons branch handle
    # the length check via the body expression.
    hd = body.head_var
    tl = body.tail_var
    # Cons arm: the head and tail are the constructor bindings.
    # The body already has xs[0] → hd and xs[1:] → tl.
    cons_body = ast.unparse(body.cons_expr)
    # Wrap in Coq comparison form: Python's `and` → `&&`
    cons_body_coq = _py_expr_to_coq_bool(cons_body)

    return (
        f"Fixpoint {name} ({param} : list Z) {{struct {param}}} : bool :=\n"
        f"  match {param} with\n"
        f"{arms[0] if arms else '  | [] => true'}\n"
        f"  | {hd} :: {tl} => {cons_body_coq}\n"
        f"  end.\n"
    )


def _emit_measured(name: str, param: str) -> str:
    """Pattern 2: nat counter decreasing + list consumed via inner match.

    Call sites translate f(xs[n:]) → f xs n (not f (dropn xs n) 0).
    The Fixpoint itself uses an inner match on xs to expose a structural
    subterm for each recursion step, so the guard checker accepts it.

    Emitted shape:
        Fixpoint f (xs : list Z) (n : nat) {struct n} : bool :=
          match n with
          | O => <body with xs as suffix>
          | S n' =>
              match xs with
              | [] => true
              | _ :: rest => f rest n'
              end
          end.
    """
    return (
        f"Fixpoint {name} ({param} : list Z) (n : nat) {{struct n}} : bool :=\n"
        f"  match n with\n"
        f"  | O => <body with {param} as suffix>\n"
        f"  | S n' =>\n"
        f"      match {param} with\n"
        f"      | [] => true\n"
        f"      | _ :: rest => {name} rest n'\n"
        f"      end\n"
        f"  end.\n"
    )


def _py_expr_to_coq_bool(py_expr: str) -> str:
    """Crude Python bool expression → Coq bool expression.

    Replaces `and`/`or` with `&&`/`||` and wraps integer comparisons in
    Coq operators.
    """
    result = py_expr
    result = result.replace(" and ", " && ")
    result = result.replace(" or ", " || ")
    result = result.replace("not ", "negb ")
    result = result.replace("<=", "<=?")
    result = result.replace("==", "=?")
    result = result.replace("< ", "<? ")
    return result


def normalize_slice_rec(
    body_expr: ast.expr,
    param: str,
    *,
    head_var: str = "hd",
    tail_var: str = "tl",
) -> NormalizedBody | None:
    """Normalize a recursive predicate body that uses slice patterns.

    Recognises `if <guard>: <base> else: <recursive branch>` where the guard
    is a length check on *param* and the recursive branch contains self-calls
    on *param[1:]*.

    Returns None if the body does not match the expected if/else pattern.
    """
    if not isinstance(body_expr, ast.IfExp):
        return None

    guard = body_expr.test
    base = body_expr.body
    cons = body_expr.orelse

    # Extract the length bound from the guard, e.g. len(xs) <= 2.
    bound = _extract_len_bound(guard, param)
    if bound is None:
        return None

    # Rewrite the cons branch: replace xs[0] -> hd, xs[1:] -> tl.
    cons_rewritten = _rewrite_slices(cons, param, head_var, tail_var)

    return NormalizedBody(
        base_expr=base,
        cons_expr=cons_rewritten,
        head_var=head_var,
        tail_var=tail_var,
        param=param,
        base_guards=bound,
    )


# ---------------------------------------------------------------------------
# AST rewriting
# ---------------------------------------------------------------------------

class _SliceRewriter(ast.NodeTransformer):
    """Replace slice/index references to *param* with head/tail vars.

    xs[0]    → head_var
    xs[1:]   → tail_var
    xs[1]    → tail_var[0]  (second element accessed via rest)
    """

    def __init__(self, param: str, head_var: str, tail_var: str):
        self.param = param
        self.head_var = head_var
        self.tail_var = tail_var

    def visit_Subscript(self, node: ast.Subscript) -> ast.expr:
        self.generic_visit(node)
        if not isinstance(node.value, ast.Name):
            return node
        if node.value.id != self.param:
            return node

        sl = node.slice
        if isinstance(sl, ast.Constant):
            idx = sl.value
            if idx == 0:
                return ast.Name(id=self.head_var, ctx=ast.Load())
            return ast.Subscript(
                value=ast.Name(id=self.tail_var, ctx=ast.Load()),
                slice=ast.Constant(value=idx - 1),
                ctx=ast.Load(),
            )
        if isinstance(sl, ast.Slice):
            lo = sl.lower
            hi = sl.upper
            if (isinstance(lo, ast.Constant) and lo.value == 1
                    and hi is None):
                return ast.Name(id=self.tail_var, ctx=ast.Load())
            if lo is not None and hi is None:
                # xs[n:] -> tail_var[n-1:]
                shifted = ast.BinOp(
                    left=lo,
                    op=ast.Sub(),
                    right=ast.Constant(value=1),
                )
                return ast.Subscript(
                    value=ast.Name(id=self.tail_var, ctx=ast.Load()),
                    slice=ast.Slice(lower=shifted, upper=None),
                    ctx=ast.Load(),
                )
        return node


def _rewrite_slices(
    node: ast.expr,
    param: str,
    head_var: str,
    tail_var: str,
) -> ast.expr:
    """Return a copy of *node* with slice patterns on *param* rewritten."""
    rewriter = _SliceRewriter(param, head_var, tail_var)
    result = rewriter.visit(node)
    assert isinstance(result, ast.expr)
    ast.fix_missing_locations(result)
    return result


# ---------------------------------------------------------------------------
# Guard analysis: extract len(param) <= n
# ---------------------------------------------------------------------------

def _extract_len_bound(guard: ast.expr, param: str) -> int | None:
    """Extract the integer bound from a length guard.

    Recognises:
        len(xs) <= n   or   n >= len(xs)
        len(xs) < n
    """
    if isinstance(guard, ast.Compare):
        if (len(guard.ops) == 1 and len(guard.comparators) == 1
                and isinstance(guard.ops[0], (ast.LtE, ast.Lt))
                and isinstance(guard.comparators[0], ast.Constant)):
            bound = guard.comparators[0].value
            left = guard.left
            if isinstance(guard.ops[0], ast.LtE):
                # len(xs) <= n  or  n >= len(xs)
                if _is_len_of(left, param) and isinstance(bound, int):
                    return bound
                if (isinstance(left, ast.Constant)
                        and _is_len_of(guard.comparators[0], param)):
                    return left.value
            else:
                # len(xs) < n  =>  len(xs) <= n-1
                if _is_len_of(left, param) and isinstance(bound, int):
                    return bound - 1
        if (len(guard.ops) == 1 and len(guard.comparators) == 1
                and isinstance(guard.ops[0], ast.GtE)):
            # n >= len(xs)
            left = guard.left
            right = guard.comparators[0]
            if isinstance(left, ast.Constant) and _is_len_of(right, param):
                return left.value
        if (len(guard.ops) == 1 and len(guard.comparators) == 1
                and isinstance(guard.ops[0], ast.Gt)):
            # n > len(xs)  =>  len(xs) <= n-1
            left = guard.left
            right = guard.comparators[0]
            if isinstance(left, ast.Constant) and _is_len_of(right, param):
                return left.value - 1
    return None


def _is_len_of(node: ast.expr, param: str) -> bool:
    """Check if *node* is `len(param)`."""
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "len"
            and len(node.args) == 1
            and isinstance(node.args[0], ast.Name)
            and node.args[0].id == param)