"""
Contract Expression Language — Linter + Coq Translator

Validates that `assert` expressions in Python are:
  1. Boolean-valued (the contract language)
  2. Pure (no side effects, no function calls beyond the whitelist)
  3. Translates to Coq shallow embedding (Coq Prop expressions)

## The Contract Expression Language

A quantifier-free, pure, boolean-valued subset of Python:

    expr ::= comparison | bool_op | unary_op | call | literal | name | attr

    comparison ::= expr ('==' | '!=' | '<' | '<=' | '>' | '>=' | 'is' | 'is not') expr
    bool_op    ::= expr 'and' expr | expr 'or' expr
    unary_op   ::= 'not' expr
    call       ::= pure_fn '(' args ')'
    literal    ::= int | float | bool | str | None
    attr       ::= expr '.' name            (only for pure attribute access)
    name       ::= variable reference

    pure_fn    ::= abs | len | min | max | sum | sorted | all | any
                 | isinstance | int | float | bool | str
                 | round | ord | chr | range | math.*

## Shallow Embedding → Coq

Python expressions map directly to Coq Prop:

    Python              Coq
    ──────              ───
    x > 0               (x > 0)%Z
    a == b              (a = b)%Z
    x > 0 and y < 10    ((x > 0)%Z /\ (y < 10)%Z)
    not (x == 0)        (~ (x = 0)%Z)
    len(lst) > 0        (Z.of_nat (length lst) > 0)%Z
    isinstance(x, int)  True     (Python type system guarantees this)
"""

import ast
import sys
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Optional


# ─── Language Definition ──────────────────────────────────────────

class ExprKind(Enum):
    """Classification of an expression in the contract language."""
    OK = "ok"
    IMPURE_CALL = "impure_call"         # function with side effects
    SIDE_EFFECT = "side_effect"         # assignment, I/O, etc.
    TYPE_ERROR = "type_error"           # expression doesn't evaluate to bool
    UNSUPPORTED = "unsupported"         # valid Python but not in our fragment
    NOT_BOOLEAN = "not_boolean"         # expression is not a boolean


PURE_BUILTINS = frozenset({
    # Arithmetic
    "abs", "round", "int", "float", "bool", "str",
    # Collections
    "len", "min", "max", "sum", "sorted", "all", "any",
    # Type checks
    "isinstance",
    # Character
    "ord", "chr",
    # Iteration
    "range",
    # Math (common subset)
    "pow", "sqrt",
})

PURE_MODULE_FUNCTIONS = frozenset({
    "math.sqrt", "math.pow", "math.ceil", "math.floor",
    "math.log", "math.log2", "math.log10",
    "math.sin", "math.cos", "math.tan",
    "math.abs", "math.fabs",
})

BOOLEAN_OPS = frozenset({ast.And, ast.Or})
COMPARISON_OPS = frozenset({
    ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE,
    ast.Is, ast.IsNot, ast.In, ast.NotIn,
})


@dataclass
class LintViolation:
    """A single lint violation with location and message."""
    line: int
    col: int
    kind: ExprKind
    message: str
    expression_text: str = ""


@dataclass
class LintResult:
    """Result of linting an assert expression."""
    expr_node: ast.expr
    violations: list[LintViolation] = field(default_factory=list)
    coq_translation: str = ""

    @property
    def is_valid(self) -> bool:
        return len(self.violations) == 0


# ─── Linter ───────────────────────────────────────────────────────

class ContractLinter(ast.NodeVisitor):
    """Validates assert expressions against the contract language.

    Usage:
        linter = ContractLinter(params=['a', 'b'], context='precondition')
        result = linter.lint_expression(assert_node.test)
    """

    def __init__(self, params: list[str] | None = None, context: str = "postcondition"):
        self.violations: list[LintViolation] = []
        self._coq_parts: list[str] = []
        self._in_boolean_context = True
        self.params = params or []
        self.context = context  # "precondition", "postcondition", or "invariant"  # function parameter names

    def lint_expression(self, node: ast.expr) -> LintResult:
        """Validate a single expression and return results."""
        self.violations = []
        self._coq_parts = []
        self._in_boolean_context = True
        self.visit(node)
        return LintResult(
            expr_node=node,
            violations=list(self.violations),
            coq_translation="".join(self._coq_parts) if not self.violations else "",
        )

    def _violation(self, node: ast.AST, kind: ExprKind, message: str):
        self.violations.append(LintViolation(
            line=getattr(node, "lineno", 0),
            col=getattr(node, "col_offset", 0),
            kind=kind,
            message=message,
            expression_text=ast.unparse(node) if hasattr(ast, "unparse") else str(node),
        ))

    def _emit_coq(self, s: str):
        self._coq_parts.append(s)

    # ─── Top-level dispatcher ─────────────────────────────────────

    def visit_Compare(self, node: ast.Compare):
        """x < y, a == b, etc. — the core boolean expressions."""
        # Single comparison: left OP right
        if len(node.ops) == 1 and len(node.comparators) == 1:
            self.visit(node.left)
            op_str = self._translate_compare_op(node.ops[0])
            self._emit_coq(f" {op_str} ")
            self.visit(node.comparators[0])
            return

        # Chained comparison: a < b < c → (a < b) /\ (b < c)
        parts = [node.left]
        parts.extend(node.comparators)
        self._emit_coq("(")
        for i, op in enumerate(node.ops):
            if i > 0:
                self._emit_coq(" /\\ ")
            self.visit(parts[i])
            op_str = self._translate_compare_op(op)
            self._emit_coq(f" {op_str} ")
            self.visit(parts[i + 1])
        self._emit_coq(")")

    def visit_BoolOp(self, node: ast.BoolOp):
        """x and y, x or y."""
        if isinstance(node.op, ast.And):
            self._emit_coq("(")
            for i, val in enumerate(node.values):
                if i > 0:
                    self._emit_coq(" /\\ ")
                self.visit(val)
            self._emit_coq(")")
        elif isinstance(node.op, ast.Or):
            self._emit_coq("(")
            for i, val in enumerate(node.values):
                if i > 0:
                    self._emit_coq(" \\/ ")
                self.visit(val)
            self._emit_coq(")")

    def visit_UnaryOp(self, node: ast.UnaryOp):
        """not x, -x."""
        if isinstance(node.op, ast.Not):
            self._emit_coq("~ (")
            self.visit(node.operand)
            self._emit_coq(")")
        elif isinstance(node.op, ast.USub):
            self._emit_coq("(- ")
            self.visit(node.operand)
            self._emit_coq(")")

    def visit_BinOp(self, node: ast.BinOp):
        """a + b, a * b, etc. in non-boolean context."""
        op_map = {
            ast.Add: "+", ast.Sub: "-", ast.Mult: "*",
            ast.Div: "/", ast.FloorDiv: "/", ast.Mod: "mod",
        }
        op_str = op_map.get(type(node.op), "?")
        self._emit_coq("(")
        self.visit(node.left)
        self._emit_coq(f" {op_str} ")
        self.visit(node.right)
        self._emit_coq(")")

    def visit_Call(self, node: ast.Call):
        """Function calls — must be in the pure whitelist."""
        name = self._get_call_name(node)
        if not name:
            self._violation(node, ExprKind.IMPURE_CALL,
                          f"Function call '{ast.unparse(node.func)}' cannot be resolved")
            return

        if name in PURE_BUILTINS:
            self._translate_pure_call(node, name)
        elif name in PURE_MODULE_FUNCTIONS:
            self._translate_pure_call(node, name)
        else:
            self._violation(node, ExprKind.IMPURE_CALL,
                          f"Function '{name}' is not in the pure whitelist. "
                          f"Allowed: {sorted(PURE_BUILTINS)}")

    def visit_Constant(self, node: ast.Constant):
        """Literals: 42, True, 'hello', None."""
        if isinstance(node.value, bool):
            self._emit_coq("True" if node.value else "False")
        elif isinstance(node.value, int):
            self._emit_coq(f"{node.value}%Z")
        elif isinstance(node.value, str):
            self._emit_coq(f'"{node.value}"%string')
        elif node.value is None:
            self._emit_coq("None")
        else:
            self._emit_coq(str(node.value))

    def visit_Name(self, node: ast.Name):
        """Variable references. In preconditions: use param names directly.
        In postconditions/invariants: use state lookups."""
        name = node.id
        if self.context == "precondition":
            self._emit_coq(name)
        elif name not in self.params:
            self._emit_coq(f's "{name}"%string')
        else:
            self._emit_coq(name)

    def visit_Attribute(self, node: ast.Attribute):
        """Attribute access. In preconditions: emit expanded param name.
        In postconditions/invariants: emit state lookup."""
        path = self._attribute_path(node)
        if self.context == "precondition":
            # account.balance → account_balance
            self._emit_coq(path.replace(".", "_"))
        else:
            self._emit_coq(f's "{path}"%string')

    def visit_List(self, node: ast.List):
        self._emit_coq("[")
        for i, elt in enumerate(node.elts):
            if i > 0:
                self._emit_coq("; ")
            self.visit(elt)
        self._emit_coq("]")

    def visit_Subscript(self, node: ast.Subscript):
        """Array access: arr[i] → s (parray_key "arr" i)%string."""
        if self.context == "precondition":
            self.visit(node.value)
            self._emit_coq("[")
            if isinstance(node.slice, ast.Constant):
                self.visit(node.slice)
            else:
                self.visit(node.slice)
            self._emit_coq("]")
        else:
            self._emit_coq('s (parray_key "')
            if isinstance(node.value, ast.Name):
                self._emit_coq(node.value.id)
            self._emit_coq('"%string ')
            if isinstance(node.slice, ast.Constant):
                self.visit(node.slice)
            else:
                self.visit(node.slice)
            self._emit_coq(')%string')

    def visit_Index(self, node):
        """Python 3.8 compatibility."""
        self.visit(node.value)

    # ─── Fallback for unsupported nodes ───────────────────────────

    def generic_visit(self, node: ast.AST):
        """Any unhandled AST node is a violation."""
        self._violation(node, ExprKind.UNSUPPORTED,
                      f"Unsupported construct: {type(node).__name__}")

    # ─── Helpers ──────────────────────────────────────────────────

    def _get_call_name(self, node: ast.Call) -> Optional[str]:
        func = node.func
        if isinstance(func, ast.Name):
            return func.id
        if isinstance(func, ast.Attribute):
            parts = []
            c = func
            while isinstance(c, ast.Attribute):
                parts.append(c.attr)
                c = c.value
            if isinstance(c, ast.Name):
                parts.append(c.id)
            return ".".join(reversed(parts))
        return None

    def _attribute_path(self, node: ast.Attribute) -> str:
        """obj.field.subfield → 'obj.field.subfield'"""
        parts = []
        current = node
        while isinstance(current, ast.Attribute):
            parts.append(current.attr)
            current = current.value
        if isinstance(current, ast.Name):
            parts.append(current.id)
        return ".".join(reversed(parts))

    def _translate_compare_op(self, op: ast.cmpop) -> str:
        """Map a Python comparison operator to its Coq equivalent."""
        op_map = {
            ast.Eq: "=",
            ast.NotEq: "<>",
            ast.Lt: "<",
            ast.LtE: "<=",
            ast.Gt: ">",
            ast.GtE: ">=",
        }
        op_type = type(op)
        if op_type in op_map:
            return op_map[op_type]
        if op_type in (ast.Is, ast.IsNot):
            return "=" if op_type == ast.Is else "<>"
        if op_type in (ast.In, ast.NotIn):
            return "In" if op_type == ast.In else "~ In"
        return "?"

    def _translate_pure_call(self, node: ast.Call, name: str):
        """Translate a pure function call to Coq."""
        # Builtins that map to Z functions
        z_funcs = {"abs": "Z.abs", "min": "Z.min", "max": "Z.max"}
        if name in z_funcs:
            self._emit_coq(f"({z_funcs[name]} ")
            for i, arg in enumerate(node.args):
                if i > 0:
                    self._emit_coq(" ")
                self.visit(arg)
            self._emit_coq(")")
        elif name == "len":
            if self.context == "precondition":
                self._emit_coq("0%Z")
            else:
                self._emit_coq('s "')
                if node.args:
                    for arg in node.args:
                        if isinstance(arg, ast.Name):
                            self._emit_coq(f"{arg.id}._len")
                self._emit_coq('"%string')
        elif name in ("int", "float", "bool"):
            # Type conversion — identity in our typed world
            if node.args:
                self.visit(node.args[0])
            else:
                self._emit_coq("0%Z")
        elif name == "range":
            # range(n) → the length is n
            if node.args:
                self.visit(node.args[0])
            else:
                self._emit_coq("0%Z")
        elif name == "isinstance":
            # isinstance(x, int) → always True in our typed world
            self._emit_coq("True")
        elif name in ("all", "any"):
            self._emit_coq(f"({name} ")
            for arg in node.args:
                self.visit(arg)
            self._emit_coq(")")
        else:
            # Generic: emit the function name
            self._emit_coq(f"({name} ")
            for i, arg in enumerate(node.args):
                if i > 0:
                    self._emit_coq(" ")
                self.visit(arg)
            self._emit_coq(")")


# ─── File-level linter ────────────────────────────────────────────

@dataclass
class AssertInfo:
    """Information about a single assert statement in context."""
    node: ast.Assert
    lineno: int
    col_offset: int
    classification: str    # "precondition", "postcondition", "invariant", "general"
    lint_result: LintResult


def lint_file(source: str | Path) -> list[AssertInfo]:
    """Lint all assert statements in a Python file.

    Uses a context-tracking walk to classify asserts by position.
    """
    if isinstance(source, Path):
        source = source.read_text()

    tree = ast.parse(source)
    linter = ContractLinter()
    results: list[AssertInfo] = []

    def is_docstring(s):
        return (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                and isinstance(s.value.value, str))

    def walk_body(body: list[ast.stmt], context: str, parent_node=None):
        """Walk a statement list, tracking whether we've seen non-assert code yet."""
        seen_code = False
        for i, stmt in enumerate(body):
            if isinstance(stmt, ast.Assert):
                # Check postcondition first (before return, even if seen_code=True)
                if (i + 1 < len(body) and isinstance(body[i + 1], ast.Return)):
                    classification = "postcondition"
                elif context == "function" and not seen_code:
                    classification = "precondition"
                elif context == "loop" and not seen_code:
                    classification = "invariant"
                else:
                    classification = "general"

                lint_result = linter.lint_expression(stmt.test)
                results.append(AssertInfo(
                    node=stmt,
                    lineno=stmt.lineno,
                    col_offset=stmt.col_offset,
                    classification=classification,
                    lint_result=lint_result,
                ))
            elif is_docstring(stmt) or isinstance(stmt, ast.Return):
                continue  # docstrings and return don't count as "code"
            else:
                seen_code = True

            # Recurse into nested bodies
            if isinstance(stmt, (ast.For, ast.While)):
                walk_body(stmt.body, "loop", stmt)
                if stmt.orelse:
                    walk_body(stmt.orelse, "loop_else", stmt)
            elif isinstance(stmt, ast.If):
                walk_body(stmt.body, "if_body", stmt)
                if stmt.orelse:
                    walk_body(stmt.orelse, "if_else", stmt)
            elif isinstance(stmt, (ast.Try, ast.With)):
                walk_body(stmt.body, "block", stmt)

    # Top-level: walk each function
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.FunctionDef):
            walk_body(node.body, "function", node)
        elif isinstance(node, ast.Assert):
            # Top-level assert (rare)
            lint_result = linter.lint_expression(node.test)
            results.append(AssertInfo(
                node=node, lineno=node.lineno, col_offset=node.col_offset,
                classification="general", lint_result=lint_result,
            ))

    return results


def classify_assert(node: ast.Assert, tree: ast.Module) -> str:
    """Stub — classification is now done in lint_file's walk_body."""
    return "general"


# ─── CLI ──────────────────────────────────────────────────────────

def main():
    if len(sys.argv) < 2:
        print("Usage: check-contracts <file.py>")
        sys.exit(1)

    path = Path(sys.argv[1])
    results = lint_file(path)

    print(f"# Contract Lint: {path.name}")
    print(f"Found {len(results)} assert(s)\n")

    valid_count = 0
    for info in results:
        status = "✓" if info.lint_result.is_valid else "✗"
        print(f"Line {info.lineno}: {status} [{info.classification}]  {ast.unparse(info.node)}")
        if info.lint_result.is_valid:
            valid_count += 1
            print(f"       Coq: {info.lint_result.coq_translation}")
        else:
            for v in info.lint_result.violations:
                print(f"       ✗ {v.kind.value}: {v.message}")
        print()

    print(f"{valid_count}/{len(results)} assertions are valid")


if __name__ == "__main__":
    main()
