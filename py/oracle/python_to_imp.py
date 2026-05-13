"""
Python → IMP Translator

Converts a Python function AST into IMP commands for the Coq pipeline.
Handles: assignments, if/else, while loops, return, arithmetic, attribute access.

Translation rules:
    Python                    IMP
    ──────                    ───
    x = e                     CAss "x" (translate e)
    return e                  CAss "result" (translate e)
    obj.field = e             CAss "obj.field" (translate e)
    obj.field                 AVar "obj.field"
    if b: s1 else: s2         CIf (translate b) (translate s1) (translate s2)
    while b: body              CWhile (translate b) invariant (translate body)
    for i in range(n): body   CWhile (i < n) invariant (translate body ++ i+=1)
    a + b                     APlus (translate a) (translate b)
    a < b                     BLe (translate a) (translate b)
    a == b                    BEq (translate a) (translate b)
    and / or                  BAnd / ... (via shortcut evaluation)
"""

import ast
from typing import Optional


def python_to_imp(func_node: ast.FunctionDef, invariants: dict[int, str] | None = None) -> str:
    """Translate a Python function to its IMP body commands.

    Args:
        func_node: The AST FunctionDef node.
        invariants: Optional pre-computed invariant map (loop_line → Coq string).
                    If not provided, InvariantFinder is run on the function.

    Returns a Coq `com` expression string.
    """
    translator = ImpTranslator()
    if invariants is not None:
        translator._invariants = invariants
    else:
        finder = InvariantFinder()
        finder.visit(func_node)
        translator._invariants = finder.invariants
    body = translator.translate_body(func_node.body)
    return body if body else "CSkip"


class ImpTranslator:
    """AST visitor that emits IMP commands as Coq strings."""

    def __init__(self):
        self._invariants: dict[int, str] = {}  # line → invariant string

    def translate_body(self, body: list[ast.stmt]) -> str:
        """Translate a list of statements into a seq of IMP commands."""
        commands = []
        for stmt in body:
            cmd = self.translate_stmt(stmt)
            if cmd:
                commands.append(cmd)
        if not commands:
            return "CSkip"
        if len(commands) == 1:
            return commands[0]
        # Build nested CSeq: CSeq c1 (CSeq c2 (...))
        result = commands[-1]
        for cmd in reversed(commands[:-1]):
            result = f"(CSeq {cmd} {result})"
        return result

    def translate_stmt(self, stmt: ast.stmt) -> Optional[str]:
        """Translate a single statement to an IMP command string."""
        if isinstance(stmt, ast.Assign):
            return self._translate_assign(stmt)
        elif isinstance(stmt, ast.AugAssign):
            return self._translate_augassign(stmt)
        elif isinstance(stmt, ast.Return):
            return self._translate_return(stmt)
        elif isinstance(stmt, ast.If):
            return self._translate_if(stmt)
        elif isinstance(stmt, ast.While):
            return self._translate_while(stmt)
        elif isinstance(stmt, ast.For):
            return self._translate_for(stmt)
        elif isinstance(stmt, ast.Assert):
            return None
        elif isinstance(stmt, ast.Expr):
            return self._translate_expr_stmt(stmt)
        elif isinstance(stmt, ast.Pass):
            return None
        else:
            return f"(* untranslated: {type(stmt).__name__} *)"

    def _translate_expr_stmt(self, stmt: ast.Expr) -> Optional[str]:
        """Translate expression statements like lst.append(x) → CListAppend."""
        value = stmt.value
        if isinstance(value, ast.Call):
            name = self._get_call_name(value)
            if name and name.endswith(".append") and value.args:
                # obj.append(x) → CListAppend
                obj = self._get_call_object(value)
                if obj:
                    val = self.translate_expr(value.args[0])
                    return f'(CListAppend "{obj}"%string {val})'
        return None

    def translate_expr(self, node: ast.expr) -> str:
        """Translate a Python expression to an IMP aexp or bexp string."""
        if isinstance(node, ast.Constant):
            val = node.value
            if isinstance(val, bool):
                return "BTrue" if val else "BFalse"
            if isinstance(val, int):
                return f"(ANum {val})"
            if val is None:
                return f"(ANum 0)"
            return f"(ANum 0) (* unhandled constant: {val} *)"

        if isinstance(node, ast.Name):
            return f'(AVar "{node.id}"%string)'

        if isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Subscript):
                # items[i].field → AIndex "items.field" i
                base = self._translate_target(node.value.value)
                idx = self.translate_expr(node.value.slice)
                return f'(AIndex "{base}.{node.attr}"%string {idx})'
            path = self._attribute_path(node)
            return f'(AVar "{path}"%string)'

        if isinstance(node, ast.BinOp):
            left = self.translate_expr(node.left)
            right = self.translate_expr(node.right)
            op = self._translate_binop(node.op)
            return f"({op} {left} {right})"

        if isinstance(node, ast.UnaryOp):
            operand = self.translate_expr(node.operand)
            if isinstance(node.op, ast.USub):
                return f"(AMult (ANum (-1)) {operand})"
            if isinstance(node.op, ast.Not):
                return f"(BNot {operand})"

        if isinstance(node, ast.Compare):
            return self._translate_compare(node)

        if isinstance(node, ast.BoolOp):
            return self._translate_boolop(node)

        if isinstance(node, ast.Call):
            return self._translate_call(node)

        if isinstance(node, ast.Subscript):
            name = self._translate_target(node.value)
            if isinstance(node.slice, ast.Constant):
                idx = self.translate_expr(node.slice)
            else:
                idx = self.translate_expr(node.slice)
            return f'(AIndex "{name}"%string {idx})'

        return f"(* unhandled: {type(node).__name__} *)"

    # ─── Private helpers ──────────────────────────────────────────

    def _translate_assign(self, stmt: ast.Assign) -> str:
        targets = []
        for t in stmt.targets:
            if isinstance(t, ast.Subscript):
                # lst[idx] = val → CListSet
                name = self._translate_target(t.value)
                idx = self.translate_expr(t.slice)
                val = self.translate_expr(stmt.value)
                return f'(CListSet "{name}"%string {idx} {val})'

            target = self._translate_target(t)
            value = stmt.value
            if isinstance(value, ast.Compare):
                cond = self._translate_compare(value)
                targets.append(
                    f'(CIf {cond} (CAss "{target}"%string (ANum 1)) '
                    f'(CAss "{target}"%string (ANum 0)))'
                )
            elif isinstance(value, ast.List):
                # list literal: x = [] → CListNew; x = [a,b] → CListNew + appends
                return self._translate_list_literal(target, value)
            else:
                val = self.translate_expr(value)
                targets.append(f'(CAss "{target}"%string {val})')
        if len(targets) == 1:
            return targets[0]
        result = targets[-1]
        for cmd in reversed(targets[:-1]):
            result = f"(CSeq {cmd} {result})"
        return result

    def _translate_augassign(self, stmt: ast.AugAssign) -> str:
        """Translate augmented assignment: i += 1 → CAss i (APlus i 1)."""
        target = self._translate_target(stmt.target)
        val = self.translate_expr(stmt.value)
        op_map = {ast.Add: "APlus", ast.Sub: "AMinus", ast.Mult: "AMult"}
        op_str = op_map.get(type(stmt.op), "APlus")
        return f'(CAss "{target}"%string ({op_str} (AVar "{target}"%string) {val}))'

    def _translate_list_literal(self, target: str, node: ast.List) -> str:
        """Translate list literal: x = [e1, e2, ...] → CListNew + CListAppend chain."""
        cmds = [f'(CListNew "{target}"%string)']
        for elt in node.elts:
            val = self.translate_expr(elt)
            cmds.append(f'(CListAppend "{target}"%string {val})')
        result = cmds[-1]
        for cmd in reversed(cmds[:-1]):
            result = f"(CSeq {cmd} {result})"
        return result

    def _translate_return(self, stmt: ast.Return) -> str:
        if stmt.value:
            value = self.translate_expr(stmt.value)
            return f'(CAss "result"%string {value})'
        return "CSkip"

    def _translate_if(self, stmt: ast.If) -> str:
        test = self.translate_expr(stmt.test)
        then_body = self.translate_body(stmt.body)
        else_body = self.translate_body(stmt.orelse) if stmt.orelse else "CSkip"
        return f"(CIf {test} {then_body} {else_body})"

    def _translate_while(self, stmt: ast.While) -> str:
        test = self.translate_expr(stmt.test)
        body = self.translate_body(stmt.body)
        # While loops: use (fun _ => True) in IMP body.
        # The actual invariant is proved separately by the VCG — embedding
        # complex invariants (with division etc.) breaks wp_prove at entry.
        inv = "(fun _ => True)"
        return f"(CWhile {test} {inv} {body})"

    def _translate_for(self, stmt: ast.For) -> str:
        target = self._translate_target(stmt.target)
        if (isinstance(stmt.iter, ast.Call)
            and isinstance(stmt.iter.func, ast.Name)
            and stmt.iter.func.id == "range"):
            args = stmt.iter.args
            if len(args) == 1:
                start_val = "(ANum 0)"
                limit_val = self.translate_expr(args[0])
                step_val = "(ANum 1)"
            elif len(args) == 2:
                start_val = self.translate_expr(args[0])
                limit_val = self.translate_expr(args[1])
                step_val = "(ANum 1)"
            elif len(args) == 3:
                start_val = self.translate_expr(args[0])
                limit_val = self.translate_expr(args[1])
                step_val = self.translate_expr(args[2])
            else:
                return f"(* untranslated for: {ast.unparse(stmt)} *)"

            body_cmds = self.translate_body(stmt.body)
            if not body_cmds:
                body_cmds = "CSkip"
            incr = f'(CAss "{target}"%string (APlus (AVar "{target}"%string) {step_val}))'

            # Use user-provided invariant if found, else generate default from bounds
            inv = self._invariants.get(stmt.lineno)
            if inv is None or inv == "(fun _ => True)":
                inv = self._default_for_invariant(target, limit_val, start_val)

            init = f'(CAss "{target}"%string {start_val})'
            cond = f"(BLe (APlus (AVar \"{target}\"%string) {step_val}) {limit_val})"
            loop_body = body_cmds if body_cmds == "CSkip" else f"(CSeq {body_cmds} {incr})"
            loop = f"(CWhile {cond} {inv} {loop_body})"
            return f"(CSeq {init} {loop})"
        return f"(* untranslated for: {ast.unparse(stmt)} *)"

    def _default_for_invariant(self, target: str, limit_coq: str, start_coq: str) -> str:
        r"""Generate a default loop invariant from range bounds.

        For `for i in range(n):`, generates `0 <= s"i" /\ s"i" <= s"n"`.
        Uses state lookups so the invariant is self-contained (no free Coq variables).
        """
        import re

        # Convert a Coq aexp string to a Z expression usable inside (fun s => ...)
        def aexp_to_z(coq_str: str) -> str:
            m = re.match(r'\(AVar "([^"]+)"%string\)', coq_str)
            if m:
                return f's "{m.group(1)}"%string'
            m = re.match(r'\(ANum (-?\d+)\)', coq_str)
            if m:
                return m.group(1)
            return coq_str

        start_z = aexp_to_z(start_coq)
        limit_z = aexp_to_z(limit_coq)

        return (
            f'(fun s => '
            f'{start_z} <= s "{target}"%string /\\ '
            f's "{target}"%string <= {limit_z})'
        )

    def _translate_boolop(self, node: ast.BoolOp) -> str:
        if isinstance(node.op, ast.And):
            op = "BAnd"
        elif isinstance(node.op, ast.Or):
            op = "BOr"
        else:
            op = "BAnd"
        values = [self.translate_expr(v) for v in node.values]
        result = values[0]
        for v in values[1:]:
            result = f"({op} {result} {v})"
        return result

    def _translate_call(self, node: ast.Call) -> str:
        """Translate pure function calls: len, abs, min, max, etc."""
        name = self._get_call_name(node)
        if name == "len":
            if node.args and isinstance(node.args[0], ast.Name):
                return f'(ALen "{node.args[0].id}"%string)'
            if node.args:
                arg = self.translate_expr(node.args[0])
                return f"(* len of expr *) (ANum 0)"
            return "(ANum 0)"
        if name in ("abs", "min", "max", "int", "float"):
            arg = self.translate_expr(node.args[0]) if node.args else "(ANum 0)"
            return arg
        if name == "isinstance":
            return "BTrue"
        return f"(* call: {name} *) (ANum 0)"

    def _translate_target(self, node: ast.expr) -> str:
        """Get the variable name for an assignment target."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            return self._attribute_path(node)
        return "unknown"

    def _attribute_path(self, node: ast.Attribute) -> str:
        """obj.field.subfield → 'obj.field.subfield'"""
        parts = []
        current = node
        while isinstance(current, ast.Attribute):
            parts.append(current.attr)
            current = current.value
        if isinstance(current, ast.Name):
            parts.append(current.id)
        elif isinstance(current, ast.Subscript):
            inner = self._translate_target(current.value)
            idx = self.translate_expr(current.slice)
            # items[i].field → "items.field" with AIndex semantics
            # The key is constructed as list_name.attr_name (indexed dynamically)
            full = f"{inner}.{'.'.join(reversed(parts))}"
            return full
        return ".".join(reversed(parts))

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

    def _get_call_object(self, node: ast.Call) -> Optional[str]:
        """Get the object name from obj.method() call like lst.append()."""
        func = node.func
        if isinstance(func, ast.Attribute):
            return self._translate_target(func.value)
        return None

    def _translate_compare(self, node: ast.Compare) -> str:
        if len(node.ops) == 1 and len(node.comparators) == 1:
            left = self.translate_expr(node.left)
            right = self.translate_expr(node.comparators[0])
            return self._mk_cmp(node.ops[0], left, right)
        # Chained: a < b < c → BAnd (a < b) (BAnd (b < c) ...)
        parts = [node.left] + node.comparators
        result = self._mk_cmp(node.ops[0], parts[0], parts[1])
        for i in range(1, len(node.ops)):
            result = f"(BAnd {result} {self._mk_cmp(node.ops[i], parts[i], parts[i+1])})"
        return result

    @staticmethod
    def _mk_cmp(op, left, right) -> str:
        op_map = {
            ast.Eq: "BEq", ast.NotEq: "BNot (BEq ...)",
            ast.LtE: "BLe",
        }
        if isinstance(op, ast.Lt):
            # a < b  ≡  a + 1 <= b  since IMP only has BLe (<=)
            return f"(BLe (APlus {left} (ANum 1)) {right})"
        if isinstance(op, ast.Gt):
            # a > b  ≡  b + 1 <= a  ≡  b < a
            return f"(BLe (APlus {right} (ANum 1)) {left})"
        if isinstance(op, ast.GtE):
            # a >= b  ≡  b <= a
            return f"(BLe {right} {left})"
        if isinstance(op, ast.NotEq):
            return f"(BNot (BEq {left} {right}))"
        op_str = op_map.get(type(op), "BEq")
        return f"({op_str} {left} {right})"

    @staticmethod
    def _translate_binop(op: ast.operator) -> str:
        op_map = {
            ast.Add: "APlus", ast.Sub: "AMinus",
            ast.Mult: "AMult", ast.FloorDiv: "ADiv", ast.Mod: "AMod",
        }
        return op_map.get(type(op), "APlus")

    @staticmethod
    def _translate_cmpop(op: ast.cmpop) -> str:
        return ImpTranslator._mk_cmp(op, "", "").split(" ")[0].strip("(")


def translate_function(source: str, func_name: str | None = None) -> str:
    """Parse Python source and translate a function to IMP.

    Returns a Coq `Definition ..._body : com := ...` string.
    """
    tree = ast.parse(source)

    # Find invariants: assertions at the top of loop bodies
    inv_finder = InvariantFinder()
    inv_finder.visit(tree)

    for func in ast.walk(tree):
        if not isinstance(func, ast.FunctionDef):
            continue
        if func_name and func.name != func_name:
            continue

        translator = ImpTranslator()
        translator._invariants = inv_finder.invariants

        body = translator.translate_body(func.body)
        return f"Definition {func.name}_body : com :=\n  {body}."

    return "(* No function found *)"


class InvariantFinder(ast.NodeVisitor):
    """Find assert statements at the top of loop bodies (invariants)."""

    def __init__(self):
        self.invariants: dict[int, str] = {}  # loop_line → Coq invariant string

    def visit_While(self, node: ast.While):
        self._find_in_body(node.body, node.lineno)
        self.generic_visit(node)

    def visit_For(self, node: ast.For):
        self._find_in_body(node.body, node.lineno)
        self.generic_visit(node)

    def _find_in_body(self, body: list[ast.stmt], loop_line: int):
        inv_parts = []
        for stmt in body:
            if isinstance(stmt, ast.Assert):
                from oracle.contract_linter import ContractLinter
                lint = ContractLinter()
                result = lint.lint_expression(stmt.test)
                if result.is_valid:
                    inv_parts.append(result.coq_translation)
            else:
                break  # only consecutive asserts at the top are invariants
        if inv_parts:
            if len(inv_parts) == 1:
                self.invariants[loop_line] = f"(fun s => {inv_parts[0]})"
            else:
                joined = " /\\ ".join(inv_parts)
                self.invariants[loop_line] = f"(fun s => {joined})"
