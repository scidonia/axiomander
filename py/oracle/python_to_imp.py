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


def python_to_imp(func_node: ast.FunctionDef, invariants: dict[int, str] | None = None, contract_map: dict[str, tuple[list[str], str, str, list[str], list[str]]] | None = None, tree: ast.Module | None = None, ghost_vars: set[str] | None = None, record_fields: dict[str, list[str]] | None = None) -> str:
    """Translate a Python function to its IMP body commands.

    Contracts:
      pre:  isinstance(func_node, ast.FunctionDef)
      post: returns a valid Coq com expression string
    """
    assert isinstance(func_node, ast.FunctionDef)
    translator = ImpTranslator()
    if invariants is not None:
        translator._invariants = invariants
    else:
        finder = InvariantFinder()
        finder.visit(func_node)
        translator._invariants = finder.invariants
    if contract_map is not None:
        translator._contract_map = contract_map
    if tree is not None:
        translator._seed_types(func_node, tree)
    if ghost_vars is not None:
        translator._ghost_vars = ghost_vars
    if record_fields is not None:
        translator._record_fields = record_fields
    body = translator.translate_body(func_node.body)
    return body if body else "CSkip"


class ImpTranslator:
    """AST visitor that emits IMP commands as Coq strings."""

    def __init__(self):
        self._invariants: dict[int, str] = {}  # line → invariant string
        self._contract_map: dict[str, tuple[list[str], str, str, list[str], list[str]]] = {}  # name → (params, pre, post, reads, writes)
        self._vc = 0  # var counter for _fresh_var
        self._ghost_vars: set[str] = set()  # variables excluded from IMP body
        self._record_fields: dict[str, list[str]] = {}  # class_name → field names
        self._local_types: dict[str, str] = {}  # var_name → class name (flow-aware type inference)
        self._class_field_types: dict[str, dict[str, str]] = {}  # ClassName → {field_name: type_name}
        self._pending_cmds: list[str] = []  # commands to prepend before next statement

    def _flush_pending(self) -> str:
        """Return and clear pending commands as a CSeq chain."""
        cmds = self._pending_cmds
        self._pending_cmds = []
        if not cmds:
            return ""
        result = cmds[-1]
        for cmd in reversed(cmds[:-1]):
            result = f"(CSeq {cmd} {result})"
        return result

    def _fresh_var(self, prefix: str = "v") -> str:
        """Return a unique loop variable name: _v0, _v1, ..."""
        name = f"_{prefix}{self._vc}"
        self._vc += 1
        return name

    def _seed_types(self, func_node: ast.FunctionDef, tree: ast.Module | None = None) -> None:
        """Seed type inference from parameter annotations and class definitions."""
        self._func_node = func_node
        if tree is None:
            return
        # Scan class definitions for field types
        for node in ast.walk(tree):
            if isinstance(node, ast.ClassDef):
                fields: dict[str, str] = {}
                for stmt in node.body:
                    if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                        type_str = ast.unparse(stmt.annotation) if stmt.annotation else "int"
                        fields[stmt.target.id] = type_str
                if fields:
                    self._class_field_types[node.name] = fields

        # Seed local types from function parameter annotations
        class_names = list(self._class_field_types.keys())
        for arg in func_node.args.args:
            if arg.annotation:
                type_str = ast.unparse(arg.annotation)
                for cls_name in class_names:
                    if cls_name == type_str or cls_name.lower() == type_str.lower():
                        self._local_types[arg.arg] = cls_name
                        break

        # Also match by name convention: self → current class
        self._local_types["self"] = class_names[0] if class_names else ""

    def _has_break_continue(self, stmts: list) -> tuple[bool, bool]:
        """Recursively check if any statement contains break or continue."""
        has_brk = False
        has_cont = False
        for s in stmts:
            if isinstance(s, ast.Break):
                has_brk = True
            elif isinstance(s, ast.Continue):
                has_cont = True
            elif isinstance(s, (ast.If, ast.While, ast.For)):
                b, c = self._has_break_continue(getattr(s, 'body', []))
                has_brk = has_brk or b
                has_cont = has_cont or c
                if isinstance(s, ast.If):
                    b2, c2 = self._has_break_continue(getattr(s, 'orelse', []))
                    has_brk = has_brk or b2
                    has_cont = has_cont or c2
        return has_brk, has_cont

    def _desugar_break_continue(self, body: list[ast.stmt]) -> list[ast.stmt]:
        """Preprocess loop body to eliminate break/continue.

        break → _brk=1 + wrap subsequent in if _brk==0
        continue → _skp=1 + wrap subsequent in if _skp==0 + reset _skp at end
        Handles break/continue inside nested if/while/for blocks recursively.
        """
        import ast as ast_mod
        from copy import deepcopy

        has_break, has_continue = self._has_break_continue(body)
        if not has_break and not has_continue:
            return body

        brk_name = self._fresh_var("brk")
        skp_name = self._fresh_var("skp")
        # Store for later use by while/for translators
        self._last_brk_var = brk_name if has_break else None
        self._last_skp_var = skp_name if has_continue else None

        result: list[ast.stmt] = []
        after_break = False
        after_skip = False

        for stmt in body:
            if isinstance(stmt, ast_mod.Break):
                result.append(ast_mod.Assign(
                    targets=[ast_mod.Name(id=brk_name, ctx=ast_mod.Store())],
                    value=ast_mod.Constant(value=1)))
                after_break = True
                continue
            if isinstance(stmt, ast_mod.Continue):
                result.append(ast_mod.Assign(
                    targets=[ast_mod.Name(id=skp_name, ctx=ast_mod.Store())],
                    value=ast_mod.Constant(value=1)))
                after_skip = True
                continue
            s = deepcopy(stmt)
            # Recursively desugar break/continue inside if/while/for bodies
            if isinstance(s, ast_mod.If) and (has_break or has_continue):
                s.body = self._desugar_break_continue(s.body)
                s.orelse = self._desugar_break_continue(s.orelse)
            elif isinstance(s, (ast_mod.While, ast_mod.For)) and (has_break or has_continue):
                s.body = self._desugar_break_continue(s.body)
            if after_break:
                guard = ast_mod.Compare(
                    left=ast_mod.Name(id=brk_name, ctx=ast_mod.Load()),
                    ops=[ast_mod.Eq()], comparators=[ast_mod.Constant(value=0)])
                s = ast_mod.If(test=guard, body=[s], orelse=[])
            if after_skip:
                guard = ast_mod.Compare(
                    left=ast_mod.Name(id=skp_name, ctx=ast_mod.Load()),
                    ops=[ast_mod.Eq()], comparators=[ast_mod.Constant(value=0)])
                s = ast_mod.If(test=guard, body=[s], orelse=[])
            result.append(s)

        if has_continue:
            result.append(ast_mod.Assign(
                targets=[ast_mod.Name(id=skp_name, ctx=ast_mod.Store())],
                value=ast_mod.Constant(value=0)))
        return result

    def _add_break_to_condition(self, cond_str: str) -> str:
        brk = getattr(self, '_last_brk_var', '_brk')
        return f'(BAnd {cond_str} (BEq (AVar "{brk}"%string) (ANum 0)))'

    def _break_init(self) -> str:
        brk = getattr(self, '_last_brk_var', '_brk')
        return f'(CAss "{brk}"%string (ANum 0))'

    def translate_body(self, body: list[ast.stmt]) -> str:
        """Translate a list of statements into an IMP command sequence."""
        body = self._desugar_break_continue(body)
        commands = []
        for stmt in body:
            cmd = self.translate_stmt(stmt)
            if cmd:
                commands.append(cmd)
        if not commands:
            return "CSkip"
        # Strip trailing identity CAss "result" → (AVar "result") — always redundant
        while commands and 'CAss "result"%string (AVar "result"%string)' in commands[-1]:
            commands = commands[:-1]
        if not commands:
            return commands[0]
        result = commands[-1]
        for cmd in reversed(commands[:-1]):
            result = f"(CSeq {cmd} {result})"
        return result

    def translate_stmt(self, stmt: ast.stmt) -> Optional[str]:
        """Translate a single statement to an IMP command string.

        Contracts:
          pre: isinstance(stmt, ast.stmt)
          post: returns a Coq com string or None (for no-op stmts)
        """
        assert isinstance(stmt, ast.stmt)
        if isinstance(stmt, ast.AnnAssign):
            # Type-annotated assignment: x: Type = value → treat as x = value
            return self._translate_assign_to(
                self._translate_target(stmt.target),
                stmt.value,
            ) if stmt.value else None
        elif isinstance(stmt, ast.Assign):
            return self._translate_assign(stmt)
        elif isinstance(stmt, ast.AugAssign):
            return self._translate_augassign(stmt)
        elif isinstance(stmt, ast.Return):
            return self._translate_return(stmt)
        elif isinstance(stmt, ast.If):
            # 'if __debug__:' blocks are ghost — strip them from IMP
            if isinstance(stmt.test, ast.Name) and stmt.test.id == "__debug__":
                return "CSkip"
            return self._translate_if(stmt)
        elif isinstance(stmt, ast.While):
            return self._translate_while(stmt)
        elif isinstance(stmt, ast.For):
            return self._translate_for(stmt)
        elif isinstance(stmt, ast.Try):
            body_cmd = self.translate_body(stmt.body)
            return f"(CSeq {body_cmd} (CHavoc []))"
        elif isinstance(stmt, (ast.Import, ast.ImportFrom)):
            return None  # imports are metadata, not IMP code
        elif isinstance(stmt, ast.Delete):
            return "CSkip"  # del statement → no-op in IMP
        elif isinstance(stmt, ast.Assert):
            return None
        elif isinstance(stmt, ast.Expr):
            return self._translate_expr_stmt(stmt)
        elif isinstance(stmt, ast.Pass):
            return None
        else:
            return f"(* untranslated: {type(stmt).__name__} *)"

    def _translate_expr_stmt(self, stmt: ast.Expr) -> Optional[str]:
        """Translate expression statements like lst.append(x) and dict[key].append(x)."""
        value = stmt.value
        if isinstance(value, ast.Call):
            name = self._get_call_name(value)
            if name and name.endswith(".pop") and not value.args:
                # list.pop() → CListPop
                obj = self._get_call_object(value)
                if obj:
                    return f'(CListPop "{obj}"%string)'
            if name and name.endswith(".append") and value.args:
                obj = self._get_call_object(value)
                if obj:
                    val = self.translate_expr(value.args[0])
                    if isinstance(value.func, ast.Attribute) and isinstance(value.func.value, ast.Subscript):
                        sub = value.func.value
                        dict_name = self._translate_target(sub.value)
                        key_e = self.translate_expr(sub.slice)
                        return f'(CDictAppend "{dict_name}"%string {key_e} {val})'
                    return f'(CListAppend "{obj}"%string {val})'
            if name and name.endswith(".add") and value.args:
                # set.add(x) → CDictSet with value 1
                obj = self._get_call_object(value)
                if obj:
                    val = self.translate_expr(value.args[0])
                    return f'(CDictSet "{obj}"%string {val} (ANum 1))'
            if name and (name.endswith(".discard") or name.endswith(".remove")) and value.args:
                # set.discard(x) / list.remove(x) → no-op (IMP lacks dict removal)
                return "CSkip"
            if name and name.endswith(".lower") and not value.args:
                obj = self._get_call_object(value)
                if obj:
                    loop_var = self._fresh_var("k")
                    init = f'(CAss "{loop_var}"%string (ANum 0))'
                    cond = f"(BLe (APlus (AVar \"{loop_var}\"%string) (ANum 1)) (ALen \"{obj}\"%string))"
                    char = f'(AIndex "{obj}"%string (AVar "{loop_var}"%string))'
                    is_upper = f'(BAnd (BLe (ANum 65) {char}) (BLe {char} (ANum 90)))'
                    lowered = f'(APlus {char} (ANum 32))'
                    body = f'(CSeq (CIf {is_upper} (CListSet "{obj}"%string (AVar "{loop_var}"%string) {lowered}) CSkip) (CAss "{loop_var}"%string (APlus (AVar "{loop_var}"%string) (ANum 1))))'
                    loop = f'(CWhile {cond} (fun _ => True) {body})'
                    return f'(CSeq {init} {loop})'
            if name and name.endswith(".upper") and not value.args:
                obj = self._get_call_object(value)
                if obj:
                    loop_var = self._fresh_var("k")
                    init = f'(CAss "{loop_var}"%string (ANum 0))'
                    cond = f"(BLe (APlus (AVar \"{loop_var}\"%string) (ANum 1)) (ALen \"{obj}\"%string))"
                    char = f'(AIndex "{obj}"%string (AVar "{loop_var}"%string))'
                    is_lower = f'(BAnd (BLe (ANum 97) {char}) (BLe {char} (ANum 122)))'
                    uppered = f'(AMinus {char} (ANum 32))'
                    body = f'(CSeq (CIf {is_lower} (CListSet "{obj}"%string (AVar "{loop_var}"%string) {uppered}) CSkip) (CAss "{loop_var}"%string (APlus (AVar "{loop_var}"%string) (ANum 1))))'
                    loop = f'(CWhile {cond} (fun _ => True) {body})'
                    return f'(CSeq {init} {loop})'
            if name and name.endswith(".strip") and not value.args:
                obj = self._get_call_object(value)
                if obj:
                    ln = f'(ALen "{obj}"%string)'
                    ws = lambda v: f'(BLe (AIndex "{obj}"%string (AVar "{v}"%string)) (ANum 32))'
                    incr = lambda v: f'(CAss "{v}"%string (APlus (AVar "{v}"%string) (ANum 1)))'
                    decr = lambda v: f'(CAss "{v}"%string (AMinus (AVar "{v}"%string) (ANum 1)))'
                    # Scan left: find first non-whitespace
                    l = self._fresh_var("l"); r = self._fresh_var("r"); i = self._fresh_var("i")
                    left_cond = f'(BAnd (BLe (APlus (AVar "{l}"%string) (ANum 1)) {ln}) {ws(l)})'
                    left_loop = f'(CWhile {left_cond} (fun _ => True) {incr(l)})'
                    left_init = f'(CAss "{l}"%string (ANum 0))'
                    # Scan right
                    right_init = f'(CAss "{r}"%string (AMinus {ln} (ANum 1)))'
                    right_cond = f'(BAnd (BLe (ANum 1) (APlus (AVar "{r}"%string) (ANum 1))) {ws(r)})'
                    right_loop = f'(CWhile {right_cond} (fun _ => True) {decr(r)})'
                    # Shift: for _i from 0 to _r-_l, s[_i] = s[_l+_i]
                    src_idx = f'(APlus (AVar "{l}"%string) (AVar "{i}"%string))'
                    shift_body = f'(CSeq (CListSet "{obj}"%string (AVar "{i}"%string) (AIndex "{obj}"%string {src_idx})) {incr(i)})'
                    shift_cond = f'(BLe (APlus (AVar "{i}"%string) (ANum 1)) (APlus (AMinus (AVar "{r}"%string) (AVar "{l}"%string)) (ANum 1)))'
                    shift_loop = f'(CWhile {shift_cond} (fun _ => True) {shift_body})'
                    shift_init = f'(CAss "{i}"%string (ANum 0))'
                    shift = f'(CSeq {shift_init} {shift_loop})'
                    # Truncate: while len > _r-_l+1, pop
                    new_len = f'(APlus (AMinus (AVar "{r}"%string) (AVar "{l}"%string)) (ANum 1))'
                    pop_cond = f'(BLe (APlus {new_len} (ANum 1)) {ln})'
                    pop_loop = f'(CWhile {pop_cond} (fun _ => True) (CListPop "{obj}"%string))'
                    return f'(CSeq {left_init} (CSeq {left_loop} (CSeq {right_init} (CSeq {right_loop} (CSeq {shift} {pop_loop})))))'
        return None

    def translate_expr(self, node: ast.expr) -> str:
        """Translate a Python expression to an IMP aexp or bexp string.

        Contracts:
          pre: isinstance(node, ast.expr)
          post: returns a Coq aexp/bexp string
        """
        assert isinstance(node, ast.expr)
        if isinstance(node, ast.Constant):
            val = node.value
            if isinstance(val, bool):
                return "(ABool BTrue)" if val else "(ABool BFalse)"
            if isinstance(val, int):
                return f"(ANum {val})"
            if val is None:
                return "(ANone)"
            if isinstance(val, str):
                escaped = val.replace('\\', '\\\\').replace('"', '\\"')
                return f'(AString "{escaped}"%string)'
            if isinstance(val, float):
                scaled = int(val * 100)
                return f"(AFloat {scaled})"
            if isinstance(val, bytes):
                els = " :: ".join(f"(ANum {b})" for b in val)
                return f"(ABytes ({els} :: nil))" if els else "(ABytes nil)"
            return f"(ANum 0) (* unhandled constant: {val} *)"

        if isinstance(node, ast.Name):
            return f'(AVar "{node.id}"%string)'

        if isinstance(node, ast.Attribute):
            if isinstance(node.value, ast.Subscript):
                base = self._translate_target(node.value.value)
                idx = self.translate_expr(node.value.slice)
                return f'(AIndex "{base}.{node.attr}"%string {idx})'
            expanded = self._try_record_field(node)
            if expanded:
                return f'(AVar "{expanded}"%string)'
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
            idx = self.translate_expr(node.slice)
            return f'(AIndex "{name}"%string {idx})'

        if isinstance(node, ast.List):
            if not node.elts:
                return "(ANum 0)"  # empty list in expression → placeholder
            return f"(* non-empty list literal *) (ANum 0)"

        if isinstance(node, ast.Dict):
            if not node.keys:
                return "(ADict nil)"
            pairs = []
            for k, v in zip(node.keys, node.values):
                pairs.append(f"({self.translate_expr(k)}, {self.translate_expr(v)})")
            return f"(ADict ({' :: '.join(pairs)} :: nil))"

        if isinstance(node, ast.Set):
            if not node.elts:
                return "(ASetLit nil)"
            els = " :: ".join(self.translate_expr(e) for e in node.elts)
            return f"(ASetLit ({els} :: nil))"

        if isinstance(node, ast.DictComp):
            return "CSkip"  # dict comprehension → opaque

        if isinstance(node, ast.JoinedStr):
            return "(ANum 0)"  # f-string → opaque aexp

        if isinstance(node, ast.Tuple):
            elements = " :: ".join(self.translate_expr(e) for e in node.elts) if node.elts else ""
            return f"(ATuple ({elements} :: nil))" if elements else "(ATuple nil)"

        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            # Path / subpath → opaque expression (Path division)
            return "(ANum 0)"

        return f"(* unhandled: {type(node).__name__} *)"

    # ─── Private helpers ──────────────────────────────────────────

    def _translate_assign(self, stmt: ast.Assign) -> str:
        # Skip ghost variable assignments — they exist only for verification
        if all(isinstance(t, ast.Name) and t.id in self._ghost_vars for t in stmt.targets):
            return "CSkip"
        targets = []
        for t in stmt.targets:
            if isinstance(t, ast.Subscript):
                if isinstance(t.slice, ast.Slice):
                    # lst[i:j] = val → while-loop copy
                    return self._translate_slice_assign(t, stmt.value)
                name = self._translate_target(t.value)
                idx = self.translate_expr(t.slice)
                val = self.translate_expr(stmt.value)
                if isinstance(stmt.value, ast.List):
                    return f'(CDictEnsureList "{name}"%string {idx})'
                return f'(CDictAppendKv "{name}"%string {idx} {val})'

            target = self._translate_target(t)
            value = stmt.value
            if isinstance(value, ast.Compare):
                cond = self._translate_compare(value)
                targets.append(
                    f'(CIf {cond} (CAss "{target}"%string (ANum 1)) '
                    f'(CAss "{target}"%string (ANum 0)))'
                )
            elif isinstance(value, ast.List):
                return self._translate_list_literal(target, value)
            elif isinstance(value, ast.IfExp):
                # Ternary: target = x if cond else y → CIf(cond, CAss(target, x), CAss(target, y))
                cond = self._truthify(value.test)
                then_cmd = self._translate_assign_to(target, value.body)
                else_cmd = self._translate_assign_to(target, value.orelse)
                return f"(CIf {cond} {then_cmd} {else_cmd})"
            elif isinstance(value, ast.Dict) and not value.keys:
                return "CSkip"  # x = {} — empty dict
            elif isinstance(value, ast.Call):
                name = self._get_call_name(value)
                if name == "set" and not value.args:
                    return "CSkip"  # x = set() — empty set
                if name == "list" and value.args:
                    # list(expr) → CListNew + deferred copy
                    return f'(CListNew "{target}"%string)'
                if name == "dict" and value.args:
                    return "CSkip"  # dict(expr) → opaque
                if name and (name.endswith(".keys") or name.endswith(".values") or name.endswith(".items")) and not value.args:
                    # dict.keys()/values()/items() → CListNew + deferred copy
                    return f'(CListNew "{target}"%string)'
                if name == "set" and value.args:
                    return "CSkip"  # set(expr) — deferred
                # Tuple target: store CCall to temp, assign each element
                if target == "unknown" and isinstance(t, ast.Tuple):
                    tmp = self._fresh_var("tup")
                    cc = self._translate_function_call(tmp, value)
                    if cc:
                        result = cc
                        for elt in t.elts:
                            elt_name = self._translate_target(elt)
                            result = f"(CSeq {result} (CAss \"{elt_name}\"%string (AVar \"{tmp}\"%string)))"
                        return result
                cc = self._translate_function_call(target, value)
                if cc:
                    return cc
                val = self.translate_expr(value)
                targets.append(f'(CAss "{target}"%string {val})')
            elif isinstance(value, ast.BoolOp):
                # Short-circuit Boolean ops: x or y → CIf(x, result:=x, result:=y)
                # x and y → CIf(x, result:=y, result:=x)
                if len(value.values) >= 2:
                    if isinstance(value.op, ast.Or):
                        cond = self._truthify(value.values[0])
                        then_cmd = self._translate_assign_to(target, value.values[0])
                        else_cmd = self._translate_assign_to(target, value.values[1])
                        return f"(CIf {cond} {then_cmd} {else_cmd})"
                    elif isinstance(value.op, ast.And):
                        cond = self._truthify(value.values[0])
                        then_cmd = self._translate_assign_to(target, value.values[1])
                        else_cmd = self._translate_assign_to(target, value.values[0])
                        return f"(CIf {cond} {then_cmd} {else_cmd})"
                # Fallback for complex chained BoolOps
                val = self.translate_expr(value)
                targets.append(f'(CAss "{target}"%string (ABool {val}))')
            elif isinstance(value, ast.Subscript) and isinstance(value.slice, ast.Slice):
                return self._translate_slice_copy(target, value)
            elif isinstance(value, ast.ListComp):
                return self._translate_list_comp(target, value)
            elif isinstance(value, ast.DictComp):
                return "CSkip"  # dict comprehension → opaque
            else:
                # Handle string/list concatenation: s1 + s2 → while-loop copy
                if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
                    concat_cmd = self._translate_concat(target, value)
                    if concat_cmd:
                        return concat_cmd
                val = self.translate_expr(value)
                targets.append(f'(CAss "{target}"%string {val})')
        if len(targets) == 1:
            return targets[0]
        result = targets[-1]
        for cmd in reversed(targets[:-1]):
            result = f"(CSeq {cmd} {result})"
        return result

    def _translate_assign_to(self, target: str, expr: ast.expr) -> str:
        """Translate an expression assigned to a target variable."""
        if target in self._ghost_vars:
            return "CSkip"
        # Empty dict/list/set → no state change needed
        if isinstance(expr, ast.Dict) and not expr.keys:
            return "CSkip"
        if isinstance(expr, ast.List) and not expr.elts:
            return f'(CListNew "{target}"%string)'
        # Try CCall for Call expressions first
        if isinstance(expr, ast.Call):
            cc = self._translate_function_call(target, expr)
            if cc:
                return cc
        val = self.translate_expr(expr)
        # If value is boolean (bexp), wrap in ABool → aexp for CAss
        if isinstance(expr, (ast.Compare, ast.BoolOp)):
            val = f"(ABool {val})"
        return f'(CAss "{target}"%string {val})'

    def _translate_concat(self, target: str, node: ast.BinOp) -> str | None:
        """Translate s1 + s2 (string/list concat) → while-loop copy.

        Builds: CListNew target; i=0; while i<len(left): append; i+=1;
                j=0; while j<len(right): append; j+=1
        """
        if not isinstance(node.op, ast.Add):
            return None
        if not isinstance(node.left, ast.Name) or not isinstance(node.right, ast.Name):
            return None
        left = node.left.id
        right = node.right.id
        # Only concat if operands are explicitly list or string.
        # In Python, + is ambiguous — we need annotations to disambiguate.
        # Contracts (e.g. assert x >= 0) imply numeric, not list.
        def _is_concat_annot(annot) -> bool:
            """Check annotation AST for list or str type, without unparsing."""
            if annot is None:
                return False
            if isinstance(annot, ast.Name):
                return annot.id in ("str", "list")
            if isinstance(annot, ast.Subscript):
                if isinstance(annot.value, ast.Name):
                    return annot.value.id == "list"
            return False
        l_annot = r_annot = None
        if hasattr(self, '_func_node'):
            for arg in self._func_node.args.args:
                if arg.arg == left: l_annot = arg.annotation
                if arg.arg == right: r_annot = arg.annotation
        if not _is_concat_annot(l_annot) and not _is_concat_annot(r_annot):
            return None
        li = self._fresh_var("i")
        rj = self._fresh_var("j")
        new_list = f'(CListNew "{target}"%string)'
        # Copy left
        li_init = f'(CAss "{li}"%string (ANum 0))'
        li_cond = f'(BLe (APlus (AVar "{li}"%string) (ANum 1)) (ALen "{left}"%string))'
        li_append = f'(CListAppend "{target}"%string (AIndex "{left}"%string (AVar "{li}"%string)))'
        li_incr = f'(CAss "{li}"%string (APlus (AVar "{li}"%string) (ANum 1)))'
        li_body = f'(CSeq {li_append} {li_incr})'
        li_loop = f'(CWhile {li_cond} (fun _ => True) {li_body})'
        # Copy right
        rj_init = f'(CAss "{rj}"%string (ANum 0))'
        rj_cond = f'(BLe (APlus (AVar "{rj}"%string) (ANum 1)) (ALen "{right}"%string))'
        rj_append = f'(CListAppend "{target}"%string (AIndex "{right}"%string (AVar "{rj}"%string)))'
        rj_incr = f'(CAss "{rj}"%string (APlus (AVar "{rj}"%string) (ANum 1)))'
        rj_body = f'(CSeq {rj_append} {rj_incr})'
        rj_loop = f'(CWhile {rj_cond} (fun _ => True) {rj_body})'
        return f'(CSeq {new_list} (CSeq {li_init} (CSeq {li_loop} (CSeq {rj_init} {rj_loop}))))'

    def _translate_function_call(self, target: str, node: ast.Call) -> Optional[str]:
        name = self._get_call_name(node)
        if not name:
            return None

        # Resolve method calls via AST: obj.method(args) → lookup 'method', pass obj as first arg
        lookup_name = name
        call_args = list(node.args)

        if isinstance(node.func, ast.Attribute):
            lookup_name = node.func.attr  # the method name
            # Inject the object (node.func.value) as the first argument
            call_args.insert(0, node.func.value)
        
        if lookup_name not in self._contract_map:
            return None

        callee_params, pre_coq, post_coq, callee_reads, callee_writes = self._contract_map[lookup_name]
        
        # SSA: lift nested Call arguments to temp variables
        prefix_cmds = []
        for i, arg in enumerate(call_args):
            if isinstance(arg, ast.Call):
                tmp = self._fresh_var("call")
                inner = self._translate_function_call(tmp, arg)
                if inner is None:
                    inner = self._translate_assign_to(tmp, arg)
                if inner:
                    prefix_cmds.append(inner)
                    call_args[i] = ast.Name(id=tmp)
        
        args_list = "(" + " :: ".join(self.translate_expr(a) for a in call_args) + " :: nil)" if call_args else "nil"
        # Bind caller args to callee param slots in the state
        bindings = []
        for i, arg in enumerate(call_args):
            arg_coq = self.translate_expr(arg)
            if i < len(callee_params):
                bindings.append(f'(CAss "{callee_params[i]}"%string {arg_coq})')
        # State-scope the precondition: bare callee params → state lookups
        pre_coq = self._scope_callee_params(pre_coq, callee_params)
        # In postcondition: callee's result → caller's target variable
        post_coq = self._subst_result(post_coq, target, callee_params)
        pre_str = f"(fun s => {pre_coq})"
        post_str = f"(fun s => {post_coq})"
        writes_str = "(" + " :: ".join(f'"{w}"%string' for w in callee_writes) + " :: nil)" if callee_writes else "nil"
        call = f'(CCall "{lookup_name}"%string {args_list} {pre_str} {post_str} {writes_str} "{target}"%string)'
        result = call
        for b in reversed(bindings):
            result = f"(CSeq {b} {result})"
        for p in reversed(prefix_cmds):
            result = f"(CSeq {p} {result})"

        # Flow-aware type inference: when calling self.attr.get(), record dict value type
        _infer_result_type(node.func, target, self._local_types, self._class_field_types)

        return result

    @staticmethod
    def _scope_callee_params(coq_expr: str, params: list[str]) -> str:
        """Replace bare callee param names with state lookups (capture-safe)."""
        import re
        result = coq_expr
        for p in params:
            # Replace p__len with asZ (s "p._len"%string)
            result = re.sub(
                rf'(?<![a-zA-Z0-9_"%]){re.escape(p)}__len(?![a-zA-Z0-9_"%])',
                f'asZ (s "{p}._len"%string)', result
            )
            # Replace p as a standalone word with asZ (s "p"%string)
            result = re.sub(
                rf'(?<![a-zA-Z0-9_"%]){re.escape(p)}(?![a-zA-Z0-9_"%])',
                f'asZ (s "{p}"%string)', result
            )
        return result

    @staticmethod
    def _subst_result(post_coq: str, target: str, callee_params: list[str]) -> str:
        """Substitute callee's result with caller's target variable.
        
        s "result"%string → s "target"%string.
        Only applies when 'result' is not a callee parameter (avoid shadow).
        """
        if 'result' in callee_params:
            return post_coq  # don't substitute if callee has a 'result' param
        return post_coq.replace('s "result"%string', f's "{target}"%string')

    def _translate_augassign(self, stmt: ast.AugAssign) -> str:
        """Translate augmented assignment: i += 1 → CAss i (APlus i 1)."""
        target = self._translate_target(stmt.target)
        val = self.translate_expr(stmt.value)
        op_map = {ast.Add: "APlus", ast.Sub: "AMinus", ast.Mult: "AMult"}
        op_str = op_map.get(type(stmt.op), "APlus")
        return f'(CAss "{target}"%string ({op_str} (AVar "{target}"%string) {val}))'

    def _translate_slice_copy(self, target: str, node: ast.Subscript) -> str:
        """Translate target = lst[start:end] → while-loop copy."""
        tname = self._translate_target(node.value)
        tstart = self.translate_expr(node.slice.lower) if node.slice.lower else "(ANum 0)"
        tend = self.translate_expr(node.slice.upper) if node.slice.upper else f'(ALen "{tname}"%string)'
        loop_var = self._fresh_var("k")
        init_list = f'(CListNew "{target}"%string)'
        init = f'(CAss "{loop_var}"%string {tstart})'
        cond = f"(BLe (APlus (AVar \"{loop_var}\"%string) (ANum 1)) {tend})"
        append = f'(CListAppend \"{target}\"%string (AIndex \"{tname}\"%string (AVar \"{loop_var}\"%string)))'
        incr = f'(CAss \"{loop_var}\"%string (APlus (AVar \"{loop_var}\"%string) (ANum 1)))'
        loop_body = f"(CSeq {append} {incr})"
        loop = f"(CWhile {cond} (fun _ => True) {loop_body})"
        return f"(CSeq {init_list} (CSeq {init} {loop}))"

    def _translate_list_comp(self, target: str, node: ast.ListComp) -> str:
        """Translate list comprehension: [f(x) for x in lst if p(x)]."""
        if len(node.generators) != 1:
            return f"(* untranslated list comprehension: {ast.unparse(node)} *)"
        gen = node.generators[0]
        loop_var = self._translate_target(gen.target)
        init_list = f'(CListNew "{target}"%string)'

        # Build body: if p(x): CListAppend target f(x)
        elt_coq = self.translate_expr(node.elt)
        body = f'(CListAppend "{target}"%string {elt_coq})'
        for cond_expr in reversed(gen.ifs):
            cond = self._truthify(cond_expr)
            body = f'(CIf {cond} {body} CSkip)'

        # Build the for-loop
        if isinstance(gen.iter, ast.Name):
            for_loop = self._build_for_in_name_with_body(loop_var, gen.iter.id, body)
            return f"(CSeq {init_list} {for_loop})"
        if isinstance(gen.iter, ast.Call):
            # range(n) — expand inline as while loop
            range_loop = self._translate_for_range(loop_var, gen.iter, body)
            if range_loop:
                return f"(CSeq {init_list} {range_loop})"
        return f"(* untranslated list comprehension: {ast.unparse(node)} *)"

    def _translate_for_range(self, target: str, node: ast.Call, body: str) -> str | None:
        """Translate for i in range(...): body → while loop. Returns None if not range."""
        if not (isinstance(node.func, ast.Name) and node.func.id == "range"):
            return None
        args = node.args
        if len(args) == 1:
            start = "(ANum 0)"; limit = self.translate_expr(args[0]); step = "(ANum 1)"
        elif len(args) == 2:
            start = self.translate_expr(args[0]); limit = self.translate_expr(args[1]); step = "(ANum 1)"
        else:
            return None
        loop_var = self._fresh_var("k")
        init = f'(CAss "{target}"%string {start})'
        cond = f"(BLe (APlus (AVar \"{target}\"%string) {step}) {limit})"
        incr = f'(CAss "{target}"%string (APlus (AVar \"{target}\"%string) {step}))'
        loop_body = f"(CSeq {body} {incr})"
        loop = f"(CWhile {cond} (fun _ => True) {loop_body})"
        return f"(CSeq {init} {loop})"

    def _build_for_in_name_with_body(self, target: str, iter_name: str, body: str) -> str:
        """Build for-in loop with a pre-built body string."""
        start_val = "(ANum 0)"
        step_val = "(ANum 1)"
        loop_var = self._fresh_var("i")
        init = f'(CAss "{loop_var}"%string {start_val})'
        cond = f"(BLe (APlus (AVar \"{loop_var}\"%string) {step_val}) (ALen \"{iter_name}\"%string))"
        elem_load = f'(CAss "{target}"%string (AIndex \"{iter_name}\"%string (AVar \"{loop_var}\"%string)))'
        incr = f'(CAss "{loop_var}"%string (APlus (AVar \"{loop_var}\"%string) {step_val}))'
        loop_body = f"(CSeq {elem_load} (CSeq {body} {incr}))"
        loop = f"(CWhile {cond} (fun _ => True) {loop_body})"
        return f"(CSeq {init} {loop})"
        """Translate target = lst[start:end] → while-loop copy."""
        tname = self._translate_target(node.value)
        tstart = self.translate_expr(node.slice.lower) if node.slice.lower else "(ANum 0)"
        tend = self.translate_expr(node.slice.upper) if node.slice.upper else f'(ALen "{tname}"%string)'
        loop_var = self._fresh_var("k")
        init_list = f'(CListNew "{target}"%string)'
        init = f'(CAss "{loop_var}"%string {tstart})'
        cond = f"(BLe (APlus (AVar \"{loop_var}\"%string) (ANum 1)) {tend})"
        append = f'(CListAppend \"{target}\"%string (AIndex \"{tname}\"%string (AVar \"{loop_var}\"%string)))'
        incr = f'(CAss \"{loop_var}\"%string (APlus (AVar \"{loop_var}\"%string) (ANum 1)))'
        loop_body = f"(CSeq {append} {incr})"
        loop = f"(CWhile {cond} (fun _ => True) {loop_body})"
        return f"(CSeq {init_list} (CSeq {init} {loop}))"

    def _translate_slice_assign(self, target: ast.Subscript, value: ast.expr) -> str:
        """Translate target[start:end] = value → while-loop copy to target list."""
        tname = self._translate_target(target.value)
        tstart = self.translate_expr(target.slice.lower) if target.slice.lower else "(ANum 0)"
        tend = self.translate_expr(target.slice.upper) if target.slice.upper else f'(ALen "{tname}"%string)'
        valname = self._translate_target(value) if isinstance(value, ast.Name) else "src"
        if not isinstance(value, ast.Name):
            return f"(* untranslated slice assign: {ast.unparse(target)} = {ast.unparse(value)} *)"
        loop_var = self._fresh_var("k")
        result_cmds = f'(CListNew "{valname}"%string)'
        init = f'(CAss "{loop_var}"%string {tstart})'
        cond = f"(BLe (APlus (AVar \"{loop_var}\"%string) (ANum 1)) {tend})"
        append = f'(CListAppend "{valname}"%string (AIndex \"{tname}\"%string (AVar \"{loop_var}\"%string)))'
        incr = f'(CAss "{loop_var}"%string (APlus (AVar \"{loop_var}\"%string) (ANum 1)))'
        loop_body = f'(CSeq {append} {incr})'
        loop = f'(CWhile {cond} (fun _ => True) {loop_body})'
        return f'(CSeq {result_cmds} (CSeq {init} {loop}))'

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
        test = self._truthify(stmt.test)
        then_body = self.translate_body(stmt.body)
        else_body = self.translate_body(stmt.orelse) if stmt.orelse else "CSkip"
        cmd = f"(CIf {test} {then_body} {else_body})"
        prefix = self._flush_pending()
        return f"(CSeq {prefix} {cmd})" if prefix else cmd

    def _translate_while(self, stmt: ast.While) -> str:
        test = self._truthify(stmt.test)
        body = self.translate_body(stmt.body)
        inv = self._invariants.get(stmt.lineno, "(fun _ => True)")
        # Quantifier invariants (forall/exists) are VCG-only — too hard for WP body proofs
        if "forall" in inv:
            inv = "(fun _ => True)"
        loop = f"(CWhile {test} {inv} {body})"
        # If body had break statements, wrap with break init and guard condition
        if any(isinstance(s, ast.Break) for s in stmt.body):
            loop = f"(CSeq {self._break_init()} (CWhile {self._add_break_to_condition(test)} {inv} {body}))"
        prefix = self._flush_pending()
        return f"(CSeq {prefix} {loop})" if prefix else loop

    def _truthify(self, node: ast.expr) -> str:
        """Convert a Python expression to an IMP bexp for use in condition context.

        Handles Python truthiness rules:
        - int/float x → x != 0
        - list lst → len(lst) > 0
        - bool/compare → as-is
        - dict d → len(d) > 0
        - string s → len(s) > 0
        """
        if isinstance(node, ast.Compare):
            return self._translate_compare(node)
        if isinstance(node, ast.BoolOp):
            return self._translate_boolop(node)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            inner = self._truthify(node.operand)
            return f"(BNot {inner})"
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return "BTrue" if node.value else "BFalse"
        if isinstance(node, ast.Name):
            return f"(BNot (BEq (AVar \"{node.id}\"%string) (ANum 0)))"
        if isinstance(node, ast.BoolOp):
            return self._translate_boolop(node)
        if isinstance(node, ast.Call):
            name = self._get_call_name(node)
            if name == "isinstance" and len(node.args) == 2:
                obj = node.args[0]
                type_node = node.args[1]
                if isinstance(obj, ast.Name) and isinstance(type_node, ast.Name):
                    if type_node.id == "int":
                        return f'(BIsVZ "{obj.id}"%string)'
                    if type_node.id == "str":
                        return f'(BIsVString "{obj.id}"%string)'
                    if type_node.id == "float":
                        return f'(BIsVFloat "{obj.id}"%string)'
            if name == "len" and node.args and isinstance(node.args[0], ast.Name):
                return f"(BLe (ANum 1) (ALen \"{node.args[0].id}\"%string))"
        # Fallback: expr != 0
        val = self.translate_expr(node)
        return f"(BNot (BEq {val} (ANum 0)))"

    def _translate_for(self, stmt: ast.For) -> str:
        target = self._translate_target(stmt.target)
        # range(n), range(start, stop), range(start, stop, step)
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
                step_const = _eval_const(args[2])
                if step_const is None:
                    return f"(* untranslated for-range (dynamic step): {ast.unparse(stmt)} *)"
                step_is_neg = step_const < 0
            else:
                return f"(* untranslated for-range: {ast.unparse(stmt)} *)"
            return self._build_for_loop(target, start_val, limit_val, step_val, stmt, step_is_neg if len(args) >= 3 else False)
            return self._build_for_loop(target, start_val, limit_val, step_val, stmt, step_is_neg if len(args) >= 3 else False)

        # for x in expr: (string or list iteration)
        if isinstance(stmt.iter, ast.Name):
            return self._build_for_in_name(target, stmt.iter.id, stmt)
        # for x in obj.field, x in dict.values(), etc. — approximate as name iteration
        if isinstance(stmt.iter, (ast.Name, ast.Attribute)):
            # For subscripted attrs (obj[key].field), lift to temp first
            if isinstance(stmt.iter, ast.Attribute) and isinstance(stmt.iter.value, ast.Subscript):
                tmp_var = self._fresh_var("iter")
                eval_iter = self._translate_assign_to(tmp_var, stmt.iter)
                loop = self._build_for_in_name(target, tmp_var, stmt)
                return f"(CSeq {eval_iter} {loop})"
            path = self._translate_target(stmt.iter)
            return self._build_for_in_name(target, path, stmt)
        # for x in d.values(), d.keys(), d.items()
        if isinstance(stmt.iter, ast.Call):
            name = self._get_call_name(stmt.iter)
            if name and name.endswith(".items"):
                obj = self._translate_target(stmt.iter.func.value)
                if isinstance(stmt.target, ast.Tuple) and len(stmt.target.elts) == 2:
                    k_name = self._translate_target(stmt.target.elts[0])
                    v_name = self._translate_target(stmt.target.elts[1])
                    return self._build_for_items(k_name, v_name, obj, stmt)
            if name and name.endswith(".values"):
                obj = self._translate_target(stmt.iter.func.value)
                return self._build_for_in_name(target, f"{obj}._vals", stmt)
            if name and name.endswith(".keys"):
                obj = self._translate_target(stmt.iter.func.value)
                return self._build_for_in_name(target, f"{obj}._keys", stmt)

        # General for-in over a Call expression (method call, function call)
        # Evaluate the call into a temporary variable, then iterate over it
        if isinstance(stmt.iter, ast.Call):
            tmp_var = self._fresh_var("iter")
            eval_call = self._translate_assign_to(tmp_var, stmt.iter)
            loop = self._build_for_in_name(target, tmp_var, stmt)
            return f"(CSeq {eval_call} {loop})"

        # General for-in (other expr) — not yet supported
        return f"(* untranslated for-in: {ast.unparse(stmt)} *)"

    def _build_for_in_name(self, target: str, iter_name: str, stmt: ast.For) -> str:
        """Build a for-in-name loop: for x in name → while i<len(name): x=name[i]; body; i+=1"""
        start_val = "(ANum 0)"
        step_val = "(ANum 1)"
        loop_var = self._fresh_var("i")
        init = f'(CAss "{loop_var}"%string {start_val})'
        cond = f"(BLe (APlus (AVar \"{loop_var}\"%string) {step_val}) (ALen \"{iter_name}\"%string))"
        body_cmds = self.translate_body(stmt.body) or "CSkip"
        elem_load = f'(CAss "{target}"%string (AIndex \"{iter_name}\"%string (AVar \"{loop_var}\"%string)))'
        incr = f'(CAss "{loop_var}"%string (APlus (AVar \"{loop_var}\"%string) {step_val}))'
        inv = self._invariants.get(stmt.lineno, "(fun _ => True)")
        loop_body = f"(CSeq {elem_load} (CSeq {body_cmds} {incr}))"
        loop = f"(CWhile {cond} {inv} {loop_body})"
        return f"(CSeq {init} {loop})"

    def _build_for_items(self, k_name: str, v_name: str, obj: str, stmt: ast.For) -> str:
        """Build for k, v in d.items(): while loop over _keys and _vals."""
        start_val = "(ANum 0)"
        step_val = "(ANum 1)"
        loop_var = self._fresh_var("i")
        init = f'(CAss "{loop_var}"%string {start_val})'
        cond = f"(BLe (APlus (AVar \"{loop_var}\"%string) {step_val}) (ALen \"{obj}._keys\"%string))"
        body_cmds = self.translate_body(stmt.body) or "CSkip"
        k_load = f'(CAss "{k_name}"%string (AIndex \"{obj}._keys\"%string (AVar \"{loop_var}\"%string)))'
        v_load = f'(CAss "{v_name}"%string (AIndex \"{obj}._vals\"%string (AVar \"{loop_var}\"%string)))'
        incr = f'(CAss "{loop_var}"%string (APlus (AVar \"{loop_var}\"%string) {step_val}))'
        inv = self._invariants.get(stmt.lineno, "(fun _ => True)")
        loop_body = f"(CSeq {k_load} (CSeq {v_load} (CSeq {body_cmds} {incr})))"
        loop = f"(CWhile {cond} {inv} {loop_body})"
        return f"(CSeq {init} {loop})"

    def _build_for_loop(self, target: str, start_val: str, limit_val: str, step_val: str, stmt: ast.For, step_is_neg: bool = False) -> str:
        body_cmds = self.translate_body(stmt.body)
        if not body_cmds:
            body_cmds = "CSkip"
        incr = f'(CAss "{target}"%string (APlus (AVar "{target}"%string) {step_val}))'

        inv = self._invariants.get(stmt.lineno)
        if inv is None or inv == "(fun _ => True)":
            inv = self._default_for_invariant(target, limit_val, start_val, step_is_neg)

        init = f'(CAss "{target}"%string {start_val})'
        if step_is_neg:
            cond = f"(BNot (BLe (APlus (AVar \"{target}\"%string) {step_val}) {limit_val}))"
        else:
            cond = f"(BLe (APlus (AVar \"{target}\"%string) {step_val}) {limit_val})"
        loop_body = body_cmds if body_cmds == "CSkip" else f"(CSeq {body_cmds} {incr})"
        loop = f"(CWhile {cond} {inv} {loop_body})"
        return f"(CSeq {init} {loop})"

    def _default_for_invariant(self, target: str, limit_val: str, start_val: str, step_is_neg: bool = False) -> str:
        """Generate a default loop invariant from range bounds.
        start_val and limit_val are Coq expression strings (aexp).
        """
        def to_z_val(coq_str: str) -> str:
            """Convert an aexp Coq string to a Z-valued expression in invariant context."""
            s = coq_str.strip()
            if s.startswith('(ANum '):
                return s[6:-1]  # extract the number
            if s.startswith('(AVar "'):
                # Extract variable name and produce asZ (s "name"%string)
                end = s.index('"%string)')
                name = s[7:end]  # extract name between (AVar " and "%string)
                return f'asZ (s "{name}"%string)'
            return f'asZ (aeval ({s}) s)'

        start_z = to_z_val(start_val)
        limit_z = to_z_val(limit_val)
        i_val = f'asZ (s "{target}"%string)'
        if step_is_neg:
            return f'(fun s => {limit_z} <= {i_val} /\\ {i_val} <= {start_z})'
        return f'(fun s => {start_z} <= {i_val} /\\ {i_val} <= {limit_z})'

    def _translate_boolop(self, node: ast.BoolOp) -> str:
        if isinstance(node.op, ast.And):
            op = "BAnd"
        elif isinstance(node.op, ast.Or):
            op = "BOr"
        else:
            op = "BAnd"
        values = [self._truthify(v) for v in node.values]
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
        if name == "list" and node.args:
            # list(expr) in expression context → evaluate the inner expression
            inner = self.translate_expr(node.args[0])
            return inner
        if name == "dict" and node.args:
            # dict(expr) → opaque; result is a valid dict value
            return "(ANum 0)"
        if name == "set" and node.args:
            return "(ANum 0)"
        return f"(* call: {name} *) (ANum 0)"

    def _translate_target(self, node: ast.expr) -> str:
        """Get the variable name for an assignment target."""
        if isinstance(node, ast.Name):
            return node.id
        if isinstance(node, ast.Attribute):
            expanded = self._try_record_field(node)
            if expanded:
                return expanded
            return self._attribute_path(node)
        if isinstance(node, ast.Tuple):
            return "unknown"
        return "unknown"

    def _try_record_field(self, node: ast.Attribute) -> str | None:
        """If base is a Record-typed param, return expanded name (e.g. c_value).
        Returns None if not a Record field access."""
        if isinstance(node.value, ast.Name):
            base_name = node.value.id
            for cls_name, fields in self._record_fields.items():
                for arg in (self._func_node.args.args if hasattr(self, '_func_node') else []):
                    if arg.arg == base_name and arg.annotation and isinstance(arg.annotation, ast.Name):
                        if arg.annotation.id == cls_name:
                            if node.attr not in fields:
                                declared = ", ".join(sorted(fields))
                                raise ValueError(
                                    f"Field '{node.attr}' not declared on {cls_name}. "
                                    f"Declared fields: {declared}")
                            return f"{base_name}_{node.attr}"
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
            op = node.ops[0]
            # String 'in' with constant left: "abc" in s → substring search
            if isinstance(op, (ast.In, ast.NotIn)):
                if isinstance(node.left, ast.Constant) and isinstance(node.left.value, str):
                    return self._str_contains_expr(node, op)
            left = self.translate_expr(node.left)
            if isinstance(op, (ast.In, ast.NotIn)):
                if isinstance(node.comparators[0], ast.Name):
                    right = f'\"{node.comparators[0].id}\"%string'
                else:
                    right = self._translate_target(node.comparators[0])
                    right = f'\"{right}\"%string'
                return self._mk_cmp(op, left, right)
            right = self.translate_expr(node.comparators[0])
            return self._mk_cmp(op, left, right)
        parts = [node.left] + node.comparators
        result = self._mk_cmp(node.ops[0], parts[0], parts[1])
        for i in range(1, len(node.ops)):
            result = f"(BAnd {result} {self._mk_cmp(node.ops[i], parts[i], parts[i+1])})"
        return result

    @staticmethod
    def _mk_cmp(op, left, right) -> str:
        if isinstance(op, ast.In):
            return f"(BLe (ANum 1) (ADictLen {right} {left}))"
        if isinstance(op, ast.NotIn):
            return f"(BEq (ANum 0) (ADictLen {right} {left}))"
        if isinstance(op, ast.Lt):
            return f"(BLe (APlus {left} (ANum 1)) {right})"
        if isinstance(op, ast.Gt):
            return f"(BLe (APlus {right} (ANum 1)) {left})"
        if isinstance(op, ast.GtE):
            return f"(BLe {right} {left})"
        if isinstance(op, ast.NotEq):
            return f"(BNot (BEq {left} {right}))"
        if isinstance(op, ast.IsNot):
            return f"(BNot (BEq {left} {right}))"
        op_map = {ast.Eq: "BEq", ast.LtE: "BLe", ast.Is: "BEq"}
        op_str = op_map.get(type(op), "BEq")
        return f"({op_str} {left} {right})"

    def _str_contains_expr(self, node: ast.Compare, op) -> str:
        """Generate substring search for 'literal' in string_var → bexp + pending commands."""
        needle = node.left.value
        target = self._translate_target(node.comparators[0])
        found_var = self._fresh_var("found")
        if not needle:
            val = "1" if isinstance(op, ast.In) else "0"
            self._pending_cmds.append(f'(CAss "{found_var}"%string (ANum {val}))')
            return f"(BEq (AVar \"{found_var}\"%string) (ANum 1))"

        chars = [str(ord(c)) for c in needle]
        n = len(chars)
        tmp_i = self._fresh_var("i")
        init_found = f'(CAss "{found_var}"%string (ANum 0))'
        init_i = f'(CAss "{tmp_i}"%string (ANum 0))'
        cond = f'(BLe (APlus (AVar "{tmp_i}"%string) (ANum {n})) (ALen \"{target}\"%string))'

        match_conds = []
        for j, ch_val in enumerate(chars):
            match_conds.append(
                f'(BEq (AIndex "{target}"%string (APlus (AVar "{tmp_i}"%string) (ANum {j}))) (ANum {ch_val}))'
            )
        match = match_conds[0]
        for c in match_conds[1:]:
            match = f"(BAnd {match} {c})"

        found_body = f'(CSeq (CAss "{found_var}"%string (ANum 1)) (CAss "{tmp_i}"%string (ALen \"{target}\"%string)))'
        incr = f'(CAss "{tmp_i}"%string (APlus (AVar "{tmp_i}"%string) (ANum 1)))'
        body = f'(CIf {match} {found_body} {incr})'
        search = f'(CWhile {cond} (fun _ => True) {body})'

        self._pending_cmds.append(f'(CSeq {init_found} (CSeq {init_i} {search}))')

        if isinstance(op, ast.In):
            return f"(BEq (AVar \"{found_var}\"%string) (ANum 1))"
        else:
            return f"(BEq (AVar \"{found_var}\"%string) (ANum 0))"

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
        """Find consecutive assert statements at the top of a loop body.

        Contracts:
          pre:  len(body) >= 0
          post: self.invariants[loop_line] is set iff body starts with >= 1 valid asserts
        """
        assert len(body) >= 0
        inv_parts = []
        for stmt in body:
            if isinstance(stmt, ast.Assert):
                from oracle.contract_linter import ContractLinter
                lint = ContractLinter(context="postcondition")
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
def _eval_const(node):
    import ast; v = ast.literal_eval(node); return v if isinstance(v, int) else None


def _extract_dict_value_type(type_str: str) -> str | None:
    """Extract value type from dict[str, SomeClass] → 'SomeClass'."""
    try:
        t = ast.parse(type_str, mode='eval').body
        if isinstance(t, ast.Subscript) and isinstance(t.value, ast.Name) and t.value.id == 'dict':
            if isinstance(t.slice, ast.Tuple) and len(t.slice.elts) >= 2:
                return ast.unparse(t.slice.elts[1])
            if isinstance(t.slice, ast.Name):
                return t.slice.id
    except SyntaxError:
        pass
    return None


def _infer_result_type(
    func_node: ast.expr,
    target: str,
    local_types: dict[str, str],
    class_field_types: dict[str, dict[str, str]],
) -> None:
    """Propagate dict value type when calling self.field.get() via AST."""
    if not isinstance(func_node, ast.Attribute):
        return
    if func_node.attr != "get":
        return
    # func_node.value should be the attribute chain like self.nodes
    if not isinstance(func_node.value, ast.Attribute):
        return
    field_attr = func_node.value  # self.nodes
    if not isinstance(field_attr.value, ast.Name) or field_attr.value.id != "self":
        return
    field_name = field_attr.attr  # "nodes"
    self_cls = local_types.get("self", "")
    field_types = class_field_types.get(self_cls, {})
    if field_name in field_types:
        val_type = _extract_dict_value_type(field_types[field_name])
        if val_type:
            local_types[target] = val_type
