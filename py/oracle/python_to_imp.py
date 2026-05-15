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


def python_to_imp(func_node: ast.FunctionDef, invariants: dict[int, str] | None = None, contract_map: dict[str, tuple[list[str], str, str]] | None = None) -> str:
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
    body = translator.translate_body(func_node.body)
    return body if body else "CSkip"


class ImpTranslator:
    """AST visitor that emits IMP commands as Coq strings."""

    def __init__(self):
        self._invariants: dict[int, str] = {}  # line → invariant string
        self._contract_map: dict[str, tuple[list[str], str, str]] = {}  # name → (params, pre, post)

    def translate_body(self, body: list[ast.stmt]) -> str:
        """Translate a list of statements into an IMP command sequence."""
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
            if name and name.endswith(".lower") and not value.args:
                obj = self._get_call_object(value)
                if obj:
                    loop_var = "_k"
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
                    loop_var = "_k"
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
                    l = "_l"; r = "_r"; i = "_i"
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
                return f"(ANum 0)"
            if isinstance(val, str):
                return f"(ANum {hash(val) % 10000})"
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
            idx = self.translate_expr(node.slice)
            return f'(AIndex "{name}"%string {idx})'

        if isinstance(node, ast.Dict):
            if not node.keys:
                return "CSkip"  # empty dict → no state change needed
            return f"(* non-empty dict literal *) CSkip"

        return f"(* unhandled: {type(node).__name__} *)"

    # ─── Private helpers ──────────────────────────────────────────

    def _translate_assign(self, stmt: ast.Assign) -> str:
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
            elif isinstance(value, ast.Dict) and not value.keys:
                return "CSkip"  # x = {} — empty dict
            elif isinstance(value, ast.Call):
                name = self._get_call_name(value)
                if name == "set" and not value.args:
                    return "CSkip"  # x = set() — empty set
                cc = self._translate_function_call(target, value)
                if cc:
                    return cc
                val = self.translate_expr(value)
                targets.append(f'(CAss "{target}"%string {val})')
            elif isinstance(value, ast.BoolOp):
                val = self.translate_expr(value)
                targets.append(f'(CAss "{target}"%string (ABool {val}))')
            elif isinstance(value, ast.Subscript) and isinstance(value.slice, ast.Slice):
                return self._translate_slice_copy(target, value)
            elif isinstance(value, ast.ListComp):
                return self._translate_list_comp(target, value)
            else:
                val = self.translate_expr(value)
                targets.append(f'(CAss "{target}"%string {val})')
        if len(targets) == 1:
            return targets[0]
        result = targets[-1]
        for cmd in reversed(targets[:-1]):
            result = f"(CSeq {cmd} {result})"
        return result

    def _translate_function_call(self, target: str, node: ast.Call) -> Optional[str]:
        name = self._get_call_name(node)
        if not name or name not in self._contract_map:
            return None
        callee_params, pre_coq, post_coq = self._contract_map[name]
        args_list = "(" + " :: ".join(self.translate_expr(a) for a in node.args) + " :: nil)" if node.args else "nil"
        # Bind caller args to callee param slots in the state
        bindings = []
        for i, arg in enumerate(node.args):
            arg_coq = self.translate_expr(arg)
            if i < len(callee_params):
                bindings.append(f'(CAss "{callee_params[i]}"%string {arg_coq})')
        # State-scope the precondition: bare callee params → state lookups
        pre_coq = self._scope_callee_params(pre_coq, callee_params)
        # In postcondition: callee's result → caller's target variable
        post_coq = self._subst_result(post_coq, target, callee_params)
        pre_str = f"(fun s => {pre_coq})"
        post_str = f"(fun s => {post_coq})"
        call = f'(CCall "{name}"%string {args_list} {pre_str} {post_str} "{target}"%string)'
        result = call
        for b in reversed(bindings):
            result = f"(CSeq {b} {result})"
        return result

    @staticmethod
    def _scope_callee_params(coq_expr: str, params: list[str]) -> str:
        """Replace bare callee param names with state lookups (capture-safe)."""
        import re
        result = coq_expr
        for p in params:
            # Replace `p` as a standalone word with `s "p"%string`
            result = re.sub(
                rf'(?<![a-zA-Z0-9_"%]){re.escape(p)}(?![a-zA-Z0-9_"%])',
                f's "{p}"%string', result
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
        loop_var = "_k"
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
        loop_var = "_k"
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
        loop_var = "_i"
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
        loop_var = "_k"
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
        loop_var = "_k"
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
        return f"(CIf {test} {then_body} {else_body})"

    def _translate_while(self, stmt: ast.While) -> str:
        test = self._truthify(stmt.test)
        body = self.translate_body(stmt.body)
        inv = "(fun _ => True)"
        return f"(CWhile {test} {inv} {body})"

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
        path = self._translate_target(stmt.iter) if isinstance(stmt.iter, (ast.Name, ast.Attribute)) else None
        if path:
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

        # General for-in (other Call or expr) — not yet supported
        return f"(* untranslated for-in: {ast.unparse(stmt)} *)"

    def _build_for_in_name(self, target: str, iter_name: str, stmt: ast.For) -> str:
        """Build a for-in-name loop: for x in name → while i<len(name): x=name[i]; body; i+=1"""
        start_val = "(ANum 0)"
        step_val = "(ANum 1)"
        loop_var = "_i"
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
        loop_var = "_i"
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
            inv = self._default_for_invariant(target, limit_val, start_val)

        init = f'(CAss "{target}"%string {start_val})'
        if step_is_neg:
            cond = f"(BNot (BLe (APlus (AVar \"{target}\"%string) {step_val}) {limit_val}))"
        else:
            cond = f"(BLe (APlus (AVar \"{target}\"%string) {step_val}) {limit_val})"
        loop_body = body_cmds if body_cmds == "CSkip" else f"(CSeq {body_cmds} {incr})"
        loop = f"(CWhile {cond} {inv} {loop_body})"
        return f"(CSeq {init} {loop})"

    def _default_for_invariant(self, target: str, limit_coq: str, start_coq: str) -> str:
        """Generate a default loop invariant from range bounds.
        Only generates for simple constant bounds; falls back to (fun _ => True).
        """
        import re
        # Only handle simple ANum or AVar bounds
        def simple_z(coq_str: str) -> str | None:
            m = re.match(r'\(ANum (-?\d+)\)', coq_str.strip())
            if m: return m.group(1)
            m = re.match(r'\(AVar "([^"]+)"%string\)', coq_str.strip())
            if m: return f's "{m.group(1)}"%string'
            return None
        start_z = simple_z(start_coq)
        limit_z = simple_z(limit_coq)
        if start_z and limit_z:
            return f'(fun s => {start_z} <= s "{target}"%string /\\ s "{target}"%string <= {limit_z})'
        return '(fun _ => True)'

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
            op = node.ops[0]
            if isinstance(op, (ast.In, ast.NotIn)):
                # dict name as a string var (not aexp)
                if isinstance(node.comparators[0], ast.Name):
                    right = f'"{node.comparators[0].id}"%string'
                else:
                    right = self._translate_target(node.comparators[0])
                    right = f'"{right}"%string'
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
            # x in dict → ADictLen dict x > 0
            return f"(BLe (ANum 1) (ADictLen {right} {left}))"
        if isinstance(op, ast.NotIn):
            # x not in dict → ADictLen dict x = 0
            return f"(BEq (ANum 0) (ADictLen {right} {left}))"
        if isinstance(op, ast.Lt):
            return f"(BLe (APlus {left} (ANum 1)) {right})"
        if isinstance(op, ast.Gt):
            return f"(BLe (APlus {right} (ANum 1)) {left})"
        if isinstance(op, ast.GtE):
            return f"(BLe {right} {left})"
        if isinstance(op, ast.NotEq):
            return f"(BNot (BEq {left} {right}))"
        op_map = {ast.Eq: "BEq", ast.LtE: "BLe"}
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
def _eval_const(node):
    import ast; v = ast.literal_eval(node); return v if isinstance(v, int) else None
