"""
WP Transformer: extracts contracts from annotated Python functions
and generates Coq proof obligations.

Parses Python source with the `ast` module, finds decorated functions,
extracts their contracts, and translates the body to IMP commands.
"""

import ast
import inspect
import textwrap
from typing import Any


def parse_python(source: str) -> ast.Module:
    """Parse Python source into an AST."""
    return ast.parse(source)


def get_decorated_functions(tree: ast.Module) -> list[ast.FunctionDef]:
    """Find top-level functions that have decorators."""
    return [
        node for node in ast.walk(tree)
        if isinstance(node, ast.FunctionDef) and len(node.decorator_list) > 0
    ]


def get_decorator_name(node: ast.expr) -> str | None:
    """Extract the name of a decorator, e.g. @requires → 'requires'."""
    if isinstance(node, ast.Call):
        return get_decorator_name(node.func)
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return None


def ast_to_python(node: ast.expr) -> str:
    """Convert an AST expression node back to Python-like Coq expression."""
    if isinstance(node, ast.Constant):
        val = node.value
        if isinstance(val, bool):
            return "true" if val else "false"
        if isinstance(val, int):
            return str(val)
        if val is True:
            return "true"
        if val is False:
            return "false"
        return str(val)
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.BinOp):
        left = ast_to_python(node.left)
        right = ast_to_python(node.right)
        op_map = {
            ast.Add: "Z.add",
            ast.Sub: "Z.sub",
            ast.Mult: "Z.mul",
            ast.FloorDiv: "Z.div",
            ast.Eq: "Z.eqb",
            ast.NotEq: "(fun a b => negb (Z.eqb a b))",
            ast.Lt: "Z.ltb",
            ast.LtE: "Z.leb",
            ast.Gt: "(fun a b => Z.ltb b a)",
            ast.GtE: "(fun a b => Z.leb b a)",
            ast.And: "andb",
            ast.Or: "orb",
            ast.BitAnd: "Z.land",
        }
        op = op_map.get(type(node.op), "Z.add")
        return f"({op} {left} {right})"
    if isinstance(node, ast.UnaryOp):
        operand = ast_to_python(node.operand)
        if isinstance(node.op, ast.USub):
            return f"(Z.opp {operand})"
        if isinstance(node.op, ast.Not):
            return f"(negb {operand})"
        return operand
    if isinstance(node, ast.Compare):
        left = ast_to_python(node.left)
        # Handle simple single-comparator cases
        if len(node.ops) == 1 and len(node.comparators) == 1:
            op = node.ops[0]
            right = ast_to_python(node.comparators[0])
            op_map = {
                ast.Eq: "Z.eqb",
                ast.NotEq: "(fun a b => negb (Z.eqb a b))",
                ast.Lt: "Z.ltb",
                ast.LtE: "Z.leb",
                ast.Gt: "(fun a b => Z.ltb b a)",
                ast.GtE: "(fun a b => Z.leb b a)",
            }
            op_name = op_map.get(type(op), "Z.eqb")
            return f"({op_name} {left} {right})"
        # Multi-comparator: a < b < c  →  andb (Z.ltb a b) (Z.ltb b c)
        parts = [left]
        parts_op = []
        for op, comp in zip(node.ops, node.comparators):
            parts.append(ast_to_python(comp))
            if isinstance(op, ast.Lt):
                parts_op.append("Z.ltb")
            elif isinstance(op, ast.LtE):
                parts_op.append("Z.leb")
            elif isinstance(op, ast.Gt):
                parts_op.append("(fun a b => Z.ltb b a)")
            elif isinstance(op, ast.GtE):
                parts_op.append("(fun a b => Z.leb b a)")
            elif isinstance(op, ast.Eq):
                parts_op.append("Z.eqb")
            else:
                parts_op.append("Z.eqb")

        comparisons = []
        for i, op_name in enumerate(parts_op):
            comparisons.append(f"({op_name} {parts[i]} {parts[i+1]})")
        return f"(andb {' (andb '.join(comparisons)}{')' * (len(comparisons) - 1)}" if comparisons else "true"
    if isinstance(node, ast.BoolOp):
        op_name = "andb" if isinstance(node.op, ast.And) else "orb"
        values = [ast_to_python(v) for v in node.values]
        result = values[0]
        for v in values[1:]:
            result = f"({op_name} {result} {v})"
        return result
    if isinstance(node, ast.IfExp):
        body = ast_to_python(node.body)
        orelse = ast_to_python(node.orelse)
        test = ast_to_python(node.test)
        return f"(if {test} then {body} else {orelse})"
    if isinstance(node, ast.Tuple):
        return "TODO_tuple"
    return f"(* untranslated: {type(node).__name__} *)"


def lambda_to_coq_predicate(node: ast.Lambda, result_var: str = "result") -> str:
    """Convert a Lambda AST node to a Coq predicate over args + result.

    Example: lambda a, b, result: result == a + b
    → fun a b result => Z.eqb result (Z.add a b) = true
    """
    args = [arg.arg for arg in node.args.args]
    body = ast_to_python(node.body)
    formatted_args = " ".join(args)
    return f"fun {formatted_args} => ({body} = true)%Z"


def lambda_to_requires_predicate(node: ast.Lambda) -> str:
    """Convert a precondition Lambda to a Coq predicate.

    Example: lambda n: n >= 0  →  fun n => Z.leb 0%Z n = true
    """
    return lambda_to_coq_predicate(node, result_var="")


def build_state_setup(params: list[str]) -> str:
    """Build initial state: map each parameter to its Coq value.

    Example: params = ["a", "b"] →
    upd (upd empty_state "a" a) "b" b
    """
    s = "empty_state"
    for p in params:
        s = f"upd ({s}) {p}%string {p}"
    return s


def generate_coq_obligation(func_node: ast.FunctionDef) -> str:
    """Generate a Coq theorem statement for a decorated function."""
    name = func_node.name
    params = [arg.arg for arg in func_node.args.args]

    decorators = {}
    for d in func_node.decorator_list:
        dname = get_decorator_name(d)
        if dname and isinstance(d, ast.Call) and len(d.args) > 0:
            if isinstance(d.args[0], ast.Lambda):
                decorators.setdefault(dname, []).append(d.args[0])

    requires_list = decorators.get("requires", [])
    ensures_list = decorators.get("ensures", [])

    if not ensures_list:
        return f"(* No @ensures on {name} — skipping *)"

    # Build requires predicate
    if requires_list:
        req_predicates = " /\ ".join(
            f"({lambda_to_requires_predicate(r)} {' '.join(p.arg for p in r.args.args)})"
            for r in requires_list
        )
    else:
        req_predicates = "True"

    # Simplify: for each param p, create a Coq variable p of type Z
    coq_params = " ".join(f"({p} : Z)" for p in params)

    # Postcondition uses 'result' as the return value
    ens = ensures_list[0]
    ens_pred = lambda_to_coq_predicate(ens)

    # Initial state
    init_state = build_state_setup(params)

    lines = [
        f"(* Auto-generated from {name} *)",
        f"Require Import Imp Wp.",
        f"Open Scope Z_scope.",
        f"",
        f"Theorem {name}_correct : forall {coq_params},",
        f"  {req_predicates} ->"
        f"  wp {name}_body (fun s => {ens_pred} {' '.join(params)} (s \"result\"%string)) ({init_state}).",
        f"Proof.",
        f"  (* TODO: fill with SMT or LLM-generated proof *)",
        f"Admitted.",
    ]

    return "\n".join(lines)


def extract_function_body(func_node: ast.FunctionDef) -> str:
    """Extract the function body as Coq IMP commands (basic translation)."""
    body = func_node.body
    lines = []
    for stmt in body:
        if isinstance(stmt, ast.Return):
            val = ast_to_python(stmt.value)
            lines.append(f'  "result"%string ::= ANum {val}')
        elif isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                if isinstance(target, ast.Name):
                    val = ast_to_python(stmt.value)
                    lines.append(f'  "{target.id}"%string ::= ANum {val}')
    return " ;;\n".join(lines) if lines else "CSkip"


def generate_coq_file(source: str) -> str:
    """Parse Python source and generate a Coq .v file with all obligations."""
    tree = parse_python(source)
    funcs = get_decorated_functions(tree)

    preamble = [
        "(* Generated WP obligations *)",
        'From Stdlib Require Import ZArith String List.',
        "Require Import Imp Wp.",
        "Import ListNotations.",
        "Open Scope Z_scope.",
        "",
    ]

    sections = []
    for func in funcs:
        name = func.name
        params = [arg.arg for arg in func.args.args]

        decorators = {}
        for d in func.decorator_list:
            dname = get_decorator_name(d)
            if dname and isinstance(d, ast.Call) and len(d.args) > 0:
                if isinstance(d.args[0], ast.Lambda):
                    decorators.setdefault(dname, []).append(d.args[0])

        requires_list = decorators.get("requires", [])
        ensures_list = decorators.get("ensures", [])
        invariants_list = decorators.get("invariants", [])

        if not ensures_list:
            continue

        # Build the IMP body
        body_com = extract_function_body(func)

        # Coq variable bindings
        coq_params = " ".join(f"({p} : Z)" for p in params)

        # Precondition
        if requires_list:
            parts = []
            for r in requires_list:
                r_args = " ".join(p.arg for p in r.args.args)
                r_body = ast_to_python(r.body)
                parts.append(f"fun {r_args} => ({r_body} = true)")
            if len(parts) == 1:
                req_body = parts[0]
            else:
                req_body = "(" + " /\\ ".join(parts) + ")"
            req_formal = " ".join(params)
        else:
            req_body = "True"
            req_formal = ""

        # Postcondition
        ens = ensures_list[0]
        ens_args = [p.arg for p in ens.args.args]
        ens_body = ast_to_python(ens.body)
        # The last arg is 'result', the rest are function params
        ens_params = " ".join(ens_args)

        init_state = build_state_setup(params)

        # Parameter application for precondition
        req_applied = " ".join(params)
        ens_applied = " ".join(ens_args[:-1] + ['(s "result"%string)'])

        sections.append(f"""(* ── {name} ── *)

Definition {name}_body : com :=
  {body_com}.

Theorem {name}_correct : forall {coq_params},
  ({req_body} {req_applied}) ->
  wp {name}_body
    (fun s => ({ens_body} {ens_applied} = true))
    ({init_state}).
Proof.
  (* SMT or LLM-generated proof *)
Admitted.
""")

    result = "\n".join(preamble + sections)
    return result


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as f:
            source = f.read()
        print(generate_coq_file(source))
    else:
        print("Usage: python wp_transformer.py <python_file>")
