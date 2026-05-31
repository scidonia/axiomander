"""Dump proof obligations to .v files without running verification."""
import sys
import ast
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from oracle.mcp_server import (
    _verify_function, _generate_coq, _gen_imp_body, _build_contract_map,
    ContractLinter, _classify_assert, _infer_var_types, _func_params,
    _expand_params, _collect_predicates, _detect_ghost_vars,
)


def dump_obligations(source: str, func_name: str, outdir: str) -> str:
    """Generate .v file for a function, save it, return path."""
    tree = ast.parse(source)
    func_node = next(
        n for n in ast.walk(tree)
        if isinstance(n, ast.FunctionDef) and n.name == func_name
    )

    params = [name for name, _ in _func_params(func_node)]
    expanded, class_fields, _, _, _ = _expand_params(tree, params, func_node)
    ghost_vars = _detect_ghost_vars(func_node)
    ghost_var_names = frozenset(ghost_vars.keys())
    predicates = _collect_predicates(tree)
    var_types = _infer_var_types(func_node)

    linter_pre = ContractLinter(expanded, "precondition", predicates=predicates,
                                unbound=ghost_var_names)
    linter_post = ContractLinter(expanded, "postcondition", predicates=predicates,
                                 unbound=ghost_var_names)
    linter_pre.var_types = var_types
    linter_post.var_types = var_types

    lint_results = []
    for stmt in ast.walk(func_node):
        if isinstance(stmt, ast.Assert):
            cls = _classify_assert(func_node, stmt)
            linter = linter_pre if cls == "precondition" else linter_post
            lr = linter.lint_expression(stmt.test)
            from oracle.mcp_server import AssertInfo
            lint_results.append(AssertInfo(
                node=stmt, lineno=stmt.lineno, col_offset=stmt.col_offset,
                classification=cls, lint_result=lr,
            ))

    imp_body, imp_ir = _gen_imp_body(tree, func_node,
                                      contract_map=_build_contract_map(tree))
    coq = _generate_coq(func_node, lint_results, imp_body, tree, None,
                         ghost_vars=ghost_vars, imp_ir=imp_ir)

    outpath = Path(outdir) / f"{func_name}.v"
    outpath.parent.mkdir(parents=True, exist_ok=True)
    outpath.write_text(coq)
    return str(outpath)


if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser(description="Dump Coq proof obligations")
    p.add_argument("file", help="Python source file")
    p.add_argument("function", nargs="?", help="Function name (default: all)")
    p.add_argument("-o", "--outdir", default="/tmp/axiomander_obligations",
                   help="Output directory")
    args = p.parse_args()

    source = Path(args.file).read_text()
    tree = ast.parse(source)
    funcs = [n.name for n in ast.walk(tree)
             if isinstance(n, ast.FunctionDef)]

    if args.function:
        funcs = [f for f in funcs if f == args.function]
        if not funcs:
            print(f"Function '{args.function}' not found")
            sys.exit(1)

    for fn in funcs:
        path = dump_obligations(source, fn, args.outdir)
        size = Path(path).stat().st_size
        print(f"{fn}: {size} bytes -> {path}")
