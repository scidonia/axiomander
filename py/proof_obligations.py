"""
Semi-Automatic Proof Obligation Generator

Pipeline:
  1. Parse annotated Python → extract contracts
  2. Generate Coq theorem statements
  3. Apply Level 1 automation (WpTactics) to trivial goals
  4. Send remaining goals to SMT hammer
  5. Send still-unproven goals to LLM oracle

Usage:
    python proof_obligations.py py/examples/demo.py

Output: a Coq .v file with theorems and filled-in proofs
where possible, Admitted where automation fails.
"""

import ast
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from py.wp_transformer import (
    parse_python,
    get_decorated_functions,
    get_decorator_name,
    ast_to_coq_expr,
    build_coq_body,
)


@dataclass
class Obligation:
    """A single proof obligation extracted from a Python function."""
    func_name: str
    params: list[str]
    pre: Optional[str]       # Coq expression for precondition
    post: str                # Coq expression for postcondition
    body: str                # Coq IMP command
    init_state: str          # Coq state initializer

    def to_coq_theorem(self) -> str:
        """Generate the Coq theorem statement."""
        params_str = " ".join(f"({p} : Z)" for p in self.params)
        pre_str = self.pre or "True"
        return f"""Theorem {self.func_name}_correct : forall {params_str},
  {pre_str} ->
  wp {self.func_name}_body
     (fun s => {self.post})
     ({self.init_state}).
"""


def extract_obligations(source: str) -> list[Obligation]:
    """Extract all proof obligations from annotated Python source."""
    tree = parse_python(source)
    funcs = get_decorated_functions(tree)
    obligations = []

    for func in funcs:
        params = [arg.arg for arg in func.args.args]

        decorators = {}
        for d in func.decorator_list:
            dname = get_decorator_name(d)
            if dname and isinstance(d, ast.Call) and d.args:
                decorators.setdefault(dname, []).append(d.args[0])

        if "ensures" not in decorators:
            continue

        pre = None
        if "requires" in decorators:
            pre_lambdas = decorators["requires"]
            # Take the first @requires for now
            pre = ast_to_coq_expr(pre_lambdas[0].body)

        post_lambda = decorators["ensures"][0]
        post = ast_to_coq_expr(post_lambda.body)

        body = build_coq_body(func)

        # Build initial state from params
        parts = []
        for p in params:
            parts.append(f'("{p}"%string, {p})')
        init = "empty_state" if not parts else (
            "upd (" * len(parts) + "empty_state"
            + "".join(f' "{p}"%string {p})' for p in params)
        )

        obligations.append(Obligation(
            func_name=func.name,
            params=params,
            pre=pre,
            post=post,
            body=body,
            init_state=init,
        ))

    return obligations


# ─── Pipeline stages ──────────────────────────────────────────────

def stage1_generate_coq(obligations: list[Obligation]) -> str:
    """Generate the Coq .v file with all theorem statements."""
    lines = [
        "(* Generated proof obligations *)",
        'From Stdlib Require Import ZArith String List Lia.',
        "Require Import Imp Wp WpTactics.",
        "Import ListNotations.",
        "Open Scope Z_scope.",
        "",
    ]

    for obl in obligations:
        lines.append(f"(* ── {obl.func_name} ── *)")
        lines.append(f"")
        lines.append(f"Definition {obl.func_name}_body : com :=")
        lines.append(f"  {obl.body}.")
        lines.append(f"")
        lines.append(obl.to_coq_theorem())

        # Level 1: try wp_prove
        lines.append("Proof.")
        lines.append(f"  intros. wp_prove {obl.func_name}_body.")
        lines.append("  (* If the goal still remains, try SMT hammer *)")
        lines.append("  Restart. intros.")
        lines.append(f"  (* hammer.  (* uncomment when coq-hammer is installed *) *)")
        lines.append("  (* If hammer fails, try LLM oracle *)")
        lines.append("  (* llm_oracle. *)")
        lines.append("Admitted.")
        lines.append("")

    return "\n".join(lines)


def stage2_smt_hammer(coq_file: Path) -> str:
    """Run coq-hammer on the generated file. Returns log output."""
    try:
        result = subprocess.run(
            ["coqc", "-Q", ".", "Imp", str(coq_file)],
            capture_output=True, text=True, timeout=30,
        )
        return result.stdout + result.stderr
    except Exception as e:
        return str(e)


def stage3_llm_oracle(goal: str, context: str) -> Optional[str]:
    """Send a goal to the LLM for proof generation.

    Black hole: the LLM API call.
    Recovery: validate the returned proof with coqc.

    Returns: Coq proof script if valid, None otherwise.
    """
    # Placeholder — wired up when the LLM client is built
    _ = goal, context
    return None


# ─── Main ─────────────────────────────────────────────────────────

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python proof_obligations.py <python_file>")
        sys.exit(1)

    source = Path(sys.argv[1]).read_text()
    obligations = extract_obligations(source)

    coq_code = stage1_generate_coq(obligations)
    print(coq_code)
