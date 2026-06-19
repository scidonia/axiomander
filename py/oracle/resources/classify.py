"""Contract classification for resource-aware lowering.

Phase 1: detect `owns(x)` predicates in contracts and classify as
pure_only or mixed_pure_resource.
"""

from __future__ import annotations
from enum import Enum
from typing import Optional
from ..contract_ir import ROwnExpr, Expr


class ContractClass(Enum):
    PURE_ONLY = "pure_only"
    MIXED_PURE_RESOURCE = "mixed_pure_resource"
    RESOURCE_ONLY = "resource_only"
    UNSUPPORTED_RESOURCE = "unsupported_resource"


def classify(lint_results: list) -> tuple[ContractClass, Optional[str]]:
    """Classify a function's contract by presence of resource predicates.

    Returns (classification, resource_var_name).

    pure_only:            no resource predicates (default)
    mixed_pure_resource:  owns(x) present alongside pure pre/post
    resource_only:        only owns(x), no pure side conditions
    unsupported_resource: owns(x) with unsupported modifiers
    """
    has_owns = False
    owned_var = None

    for r in lint_results:
        if r.lint_result and r.lint_result.ir:
            # Check if any ir node is an ROwnExpr
            def _find_own(ir: Expr) -> Optional[str]:
                if isinstance(ir, ROwnExpr):
                    return ir.obj
                if hasattr(ir, 'left'):
                    result = _find_own(ir.left)
                    if result: return result
                if hasattr(ir, 'right'):
                    result = _find_own(ir.right)
                    if result: return result
                if hasattr(ir, 'operands'):
                    for op in ir.operands:
                        result = _find_own(op)
                        if result: return result
                return None

            result = _find_own(r.lint_result.ir)
            if result:
                has_owns = True
                owned_var = result

    if not has_owns:
        return ContractClass.PURE_ONLY, None

    # Check for pure side conditions: any non-ROwnExpr in pre/post
    has_pure = False
    for r in lint_results:
        if r.lint_result and r.lint_result.ir:
            def _has_pure(ir: Expr) -> bool:
                if isinstance(ir, ROwnExpr):
                    return False  # resource-only
                return True
            if _has_pure(r.lint_result.ir):
                has_pure = True
                break

    if has_pure:
        return ContractClass.MIXED_PURE_RESOURCE, owned_var
    return ContractClass.RESOURCE_ONLY, owned_var
