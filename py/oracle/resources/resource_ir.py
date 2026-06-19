"""Tiny Resource IR for the Iris backend prototype.

Phase 2 models: ownership (ROwn), field points-to (RField),
pure assertions (RPure), separating conjunction (RSep).
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Union, Optional
from ..contract_ir import Expr


@dataclass
class ROwn:
    """Ownership marker: owns(box) → ROwn(var="box")."""
    var: str


@dataclass
class RField:
    """Points-to: box.value ↦ v.  Flat-key encoding for one field."""
    obj: str        # "box"
    field: str      # "value"
    value: str      # variable name or literal, e.g. "old_box_value" or "n+1"


@dataclass
class RPure:
    """A pure (non-resource) assertion, e.g. old_box_value >= 0."""
    expr: Expr


@dataclass
class RSep:
    """Separating conjunction: P ∗ Q."""
    left: "RAssert"
    right: "RAssert"


RAssert = Union[ROwn, RField, RPure, RSep]


def infer_resource_footprint(
    owned_var: str,
    modifies: list[str],
    pre_pure_exprs: list[Expr],
) -> Optional[RAssert]:
    """Infer a resource precondition from owns(x) + modifies: {fields}.

    For the prototype, supports exactly one field.
    Returns the resource precondition as an RSep tree or None if inference fails.

    Example:
      owns(box), modifies: box.value, pure: box.value >= 0
      → RSep(RField("box", "value", "old_box_value"), RPure(box.value >= 0))
    """
    if not modifies:
        # owns(x) with no modifies is only valid if the function doesn't
        # write to any field (pure reader).  Return ownership alone.
        return ROwn(var=owned_var)

    # For each modifies field, create a RField entry
    fields: list[RAssert] = []
    for mod in modifies:
        if "." in mod:
            obj, field = mod.split(".", 1)
            if obj == owned_var:
                # Use old-value convention: old_box_value represents the pre-state value
                old_val = f"old_{obj}_{field}"
                fields.append(RField(obj=obj, field=field, value=old_val))
            else:
                return None  # modifies field of non-owned object
        else:
            return None  # modifies must be dotted field name

    # Build separating conjunction: fields ∗ pure_conditions
    result: RAssert = fields[0]
    for f in fields[1:]:
        result = RSep(left=result, right=f)

    for pure in pre_pure_exprs:
        result = RSep(left=result, right=RPure(expr=pure))

    return result


def format_resource_json(
    func_name: str,
    classification: str,
    footprint: Optional[RAssert],
    commands: list[str],
    pure_conditions: list[str],
) -> dict:
    """Emit the resource obligation as a JSON-like dict (Phase 7 format)."""
    pre: dict = {"pure": []}
    if isinstance(footprint, RSep):
        # Walk the separating conjunction tree
        def _walk(r: RAssert):
            if isinstance(r, RField):
                pre["field"] = [r.obj, r.field, r.value]
            elif isinstance(r, RPure):
                pre["pure"].append(str(r.expr))
            elif isinstance(r, RSep):
                _walk(r.left)
                _walk(r.right)

        _walk(footprint)
    elif isinstance(footprint, RField):
        pre["field"] = [footprint.obj, footprint.field, footprint.value]
    elif isinstance(footprint, ROwn):
        pre["field"] = [footprint.var, "(none)", "(none)"]

    return {
        "kind": "resource_wp_obligation",
        "function": func_name,
        "classification": classification,
        "resource_model": "owned_field_v0",
        "pre": pre,
        "program": commands,
        "post": {
            "field": pre.get("field", []),
            "pure": [str(c) for c in pure_conditions],
        },
        "pure_side_conditions": [str(c) for c in pure_conditions],
    }
