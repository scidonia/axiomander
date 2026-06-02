"""
Shape IR — compiled representation of Pydantic model shapes.

Scans the source AST for BaseModel subclasses and builds a Shape
registry mapping class names to their field names, types, constraints,
and validate_assignment mode.

The registry is used by IsShape and IsValid contract IR nodes to expand
into Coq state predicates at codegen time.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class ShapeField:
    name: str
    coq_type: str
    constraints: list[str] = field(default_factory=list)


@dataclass
class Shape:
    name: str
    fields: list[ShapeField] = field(default_factory=list)
    validate_assignment: bool = False


_shape_registry: dict[str, Shape] = {}


def build_shape_registry(tree: ast.Module) -> dict[str, Shape]:
    _shape_registry.clear()
    for node in ast.walk(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        if not _inherits_base_model(node):
            continue
        shape = _build_shape(node)
        _shape_registry[node.name] = shape
    return _shape_registry


def lookup_shape(model_name: str) -> Optional[Shape]:
    return _shape_registry.get(model_name)


def is_shape_coq(obj_prefix: str, shape: Shape, scoped: bool = False) -> str:
    """Emit the Coq is_shape predicate.

    scoped=False (precondition): bare Z params are already typed — return True.
    scoped=True (postcondition): isVZ state lookups for every field.
    """
    if not scoped:
        return "True"
    guards = []
    for f in shape.fields:
        flat_key = f"{obj_prefix}_{f.name}"
        guard = _type_guard(f.coq_type, flat_key, scoped=True)
        if guard:
            guards.append(guard)
    return " /\\ ".join(f"({g})" for g in guards) if guards else "True"


def is_valid_coq(obj_prefix: str, shape: Shape, scoped: bool = False) -> str:
    parts = [is_shape_coq(obj_prefix, shape, scoped)]
    for f in shape.fields:
        flat_key = f"{obj_prefix}_{f.name}"
        key_scoped = f's "{flat_key}"%string'
        key_bare = flat_key
        for c in f.constraints:
            if scoped:
                parts.append(c.format(key_scoped=key_scoped, key_bare=key_bare))
            else:
                formatted = c.format(key_scoped=key_scoped, key_bare=key_bare)
                unscoped = formatted.replace(f"asZ ({key_scoped})", key_bare)
                parts.append(unscoped)
    return " /\\ ".join(f"({p})" for p in parts) if parts else "True"


def _type_guard(coq_type: str, flat_key: str, scoped: bool = False) -> str:
    key_ref = f's "{flat_key}"%string' if scoped else flat_key
    match coq_type:
        case "Z" | "bool":
            return f'isVZ ({key_ref}) = true'
        case "string":
            return f'isVString ({key_ref}) = true'
        case _:
            return f'isVZ ({key_ref}) = true'


def _inherits_base_model(node: ast.ClassDef) -> bool:
    for base in node.bases:
        if isinstance(base, ast.Name) and base.id == "BaseModel":
            return True
        if isinstance(base, ast.Attribute) and base.attr == "BaseModel":
            return True
    return False


def _build_shape(node: ast.ClassDef) -> Shape:
    fields: list[ShapeField] = []
    validate_assignment = _detect_validate_assignment(node)
    for stmt in node.body:
        if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
            field_name = stmt.target.id
            py_type = _python_type_name(stmt.annotation)
            coq_type = _py_to_coq(py_type)
            constraints = _extract_field_constraints(stmt)
            fields.append(ShapeField(
                name=field_name, coq_type=coq_type, constraints=constraints))
    return Shape(name=node.name, fields=fields, validate_assignment=validate_assignment)


def _detect_validate_assignment(node: ast.ClassDef) -> bool:
    for stmt in node.body:
        if isinstance(stmt, ast.Assign):
            targets = stmt.targets if isinstance(stmt.targets, list) else [stmt.targets]
            for target in targets:
                if isinstance(target, ast.Name) and target.id == "model_config":
                    val = stmt.value
                    if isinstance(val, ast.Call):
                        func_name = None
                        if isinstance(val.func, ast.Name):
                            func_name = val.func.id
                        elif isinstance(val.func, ast.Attribute):
                            func_name = val.func.attr
                        if func_name == "ConfigDict":
                            for kw in val.keywords:
                                if kw.arg == "validate_assignment" and isinstance(kw.value, ast.Constant):
                                    return bool(kw.value.value)
    return False


def _python_type_name(annotation) -> str:
    if annotation is None:
        return "int"
    if isinstance(annotation, ast.Name):
        return annotation.id
    if isinstance(annotation, ast.Attribute):
        return annotation.attr
    if isinstance(annotation, ast.Subscript):
        base = annotation.value
        if isinstance(base, ast.Name):
            return base.id
        if isinstance(base, ast.Attribute):
            return base.attr
    if isinstance(annotation, ast.BinOp) and isinstance(annotation.op, ast.BitOr):
        return _python_type_name(annotation.left)
    return "int"


def _py_to_coq(py_type: str) -> str:
    mapping = {"int": "Z", "str": "string", "float": "Z", "bool": "bool"}
    return mapping.get(py_type, "Z")


def _extract_field_constraints(stmt: ast.AnnAssign) -> list[str]:
    """Extract Field(ge=0, ...) constraints as Coq templates.

    Uses {key_scoped} for scoped state lookups and {key_bare} for bare Z vars.
    E.g. when scoped:   "0 <= asZ (s \"key\"%string)"
         when unscoped: "0 <= key"
    """
    constraints: list[str] = []
    if not isinstance(stmt.value, ast.Call):
        return constraints
    call = stmt.value
    is_field = False
    if isinstance(call.func, ast.Name) and call.func.id == "Field":
        is_field = True
    elif isinstance(call.func, ast.Attribute) and call.func.attr == "Field":
        is_field = True
    if not is_field:
        return constraints
    for kw in call.keywords:
        s = "{key_scoped}"
        b = "{key_bare}"
        if kw.arg == "ge" and isinstance(kw.value, ast.Constant):
            constraints.append(f"({kw.value.value} <= asZ ({s}))")
        elif kw.arg == "gt" and isinstance(kw.value, ast.Constant):
            constraints.append(f"({kw.value.value} < asZ ({s}))")
        elif kw.arg == "le" and isinstance(kw.value, ast.Constant):
            constraints.append(f"(asZ ({s}) <= {kw.value.value})")
        elif kw.arg == "lt" and isinstance(kw.value, ast.Constant):
            constraints.append(f"(asZ ({s}) < {kw.value.value})")
    return constraints
