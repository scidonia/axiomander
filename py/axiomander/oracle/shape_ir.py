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
import os
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class ShapeField:
    name: str
    coq_type: str                          # Coq type: "Z", "string", "bool"
    py_type: str = ""                      # Original Python type name e.g. "int", "Address"
    constraints: list[str] = field(default_factory=list)


@dataclass
class Shape:
    name: str
    fields: list[ShapeField] = field(default_factory=list)
    validate_assignment: bool = False


def _escape_field(name: str) -> str:
    """Escape literal underscores in a field name as double underscores.

    This makes the single underscore an unambiguous obj→field separator
    in flat keys like 'account_balance'.  A user field named 'max_value'
    becomes 'max__value' so the flat key 'account_max__value' cannot be
    confused with a bare parameter named 'account_max_value'.

    axiomander:
        requires:
            len(name) >= 0
        ensures:
            implies(re_match(name, ".*_.*"), re_match(result, ".*__.*"))
            implies(not re_match(name, ".*_.*"), result == name)
    """
    return name.replace("_", "__")


_shape_registry: dict[str, Shape] = {}
_enum_registry: dict[str, dict[str, int]] = {}  # e.g. ProofLevel → {"UNPROVED": 0, ...}


def build_shape_registry(tree: ast.Module, _cwd: str = ".") -> dict[str, Shape]:
    """Build the shape/enum registry from [tree] AND its imported modules.

    Walks the AST for Pydantic/dataclass shapes and enum definitions.
    Also follows relative imports (e.g. `from external_db import ...`)
    to parse the imported module's shapes/enums into the same registry,
    so enum member refs resolve across file boundaries."""
    _shape_registry.clear()
    _enum_registry.clear()

    def _scan(node: ast.Module) -> None:
        for stmt in ast.walk(node):
            if isinstance(stmt, ast.ClassDef):
                if _inherits_base_model(stmt) or _is_dataclass(stmt):
                    _shape_registry[stmt.name] = _build_shape(stmt)
                elif _is_enum(stmt):
                    _enum_registry[stmt.name] = _build_enum_values(stmt)

    _scan(tree)

    # Follow relative imports to pick up enums from other files.
    _visited: set[str] = set()
    for stmt in ast.walk(tree):
        if isinstance(stmt, ast.ImportFrom) and stmt.module:
            module = stmt.module
            if module in _visited:
                continue
            import_path = os.path.join(_cwd, f"{module}.py")
            alt_path = os.path.join(_cwd, f"{module.replace('.', '/')}.py")
            for path in (import_path, alt_path):
                try:
                    with open(path) as f:
                        mod_tree = ast.parse(f.read())
                    _scan(mod_tree)
                    _visited.add(module)
                    break
                except (OSError, SyntaxError):
                    continue

    return _shape_registry


def lookup_enum_value(enum_name: str, member_name: str) -> int | None:
    """Return the integer encoding of an enum member, or None."""
    members = _enum_registry.get(enum_name)
    if members is None:
        return None
    return members.get(member_name)


_ENUM_BASES = frozenset({"Enum", "IntEnum", "IntFlag", "StrEnum"})


def _is_enum(node: ast.ClassDef) -> bool:
    """Check if a ClassDef inherits from Enum / IntEnum / etc.

    Recognises the standard-library enum bases (used by Pydantic models for
    enum-typed fields): Enum, IntEnum, IntFlag, StrEnum.  Matched by base
    name whether referenced bare (IntEnum) or qualified (enum.IntEnum)."""
    for base in node.bases:
        if isinstance(base, ast.Name) and base.id in _ENUM_BASES:
            return True
        if isinstance(base, ast.Attribute) and base.attr in _ENUM_BASES:
            return True
    return False


def _build_enum_values(node: ast.ClassDef) -> dict[str, int]:
    """Build {member_name: integer_encoding} for an enum class.

    If every member has an explicit integer value (the IntEnum idiom,
    e.g. READY = 0), those values are used directly.  Otherwise the
    encoding is 0-based by declaration order in the AST body.
    """
    values: dict[str, int] = {}
    idx = 0
    all_explicit = True
    pending: list[str] = []
    for stmt in node.body:
        if isinstance(stmt, ast.Assign):
            for target in (stmt.targets if isinstance(stmt.targets, list)
                           else [stmt.targets]):
                if isinstance(target, ast.Name):
                    pending.append(target.id)
                    val = stmt.value
                    if (isinstance(val, ast.Constant)
                            and isinstance(val.value, int)
                            and not isinstance(val.value, bool)):
                        values[target.id] = val.value
                    else:
                        all_explicit = False
                    idx += 1
    if not all_explicit or len(values) != len(pending):
        # Fall back to 0-based declaration order.
        values = {name: i for i, name in enumerate(pending)}
    return values


def lookup_shape(model_name: str) -> Optional[Shape]:
    return _shape_registry.get(model_name)


def is_shape_coq(obj_prefix: str, shape: Shape, scoped: bool = False) -> str:
    """isVZ/isVString type guards for every leaf field, including nested models."""
    if not scoped:
        return "True"
    guards = []
    for flat_key, f in flat_fields(shape, obj_prefix):
        guard = _type_guard(f.coq_type, flat_key, scoped=True)
        if guard:
            guards.append(guard)
    return " /\\ ".join(f"({g})" for g in guards) if guards else "True"


def is_valid_coq(obj_prefix: str, shape: Shape, scoped: bool = False) -> str:
    """is_shape + all Field constraints for every leaf field."""
    parts = [is_shape_coq(obj_prefix, shape, scoped)]
    for flat_key, f in flat_fields(shape, obj_prefix):
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


def flat_fields(
    shape: Shape,
    obj_prefix: str,
    visited: frozenset[str] | None = None,
) -> list[tuple[str, ShapeField]]:
    """Return (flat_key, ShapeField) pairs for all leaf fields of a shape.

    Nested model fields are expanded with a compound prefix, e.g.:
      User.address: Address  →  user_address__postcode  (Address.postcode)

    Cycle detection via `visited` prevents infinite recursion for types like
      Node(left: Node, right: Node) — such fields are treated as opaque Z leaves.

    axiomander:
        requires:
            is_shape(shape, Shape)
            len(obj_prefix) > 0
        ensures:
            all(key.startswith(obj_prefix + "_") for key, _ in result)
            implies(shape.name in (visited or frozenset()), result == [])
            all(is_shape(sf, ShapeField) for _, sf in result)
    """
    if visited is None:
        visited = frozenset()
    if shape.name in visited:
        # Cycle — treat the whole shape as an opaque Z leaf
        return []
    visited = visited | {shape.name}
    result: list[tuple[str, ShapeField]] = []
    for f in shape.fields:
        flat_key = f"{obj_prefix}_{_escape_field(f.name)}"
        nested = _shape_registry.get(f.py_type) if f.py_type else None
        if nested and f.py_type not in visited:
            # Recurse into nested model
            result.extend(flat_fields(nested, flat_key, visited))
        else:
            result.append((flat_key, f))
    return result


def _inherits_base_model(node: ast.ClassDef) -> bool:
    for base in node.bases:
        if isinstance(base, ast.Name) and base.id == "BaseModel":
            return True
        if isinstance(base, ast.Attribute) and base.attr == "BaseModel":
            return True
    return False


def _is_dataclass(node: ast.ClassDef) -> bool:
    """Check if a ClassDef has a @dataclass decorator."""
    for dec in node.decorator_list:
        if isinstance(dec, ast.Name) and dec.id == "dataclass":
            return True
        if isinstance(dec, ast.Call) and isinstance(dec.func, ast.Name) and dec.func.id == "dataclass":
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
                name=field_name,
                coq_type=coq_type,
                py_type=py_type,
                constraints=constraints,
            ))
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
