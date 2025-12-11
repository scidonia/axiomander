"""
SMT (Z3) translator for Python expressions.

This module translates Python AST expressions to Z3 formulas for
formal verification. Supports basic arithmetic, comparisons, boolean logic,
and function calls with type inference from annotations.
"""

import ast
from typing import Dict, List, Optional, Any, Union, Set, Tuple
from dataclasses import dataclass
from enum import Enum

try:
    import z3

    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False
    z3 = None  # Will raise AttributeError on access


class TranslationError(Exception):
    """Raised when translation to Z3 fails."""

    pass


class UnsupportedConstructError(TranslationError):
    """Raised when AST construct cannot be translated."""

    pass


class TypeInferenceError(TranslationError):
    """Raised when type cannot be inferred."""

    pass


class VariableType(Enum):
    """Supported variable types for Z3 translation."""

    INT = "int"
    REAL = "real"
    BOOL = "bool"
    STRING = "string"
    LIST = "list"
    UNKNOWN = "unknown"

    # Optional types for None support
    OPTIONAL_INT = "optional_int"
    OPTIONAL_REAL = "optional_real"
    OPTIONAL_BOOL = "optional_bool"
    OPTIONAL_STRING = "optional_string"


@dataclass
class Z3Variable:
    """Represents a variable in Z3 context."""

    name: str
    z3_var: z3.ExprRef
    var_type: VariableType
    python_name: str


class SMTTranslator:
    """Translates Python expressions to Z3 formulas."""

    # Pure built-in functions we can translate
    PURE_BUILTINS = {
        "abs": lambda x: z3.If(x >= 0, x, -x),
        "min": lambda x, y: z3.If(x <= y, x, y),
        "max": lambda x, y: z3.If(x >= y, x, y),
        "len": None,  # Special handling required
        "bool": lambda x: x != 0,  # For numeric types
    }

    def __init__(self):
        self.solver = z3.Solver()
        self.variables: Dict[str, Z3Variable] = {}
        self.type_hints: Dict[str, VariableType] = {}
        self.unsupported_constructs: List[str] = []

        # Track variable counter for unique names
        self._var_counter = 0

        # Initialize Z3 optional datatypes
        self._init_optional_datatypes()

    def reset(self):
        """Reset the translator state."""
        self.solver.reset()
        self.variables.clear()
        self.type_hints.clear()
        self.unsupported_constructs.clear()
        self._var_counter = 0

        # Reinitialize datatypes after reset
        self._init_optional_datatypes()

    def _init_optional_datatypes(self):
        """Initialize Z3 optional datatypes for None support according to DATATYPES_SPEC.md."""
        if not Z3_AVAILABLE:
            return

        # Create optional datatype for integers (following spec pattern)
        self.OptionInt = z3.Datatype("OptionInt")
        self.OptionInt.declare("None")  # represents Python None
        self.OptionInt.declare("Some", ("value", z3.IntSort()))
        self.OptionInt = self.OptionInt.create()

        # Store references for convenience (following spec naming)
        self.NoneInt = getattr(self.OptionInt, "None")
        self.SomeInt = self.OptionInt.Some
        self.valInt = self.OptionInt.value  # projector

        # Create optional datatype for reals
        self.OptionReal = z3.Datatype("OptionReal")
        self.OptionReal.declare("None")
        self.OptionReal.declare("Some", ("value", z3.RealSort()))
        self.OptionReal = self.OptionReal.create()

        self.NoneReal = getattr(self.OptionReal, "None")
        self.SomeReal = self.OptionReal.Some
        self.valReal = self.OptionReal.value

        # Create optional datatype for booleans
        self.OptionBool = z3.Datatype("OptionBool")
        self.OptionBool.declare("None")
        self.OptionBool.declare("Some", ("value", z3.BoolSort()))
        self.OptionBool = self.OptionBool.create()

        self.NoneBool = getattr(self.OptionBool, "None")
        self.SomeBool = self.OptionBool.Some
        self.valBool = self.OptionBool.value

        # Create optional datatype for strings
        self.OptionString = z3.Datatype("OptionString")
        self.OptionString.declare("None")
        self.OptionString.declare("Some", ("value", z3.StringSort()))
        self.OptionString = self.OptionString.create()

        self.NoneString = getattr(self.OptionString, "None")
        self.SomeString = self.OptionString.Some
        self.valString = self.OptionString.value

    def _get_none_value(self, var_type: VariableType):
        """Get the None value for a given optional type (following DATATYPES_SPEC.md)."""
        if var_type == VariableType.OPTIONAL_INT:
            return self.NoneInt
        elif var_type == VariableType.OPTIONAL_REAL:
            return self.NoneReal
        elif var_type == VariableType.OPTIONAL_BOOL:
            return self.NoneBool
        elif var_type == VariableType.OPTIONAL_STRING:
            return self.NoneString
        else:
            raise UnsupportedConstructError(f"No None value for type: {var_type}")

    def _create_some_value(self, value, var_type: VariableType):
        """Create a Some(value) for a given optional type (following DATATYPES_SPEC.md)."""
        if var_type == VariableType.OPTIONAL_INT:
            return self.SomeInt(value)
        elif var_type == VariableType.OPTIONAL_REAL:
            return self.SomeReal(value)
        elif var_type == VariableType.OPTIONAL_BOOL:
            return self.SomeBool(value)
        elif var_type == VariableType.OPTIONAL_STRING:
            return self.SomeString(value)
        else:
            raise UnsupportedConstructError(f"No Some constructor for type: {var_type}")

    def _is_none_check(self, var_expr, var_type: VariableType):
        """Create 'is None' check using equality (following DATATYPES_SPEC.md section 3.3)."""
        # Spec says: "x is None" → "x == OptionT.None"
        none_value = self._get_none_value(var_type)
        return var_expr == none_value

    def _handle_is_comparison(self, left_expr, right_expr, is_equal: bool):
        """Handle 'x is None' and 'x is not None' comparisons."""
        # Check if comparing with None literal
        if (isinstance(right_expr, ast.Constant) and right_expr.value is None) or (
            isinstance(right_expr, ast.NameConstant) and right_expr.value is None
        ):
            # Get variable name and infer it should be optional
            if isinstance(left_expr, ast.Name):
                var_name = left_expr.id

                # Try to infer the base type from existing hints or default to INT
                base_type = self.type_hints.get(var_name, VariableType.INT)

                # Handle already optional types
                if base_type in [
                    VariableType.OPTIONAL_INT,
                    VariableType.OPTIONAL_REAL,
                    VariableType.OPTIONAL_BOOL,
                    VariableType.OPTIONAL_STRING,
                ]:
                    optional_type = base_type
                elif base_type in [
                    VariableType.INT,
                    VariableType.REAL,
                    VariableType.BOOL,
                    VariableType.STRING,
                ]:
                    # Convert to optional type
                    if base_type == VariableType.INT:
                        optional_type = VariableType.OPTIONAL_INT
                    elif base_type == VariableType.REAL:
                        optional_type = VariableType.OPTIONAL_REAL
                    elif base_type == VariableType.BOOL:
                        optional_type = VariableType.OPTIONAL_BOOL
                    else:  # STRING
                        optional_type = VariableType.OPTIONAL_STRING
                else:
                    # Default to optional int for unknown types
                    optional_type = VariableType.OPTIONAL_INT

                # Create or get the optional variable
                var = self.get_or_create_variable(var_name, optional_type)

                # Return appropriate None check
                if is_equal:  # x is None
                    return self._is_none_check(var.z3_var, optional_type)
                else:  # x is not None
                    return z3.Not(self._is_none_check(var.z3_var, optional_type))

        # Fallback for non-None comparisons
        raise UnsupportedConstructError(f"Unsupported 'is' comparison")

    def _handle_membership_testing(self, left_expr, right_expr, is_in: bool):
        """Handle 'x in [1, 2, 3]' membership testing."""
        # This method receives the translated Z3 expressions
        # We need to handle the AST level in the comparison handler
        raise UnsupportedConstructError(
            "Use _handle_membership_testing_ast for AST-level handling"
        )

    def _handle_membership_testing_ast(self, left_expr, right_expr, is_in: bool):
        """Handle 'x in [1, 2, 3]' membership testing at AST level."""
        # Check if right side is a literal list
        if isinstance(right_expr, ast.List):
            # Get the left side Z3 variable
            left_z3 = self._translate_expr(left_expr)

            # Create disjunction/conjunction for each list element
            conditions = []
            for element in right_expr.elts:
                element_z3 = self._translate_expr(element)
                conditions.append(left_z3 == element_z3)

            if not conditions:
                # Empty list case
                return z3.BoolVal(
                    not is_in
                )  # x in [] is always False, x not in [] is always True
            elif len(conditions) == 1:
                # Single element
                result = conditions[0]
            else:
                # Multiple elements: x in [a, b, c] -> (x == a) OR (x == b) OR (x == c)
                result = z3.Or(*conditions)

            # Return result or its negation
            return result if is_in else z3.Not(result)
        else:
            # For non-literal containers, we can't handle yet
            raise UnsupportedConstructError(
                "Membership testing only supported for literal lists"
            )

    def _detect_none_usage(self, func_def: ast.FunctionDef) -> set:
        """Detect variables that might be None based on usage patterns."""
        none_variables = set()

        for node in ast.walk(func_def):
            # Check for 'x is None' and 'x is not None' patterns
            if isinstance(node, ast.Compare):
                for op, comparator in zip(node.ops, node.comparators):
                    if isinstance(op, (ast.Is, ast.IsNot)):
                        # Check if comparing with None
                        if (
                            isinstance(comparator, ast.Constant)
                            and comparator.value is None
                        ) or (
                            isinstance(comparator, ast.NameConstant)
                            and comparator.value is None
                        ):
                            # Add the left side variable to none_variables
                            if isinstance(node.left, ast.Name):
                                none_variables.add(node.left.id)

            # Check for assignments to None: x = None
            elif isinstance(node, ast.Assign):
                if (
                    isinstance(node.value, ast.Constant) and node.value.value is None
                ) or (
                    isinstance(node.value, ast.NameConstant)
                    and node.value.value is None
                ):
                    for target in node.targets:
                        if isinstance(target, ast.Name):
                            none_variables.add(target.id)

        return none_variables

    def _detect_regular_usage(self, func_def: ast.FunctionDef) -> set:
        """Detect variables used in regular (non-None) operations like math, comparisons."""
        regular_vars = set()

        for node in ast.walk(func_def):
            # Math operations: x + 1, x * y, etc.
            if isinstance(node, ast.BinOp):
                if isinstance(node.left, ast.Name):
                    regular_vars.add(node.left.id)
                if isinstance(node.right, ast.Name):
                    regular_vars.add(node.right.id)

            # Comparisons (except None checks): x > 0, a >= b, etc.
            elif isinstance(node, ast.Compare):
                # Skip None comparisons
                is_none_comparison = False
                for op, comparator in zip(node.ops, node.comparators):
                    if isinstance(op, (ast.Is, ast.IsNot)) and (
                        (
                            isinstance(comparator, ast.Constant)
                            and comparator.value is None
                        )
                        or (
                            isinstance(comparator, ast.NameConstant)
                            and comparator.value is None
                        )
                    ):
                        is_none_comparison = True
                        break

                if not is_none_comparison:
                    # Regular comparison - add variables
                    if isinstance(node.left, ast.Name):
                        regular_vars.add(node.left.id)
                    for comparator in node.comparators:
                        if isinstance(comparator, ast.Name):
                            regular_vars.add(comparator.id)

        return regular_vars

    def _make_optional_type(self, base_type: VariableType) -> VariableType:
        """Convert a base type to its optional equivalent."""
        if base_type == VariableType.INT:
            return VariableType.OPTIONAL_INT
        elif base_type == VariableType.REAL:
            return VariableType.OPTIONAL_REAL
        elif base_type == VariableType.BOOL:
            return VariableType.OPTIONAL_BOOL
        elif base_type == VariableType.STRING:
            return VariableType.OPTIONAL_STRING
        else:
            # For unknown types, default to optional int
            return VariableType.OPTIONAL_INT

    def add_type_hint(self, var_name: str, var_type: VariableType):
        """Add a type hint for a variable."""
        self.type_hints[var_name] = var_type

    def add_type_hints_from_function(self, func_def: ast.FunctionDef):
        """Extract type hints from function definition and infer additional types."""
        # First, extract explicit type annotations
        for arg in func_def.args.args:
            if arg.annotation:
                python_type = self._extract_type_from_annotation(arg.annotation)
                if python_type:
                    self.type_hints[arg.arg] = python_type

        # Add return type hint if available
        if func_def.returns:
            ret_type = self._extract_type_from_annotation(func_def.returns)
            if ret_type:
                self.type_hints["__return__"] = ret_type

        # Now use simple type inference to infer additional types
        try:
            self._infer_types_from_function(func_def)
        except Exception as e:
            # Type inference failed, but don't let it break the whole process
            import logging

            logger = logging.getLogger(__name__)
            logger.debug(f"Type inference failed: {e}")

    def _extract_type_from_annotation(
        self, annotation: ast.expr
    ) -> Optional[VariableType]:
        """Extract VariableType from Python type annotation."""
        if isinstance(annotation, ast.Name):
            type_name = annotation.id
            type_mapping = {
                "int": VariableType.INT,
                "float": VariableType.REAL,
                "bool": VariableType.BOOL,
                "str": VariableType.STRING,
                "list": VariableType.LIST,
            }
            return type_mapping.get(type_name)
        elif isinstance(annotation, ast.Constant):
            # Handle string annotations like "int"
            if isinstance(annotation.value, str):
                type_mapping = {
                    "int": VariableType.INT,
                    "float": VariableType.REAL,
                    "bool": VariableType.BOOL,
                    "str": VariableType.STRING,
                    "list": VariableType.LIST,
                }
                return type_mapping.get(annotation.value)
        return None

    def get_or_create_variable(
        self, name: str, var_type: Optional[VariableType] = None
    ) -> Z3Variable:
        """Get existing variable or create new one."""
        if name in self.variables:
            return self.variables[name]

        # Determine type
        if var_type is None:
            var_type = self.type_hints.get(name, VariableType.UNKNOWN)

        if var_type == VariableType.UNKNOWN:
            raise TypeInferenceError(f"Cannot determine type for variable '{name}'")

        # Create Z3 variable
        unique_name = f"{name}_{self._var_counter}"
        self._var_counter += 1

        if var_type == VariableType.INT:
            z3_var = z3.Int(unique_name)
        elif var_type == VariableType.REAL:
            z3_var = z3.Real(unique_name)
        elif var_type == VariableType.BOOL:
            z3_var = z3.Bool(unique_name)
        elif var_type == VariableType.STRING:
            z3_var = z3.String(unique_name)
        elif var_type == VariableType.OPTIONAL_INT:
            z3_var = z3.Const(unique_name, self.OptionInt)
        elif var_type == VariableType.OPTIONAL_REAL:
            z3_var = z3.Const(unique_name, self.OptionReal)
        elif var_type == VariableType.OPTIONAL_BOOL:
            z3_var = z3.Const(unique_name, self.OptionBool)
        elif var_type == VariableType.OPTIONAL_STRING:
            z3_var = z3.Const(unique_name, self.OptionString)
        else:
            raise UnsupportedConstructError(f"Unsupported variable type: {var_type}")

        z3_variable = Z3Variable(unique_name, z3_var, var_type, name)
        self.variables[name] = z3_variable
        return z3_variable

    def infer_type_from_literal(self, node: ast.expr) -> Optional[VariableType]:
        """Infer type from AST literal node."""
        if isinstance(node, ast.Constant):
            value = node.value
            if isinstance(
                value, bool
            ):  # Check bool before int (bool is subclass of int)
                return VariableType.BOOL
            elif isinstance(value, int):
                return VariableType.INT
            elif isinstance(value, float):
                return VariableType.REAL
            elif isinstance(value, str):
                return VariableType.STRING
        elif isinstance(node, ast.Num):  # Python < 3.8
            if isinstance(node.n, int):
                return VariableType.INT
            elif isinstance(node.n, float):
                return VariableType.REAL
        elif isinstance(node, ast.Str):  # Python < 3.8
            return VariableType.STRING
        elif isinstance(node, ast.NameConstant):  # Python < 3.8
            if isinstance(node.value, bool):
                return VariableType.BOOL
        return None

    def _infer_types_from_function(self, func_def: ast.FunctionDef):
        """Smart type inference that prefers regular types over optional types."""
        # Step 1: Detect variables that might be None
        none_variables = self._detect_none_usage(func_def)

        # Step 2: Detect variables used in regular operations (math, comparisons)
        regular_usage_vars = self._detect_regular_usage(func_def)

        # Step 3: Smart type decision: prefer regular types if variable is used in both contexts
        smart_none_vars = none_variables - regular_usage_vars

        # Store for use in comparison inference
        self._current_none_vars = smart_none_vars

        # Step 4: Walk through all nodes for type inference
        for node in ast.walk(func_def):
            if isinstance(node, ast.Assign):
                # Infer type from the assigned value
                value_type = self._infer_expression_type(node.value)

                if value_type:
                    # Apply to all assignment targets
                    for target in node.targets:
                        if isinstance(target, ast.Name):
                            var_name = target.id
                            # Only set if we don't already have a type for this variable
                            if var_name not in self.type_hints:
                                # Only make optional if ONLY used with None (not regular operations)
                                if var_name in smart_none_vars:
                                    optional_type = self._make_optional_type(value_type)
                                    self.type_hints[var_name] = optional_type
                                else:
                                    self.type_hints[var_name] = value_type

            elif isinstance(node, ast.Compare):
                # Infer types from comparisons like x > 0
                self._infer_types_from_comparison(node)

            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                # Handle isinstance(x, int) patterns
                if node.func.id == "isinstance" and len(node.args) >= 2:
                    self._infer_from_isinstance_call(node)

        # Step 5: Post-process remaining None-only variables
        for var_name in smart_none_vars:
            if var_name not in self.type_hints:
                # Default None-only variables to optional int
                self.type_hints[var_name] = VariableType.OPTIONAL_INT

    def _infer_expression_type(self, expr: ast.expr) -> Optional[VariableType]:
        """Infer the type of an expression."""
        if isinstance(expr, ast.Constant):
            return self.infer_type_from_literal(expr)
        elif isinstance(expr, (ast.Num, ast.Str, ast.NameConstant)):  # Python < 3.8
            return self.infer_type_from_literal(expr)
        elif isinstance(expr, ast.Name):
            # Look up existing type
            return self.type_hints.get(expr.id)
        elif isinstance(expr, ast.BinOp):
            return self._infer_binop_type(expr)
        elif isinstance(expr, ast.UnaryOp):
            return self._infer_unaryop_type(expr)
        elif isinstance(expr, ast.Call):
            return self._infer_call_type(expr)
        return None

    def _infer_binop_type(self, binop: ast.BinOp) -> Optional[VariableType]:
        """Infer type from binary operation."""
        left_type = self._infer_expression_type(binop.left)
        right_type = self._infer_expression_type(binop.right)

        # Arithmetic operations
        if isinstance(binop.op, (ast.Add, ast.Sub, ast.Mult, ast.Pow, ast.Mod)):
            # If either operand is real, result is real
            if left_type == VariableType.REAL or right_type == VariableType.REAL:
                return VariableType.REAL
            # If both are int, result is int
            elif left_type == VariableType.INT and right_type == VariableType.INT:
                return VariableType.INT
        elif isinstance(binop.op, ast.Div):
            # Division always produces float
            return VariableType.REAL
        elif isinstance(binop.op, ast.FloorDiv):
            # Floor division: if both int, result is int; otherwise real
            if left_type == VariableType.INT and right_type == VariableType.INT:
                return VariableType.INT
            else:
                return VariableType.REAL

        return None

    def _infer_unaryop_type(self, unaryop: ast.UnaryOp) -> Optional[VariableType]:
        """Infer type from unary operation."""
        operand_type = self._infer_expression_type(unaryop.operand)

        if isinstance(unaryop.op, (ast.UAdd, ast.USub)):
            # +x, -x preserve numeric type
            if operand_type in [VariableType.INT, VariableType.REAL]:
                return operand_type
        elif isinstance(unaryop.op, ast.Not):
            return VariableType.BOOL

        return None

    def _infer_call_type(self, call: ast.Call) -> Optional[VariableType]:
        """Infer type from function call."""
        if isinstance(call.func, ast.Name):
            func_name = call.func.id

            # Known builtin return types
            if func_name == "abs":
                # abs() returns same type as input (int or float)
                if call.args:
                    arg_type = self._infer_expression_type(call.args[0])
                    if arg_type in [VariableType.INT, VariableType.REAL]:
                        return arg_type
                return VariableType.INT  # Default
            elif func_name == "int":
                return VariableType.INT
            elif func_name == "float":
                return VariableType.REAL
            elif func_name == "bool":
                return VariableType.BOOL
            elif func_name == "str":
                return VariableType.STRING
            elif func_name == "len":
                return VariableType.INT
            elif func_name in ["min", "max"]:
                # Return type matches arguments
                if call.args:
                    arg_type = self._infer_expression_type(call.args[0])
                    return arg_type

        return None

    def _infer_types_from_comparison(self, compare: ast.Compare):
        """Enhanced type inference from comparison operations."""
        left_type = self._infer_expression_type(compare.left)

        # Check each comparator and operation
        for op, comparator in zip(compare.ops, compare.comparators):
            comp_type = self._infer_expression_type(comparator)

            # Enhanced inference for left operand
            if (
                isinstance(compare.left, ast.Name)
                and compare.left.id not in self.type_hints
            ):
                if comp_type in [VariableType.INT, VariableType.REAL]:
                    self.type_hints[compare.left.id] = comp_type
                elif comp_type == VariableType.STRING:
                    self.type_hints[compare.left.id] = VariableType.STRING
                elif comp_type == VariableType.BOOL:
                    self.type_hints[compare.left.id] = VariableType.BOOL
                # Special handling for numeric comparisons with literals
                elif isinstance(comparator, ast.Constant):
                    if isinstance(comparator.value, (int, float)):
                        inferred_type = (
                            VariableType.INT
                            if isinstance(comparator.value, int)
                            else VariableType.REAL
                        )
                        # Check if it's a None comparison that should be optional
                        if compare.left.id in getattr(
                            self, "_current_none_vars", set()
                        ):
                            inferred_type = self._make_optional_type(inferred_type)
                        self.type_hints[compare.left.id] = inferred_type
                    elif isinstance(comparator.value, str):
                        self.type_hints[compare.left.id] = VariableType.STRING

            # Enhanced inference for right operand
            if (
                isinstance(comparator, ast.Name)
                and comparator.id not in self.type_hints
            ):
                if left_type in [
                    VariableType.INT,
                    VariableType.REAL,
                    VariableType.STRING,
                    VariableType.BOOL,
                ]:
                    self.type_hints[comparator.id] = left_type
                # Infer from left side literals
                elif isinstance(compare.left, ast.Constant):
                    if isinstance(compare.left.value, (int, float)):
                        inferred_type = (
                            VariableType.INT
                            if isinstance(compare.left.value, int)
                            else VariableType.REAL
                        )
                        self.type_hints[comparator.id] = inferred_type
                    elif isinstance(compare.left.value, str):
                        self.type_hints[comparator.id] = VariableType.STRING

    def _infer_from_isinstance_call(self, call: ast.Call):
        """Infer types from isinstance(var, type) calls."""
        if len(call.args) >= 2:
            var_arg = call.args[0]
            type_arg = call.args[1]

            if isinstance(var_arg, ast.Name):
                var_name = var_arg.id
                inferred_type = self._extract_isinstance_type(type_arg)

                if inferred_type and var_name not in self.type_hints:
                    self.type_hints[var_name] = inferred_type

    def _extract_isinstance_type(self, type_expr: ast.expr) -> Optional[VariableType]:
        """Extract type from isinstance type check."""
        if isinstance(type_expr, ast.Name):
            type_mapping = {
                "int": VariableType.INT,
                "float": VariableType.REAL,
                "bool": VariableType.BOOL,
                "str": VariableType.STRING,
                "list": VariableType.LIST,
            }
            return type_mapping.get(type_expr.id)
        elif isinstance(type_expr, ast.Tuple) and type_expr.elts:
            # isinstance(x, (int, float)) - use the first type for simplicity
            return self._extract_isinstance_type(type_expr.elts[0])

        return None

    def translate_expression(
        self, expr: ast.expr, context: Optional[Dict[str, VariableType]] = None
    ) -> z3.ExprRef:
        """Translate a Python expression to Z3 formula."""
        if context:
            # Temporarily add context types
            old_hints = self.type_hints.copy()
            self.type_hints.update(context)

        try:
            result = self._translate_expr(expr)
            return result
        finally:
            if context:
                # Restore original type hints
                self.type_hints = old_hints

    def _translate_expr(self, expr: ast.expr) -> z3.ExprRef:
        """Internal expression translation."""

        # Literals
        if isinstance(expr, ast.Constant):
            value = expr.value
            if isinstance(value, bool):
                return z3.BoolVal(value)
            elif isinstance(value, int):
                return z3.IntVal(value)
            elif isinstance(value, float):
                return z3.RealVal(value)
            elif isinstance(value, str):
                return z3.StringVal(value)
            elif value is None:
                # Return None literal - type will be inferred from context
                return None  # Special marker for None literal
            else:
                raise UnsupportedConstructError(
                    f"Unsupported literal type: {type(value)}"
                )
        elif isinstance(expr, ast.Num):  # Python < 3.8
            if isinstance(expr.n, int):
                return z3.IntVal(expr.n)
            elif isinstance(expr.n, float):
                return z3.RealVal(expr.n)
            else:
                raise UnsupportedConstructError(
                    f"Unsupported number type: {type(expr.n)}"
                )
        elif isinstance(expr, ast.Str):  # Python < 3.8
            return z3.StringVal(expr.s)
        elif isinstance(expr, ast.NameConstant):  # Python < 3.8
            if isinstance(expr.value, bool):
                return z3.BoolVal(expr.value)
            elif expr.value is None:
                # Return None literal - type will be inferred from context
                return None  # Special marker for None literal
            else:
                raise UnsupportedConstructError(
                    f"Unsupported name constant: {expr.value}"
                )

        # Variables
        elif isinstance(expr, ast.Name):
            if isinstance(expr.ctx, ast.Load):
                var = self.get_or_create_variable(expr.id)
                return var.z3_var
            else:
                raise UnsupportedConstructError(
                    f"Unsupported name context: {type(expr.ctx)}"
                )

        # Binary operations
        elif isinstance(expr, ast.BinOp):
            left = self._translate_expr(expr.left)
            right = self._translate_expr(expr.right)

            if isinstance(expr.op, ast.Add):
                return left + right
            elif isinstance(expr.op, ast.Sub):
                return left - right
            elif isinstance(expr.op, ast.Mult):
                return left * right
            elif isinstance(expr.op, ast.Div):
                return left / right
            elif isinstance(expr.op, ast.Mod):
                return left % right
            elif isinstance(expr.op, ast.Pow):
                # Z3 doesn't have built-in power, use uninterpreted function
                pow_func = z3.Function("pow", left.sort(), right.sort(), left.sort())
                return pow_func(left, right)
            else:
                raise UnsupportedConstructError(
                    f"Unsupported binary operator: {type(expr.op)}"
                )

        # Comparisons
        elif isinstance(expr, ast.Compare):
            # Special handling for 'is None' and 'is not None' comparisons
            if len(expr.ops) == 1 and isinstance(expr.ops[0], (ast.Is, ast.IsNot)):
                op = expr.ops[0]
                comparator = expr.comparators[0]
                if isinstance(op, ast.Is):
                    return self._handle_is_comparison(expr.left, comparator, True)
                else:  # ast.IsNot
                    return self._handle_is_comparison(expr.left, comparator, False)

            # Special handling for membership testing
            if len(expr.ops) == 1 and isinstance(expr.ops[0], (ast.In, ast.NotIn)):
                op = expr.ops[0]
                comparator = expr.comparators[0]
                if isinstance(op, ast.In):
                    return self._handle_membership_testing_ast(
                        expr.left, comparator, True
                    )
                else:  # ast.NotIn
                    return self._handle_membership_testing_ast(
                        expr.left, comparator, False
                    )

            # Standard comparisons
            left = self._translate_expr(expr.left)
            result = left

            for op, comparator in zip(expr.ops, expr.comparators):
                right = self._translate_expr(comparator)

                if isinstance(op, ast.Eq):
                    comparison = result == right
                elif isinstance(op, ast.NotEq):
                    comparison = result != right
                elif isinstance(op, ast.Lt):
                    comparison = result < right
                elif isinstance(op, ast.LtE):
                    comparison = result <= right
                elif isinstance(op, ast.Gt):
                    comparison = result > right
                elif isinstance(op, ast.GtE):
                    comparison = result >= right
                else:
                    raise UnsupportedConstructError(
                        f"Unsupported comparison operator: {type(op)}"
                    )

                if result is left:
                    result = comparison
                else:
                    result = z3.And(result, comparison)

            return result

        # Boolean operations
        elif isinstance(expr, ast.BoolOp):
            values = [self._translate_expr(value) for value in expr.values]

            if isinstance(expr.op, ast.And):
                return z3.And(values)
            elif isinstance(expr.op, ast.Or):
                return z3.Or(values)
            else:
                raise UnsupportedConstructError(
                    f"Unsupported boolean operator: {type(expr.op)}"
                )

        # Unary operations
        elif isinstance(expr, ast.UnaryOp):
            operand = self._translate_expr(expr.operand)

            if isinstance(expr.op, ast.UAdd):
                return operand
            elif isinstance(expr.op, ast.USub):
                return -operand
            elif isinstance(expr.op, ast.Not):
                return z3.Not(operand)
            else:
                raise UnsupportedConstructError(
                    f"Unsupported unary operator: {type(expr.op)}"
                )

        # Function calls
        elif isinstance(expr, ast.Call):
            func_name = expr.func.id if isinstance(expr.func, ast.Name) else None

            # Special case for isinstance() - this should be handled differently
            if func_name == "isinstance":
                # isinstance(x, int) should translate to a type constraint
                if len(expr.args) >= 2:
                    var_expr = expr.args[0]
                    type_expr = expr.args[1]

                    if isinstance(var_expr, ast.Name):
                        # For isinstance(x, int), we assume it's True for typed variables
                        # This is a simplification - in practice this would need more sophisticated handling
                        var_name = var_expr.id
                        var_type = self._extract_isinstance_type(type_expr)

                        if var_type and var_name in self.variables:
                            # Return True if the variable matches the expected type
                            expected_z3_type = self.variables[var_name].var_type
                            return z3.BoolVal(expected_z3_type == var_type)
                        else:
                            # Conservative: assume isinstance check passes
                            return z3.BoolVal(True)

                # Fallback
                return z3.BoolVal(True)

            # Handle known pure builtin functions
            if func_name in self.PURE_BUILTINS:
                args = [self._translate_expr(arg) for arg in expr.args]
                builtin_handler = self.PURE_BUILTINS[func_name]

                if func_name == "len":
                    # Enhanced handling for len() with constraints
                    if len(expr.args) != 1:
                        raise UnsupportedConstructError(
                            "len() requires exactly one argument"
                        )

                    # Get the argument - should be a container variable name
                    arg = expr.args[0]
                    if isinstance(arg, ast.Name):
                        container_name = arg.id

                        # Create or get length variable for this container
                        len_var_name = f"{container_name}_len"
                        if len_var_name not in self.variables:
                            len_var = self.get_or_create_variable(
                                len_var_name, VariableType.INT
                            )
                            # Add constraint: length >= 0
                            self.add_constraint(len_var.z3_var >= 0)
                        else:
                            len_var = self.variables[len_var_name]

                        return len_var.z3_var
                    else:
                        # Fallback to uninterpreted function for complex expressions
                        len_func = z3.Function("len", args[0].sort(), z3.IntSort())
                        return len_func(args[0])
                else:
                    # Apply the lambda handler
                    return builtin_handler(*args)
            else:
                # User-defined function - will be handled by logic function encoder
                # For now, create uninterpreted function
                args = [self._translate_expr(arg) for arg in expr.args]
                if args:
                    arg_sorts = [arg.sort() for arg in args]
                    # Assume integer return type for now (will be refined)
                    func_z3 = z3.Function(func_name, *arg_sorts, z3.IntSort())
                    return func_z3(*args)
                else:
                    func_z3 = z3.Function(func_name, z3.IntSort())
                    return func_z3()
        else:
            raise UnsupportedConstructError("Only simple function names supported")

    def _translate_subscript(self, expr: ast.Subscript) -> z3.ExprRef:
        """Translate subscript operation (list[index])."""
        # Basic list indexing support
        value = self._translate_expr(expr.value)
        slice_val = self._translate_expr(expr.slice)

        # Create array access function
        if value.sort() == z3.StringSort():
            # String indexing
            return z3.SubString(value, slice_val, 1)  # Get one character
        else:
            # Assume list/array - use uninterpreted function for now
            array_get = z3.Function(
                "array_get", value.sort(), slice_val.sort(), z3.IntSort()
            )
            return array_get(value, slice_val)

    def translate_assertion(
        self, assert_node: ast.Assert, context: Optional[Dict[str, VariableType]] = None
    ) -> z3.ExprRef:
        """Translate an assert statement to Z3 formula."""
        return self.translate_expression(assert_node.test, context)

    def add_constraint(self, constraint: z3.ExprRef):
        """Add a constraint to the solver."""
        self.solver.add(constraint)

    def check_satisfiability(self) -> Tuple[bool, Optional[Dict[str, Any]]]:
        """Check if current constraints are satisfiable."""
        result = self.solver.check()

        if result == z3.sat:
            model = self.solver.model()
            # Convert model to Python values
            model_dict = {}
            for var_name, z3_var in self.variables.items():
                if model[z3_var.z3_var] is not None:
                    z3_val = model[z3_var.z3_var]

                    # Convert Z3 value to Python
                    if z3_var.var_type == VariableType.INT:
                        model_dict[var_name] = z3_val.as_long()
                    elif z3_var.var_type == VariableType.REAL:
                        # Z3 rational to float approximation
                        model_dict[var_name] = float(
                            z3_val.numerator_as_long()
                        ) / float(z3_val.denominator_as_long())
                    elif z3_var.var_type == VariableType.BOOL:
                        model_dict[var_name] = bool(z3_val)
                    elif z3_var.var_type == VariableType.STRING:
                        model_dict[var_name] = str(z3_val)
                    else:
                        model_dict[var_name] = str(z3_val)

            return True, model_dict
        elif result == z3.unsat:
            return False, None
        else:
            # Unknown
            return False, None

    def find_counterexample(
        self, assertion: z3.ExprRef
    ) -> Tuple[bool, Optional[Dict[str, Any]]]:
        """Find a counterexample by negating the assertion."""
        # Push a new context
        self.solver.push()

        try:
            # Add negation of assertion
            self.solver.add(z3.Not(assertion))

            # Check if satisfiable (i.e., counterexample exists)
            result = self.solver.check()

            if result == z3.sat:
                model = self.solver.model()
                # Convert to Python values (same as check_satisfiability)
                model_dict = {}
                for var_name, z3_var in self.variables.items():
                    if model[z3_var.z3_var] is not None:
                        z3_val = model[z3_var.z3_var]

                        if z3_var.var_type == VariableType.INT:
                            model_dict[var_name] = z3_val.as_long()
                        elif z3_var.var_type == VariableType.REAL:
                            model_dict[var_name] = float(
                                z3_val.numerator_as_long()
                            ) / float(z3_val.denominator_as_long())
                        elif z3_var.var_type == VariableType.BOOL:
                            model_dict[var_name] = bool(z3_val)
                        elif z3_var.var_type == VariableType.STRING:
                            model_dict[var_name] = str(z3_val)
                        else:
                            model_dict[var_name] = str(z3_val)

                return True, model_dict  # Counterexample found
            else:
                return False, None  # No counterexample (assertion is valid)

        finally:
            # Pop context to restore original constraints
            self.solver.pop()

    def get_solver_assertions(self) -> List[str]:
        """Get string representation of current solver assertions."""
        return [str(assertion) for assertion in self.solver.assertions()]

    def get_variable_summary(self) -> Dict[str, str]:
        """Get summary of declared variables."""
        summary = {}
        for var_name, z3_var in self.variables.items():
            summary[var_name] = f"{z3_var.var_type.value} ({z3_var.name})"
        return summary


# Use the full implementation
SMTTranslator = SMTTranslator
