"""
Purity analysis for Python code.

This module determines whether Python constructs are "pure" (no observable side effects)
or "impure" (may have observable side effects). Uses a conservative approach where
unknown constructs are considered impure.
"""

import ast
from typing import Set, Dict, List, Optional, Any
from enum import Enum
from dataclasses import dataclass

from .parser import ParsedCode, SourceLocation


class PurityLevel(Enum):
    """Classification levels for code purity."""

    PURE = "pure"  # No observable side effects, deterministic
    IMPURE = "impure"  # Has or may have observable side effects
    UNKNOWN = "unknown"  # Cannot determine, defaults to impure


@dataclass
class PurityResult:
    """Result of purity analysis."""

    level: PurityLevel
    reason: str
    location: Optional[SourceLocation] = None
    details: Optional[Dict[str, Any]] = None


class PurityAnalyzer:
    """Analyzes Python code constructs for purity."""

    # Known pure built-in functions
    PURE_BUILTINS = {
        "abs",
        "all",
        "any",
        "bin",
        "bool",
        "chr",
        "complex",
        "dict",
        "divmod",
        "enumerate",
        "float",
        "format",
        "frozenset",
        "hex",
        "int",
        "len",
        "list",
        "max",
        "min",
        "oct",
        "ord",
        "pow",
        "range",
        "reversed",
        "round",
        "set",
        "slice",
        "sorted",
        "str",
        "sum",
        "tuple",
        "type",
        "zip",
    }

    # Known pure modules (mathematical operations, etc.)
    PURE_MODULES = {
        "math",
        "cmath",
        "decimal",
        "fractions",
        "statistics",
        "operator",
        "functools",
        "itertools",  # Most functions are pure
    }

    # Known impure built-ins
    IMPURE_BUILTINS = {
        "print",
        "input",
        "open",
        "exec",
        "eval",
        "compile",
        "__import__",
        "globals",
        "locals",
        "vars",
        "dir",
        "help",
        "id",
        "hash",
    }

    def __init__(self, parsed_code: ParsedCode):
        self.parsed_code = parsed_code
        self.source_map = parsed_code.source_map
        # Track user-defined pure functions (can be extended)
        self.pure_functions: Set[str] = set()
        self.impure_functions: Set[str] = set()

    def analyze_node(self, node: ast.AST) -> PurityResult:
        """Analyze a single AST node for purity."""
        location = self.source_map.get(node)

        # Handle different node types
        if isinstance(node, ast.expr):
            return self._analyze_expression(node, location)
        elif isinstance(node, ast.stmt):
            return self._analyze_statement(node, location)
        else:
            return PurityResult(
                PurityLevel.UNKNOWN,
                f"Unknown node type: {type(node).__name__}",
                location,
            )

    def analyze_function(self, func_node: ast.FunctionDef) -> PurityResult:
        """Analyze a function definition for purity."""
        location = self.source_map.get(func_node)

        # Check function body for impure constructs
        for stmt in func_node.body:
            stmt_result = self.analyze_node(stmt)
            if stmt_result.level == PurityLevel.IMPURE:
                return PurityResult(
                    PurityLevel.IMPURE,
                    f"Contains impure statement: {stmt_result.reason}",
                    location,
                    {"impure_statement": stmt_result},
                )
            elif stmt_result.level == PurityLevel.UNKNOWN:
                return PurityResult(
                    PurityLevel.IMPURE,  # Conservative: unknown -> impure
                    f"Contains unknown construct: {stmt_result.reason}",
                    location,
                    {"unknown_statement": stmt_result},
                )

        return PurityResult(
            PurityLevel.PURE, "Function body contains only pure constructs", location
        )

    def analyze_expression_sequence(self, expressions: List[ast.expr]) -> PurityResult:
        """Analyze a sequence of expressions for collective purity."""
        for expr in expressions:
            result = self._analyze_expression(expr)
            if result.level != PurityLevel.PURE:
                return result

        return PurityResult(PurityLevel.PURE, "All expressions are pure")

    def _analyze_expression(
        self, node: ast.expr, location: Optional[SourceLocation] = None
    ) -> PurityResult:
        """Analyze an expression node."""

        # Literal values are always pure
        if isinstance(
            node, (ast.Constant, ast.Num, ast.Str, ast.Bytes, ast.NameConstant)
        ):
            return PurityResult(PurityLevel.PURE, "Literal value", location)

        # Variable names are pure (reading variables)
        elif isinstance(node, ast.Name):
            return PurityResult(PurityLevel.PURE, "Variable reference", location)

        # Attribute access is pure if object is pure
        elif isinstance(node, ast.Attribute):
            value_result = self._analyze_expression(node.value, location)
            if value_result.level == PurityLevel.PURE:
                return PurityResult(
                    PurityLevel.PURE, "Attribute access on pure value", location
                )
            return value_result

        # Binary operations are pure if both operands are pure
        elif isinstance(node, ast.BinOp):
            left_result = self._analyze_expression(node.left, location)
            right_result = self._analyze_expression(node.right, location)

            if (
                left_result.level == PurityLevel.PURE
                and right_result.level == PurityLevel.PURE
            ):
                return PurityResult(
                    PurityLevel.PURE, "Binary operation on pure operands", location
                )
            elif left_result.level == PurityLevel.IMPURE:
                return left_result
            else:
                return right_result

        # Comparison operations
        elif isinstance(node, ast.Compare):
            left_result = self._analyze_expression(node.left, location)
            if left_result.level != PurityLevel.PURE:
                return left_result

            for comparator in node.comparators:
                comp_result = self._analyze_expression(comparator, location)
                if comp_result.level != PurityLevel.PURE:
                    return comp_result

            return PurityResult(PurityLevel.PURE, "Comparison of pure values", location)

        # Boolean operations
        elif isinstance(node, ast.BoolOp):
            for value in node.values:
                val_result = self._analyze_expression(value, location)
                if val_result.level != PurityLevel.PURE:
                    return val_result
            return PurityResult(
                PurityLevel.PURE, "Boolean operation on pure values", location
            )

        # Unary operations
        elif isinstance(node, ast.UnaryOp):
            operand_result = self._analyze_expression(node.operand, location)
            return operand_result

        # Function calls - need careful analysis
        elif isinstance(node, ast.Call):
            return self._analyze_function_call(node, location)

        # Subscripting (indexing) - pure if all parts are pure
        elif isinstance(node, ast.Subscript):
            value_result = self._analyze_expression(node.value, location)
            slice_result = self._analyze_expression(node.slice, location)

            if (
                value_result.level == PurityLevel.PURE
                and slice_result.level == PurityLevel.PURE
            ):
                return PurityResult(
                    PurityLevel.PURE, "Subscript access on pure values", location
                )
            return (
                value_result if value_result.level != PurityLevel.PURE else slice_result
            )

        # Container literals are pure if contents are pure
        elif isinstance(node, (ast.List, ast.Tuple, ast.Set)):
            for elt in node.elts:
                elt_result = self._analyze_expression(elt, location)
                if elt_result.level != PurityLevel.PURE:
                    return elt_result
            return PurityResult(
                PurityLevel.PURE,
                f"{type(node).__name__} literal with pure elements",
                location,
            )

        elif isinstance(node, ast.Dict):
            for key, value in zip(node.keys, node.values):
                if key:  # key can be None in dict unpacking
                    key_result = self._analyze_expression(key, location)
                    if key_result.level != PurityLevel.PURE:
                        return key_result
                value_result = self._analyze_expression(value, location)
                if value_result.level != PurityLevel.PURE:
                    return value_result
            return PurityResult(
                PurityLevel.PURE, "Dict literal with pure elements", location
            )

        # List/set/dict comprehensions are pure if all parts are pure
        elif isinstance(
            node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
        ):
            return self._analyze_comprehension(node, location)

        # Lambda functions - analyze body
        elif isinstance(node, ast.Lambda):
            body_result = self._analyze_expression(node.body, location)
            return body_result

        # Conditional expression
        elif isinstance(node, ast.IfExp):
            test_result = self._analyze_expression(node.test, location)
            body_result = self._analyze_expression(node.body, location)
            orelse_result = self._analyze_expression(node.orelse, location)

            for result in [test_result, body_result, orelse_result]:
                if result.level != PurityLevel.PURE:
                    return result

            return PurityResult(
                PurityLevel.PURE, "Conditional expression with pure parts", location
            )

        # Default to unknown/impure for unhandled expression types
        else:
            return PurityResult(
                PurityLevel.UNKNOWN,
                f"Unknown expression type: {type(node).__name__}",
                location,
            )

    def _analyze_statement(
        self, node: ast.stmt, location: Optional[SourceLocation] = None
    ) -> PurityResult:
        """Analyze a statement node."""

        # Return statements are pure if the return value is pure
        if isinstance(node, ast.Return):
            if node.value:
                return self._analyze_expression(node.value, location)
            return PurityResult(
                PurityLevel.PURE, "Return statement with no value", location
            )

        # Expression statements are pure if the expression is pure
        elif isinstance(node, ast.Expr):
            return self._analyze_expression(node.value, location)

        # Assignment statements can be pure if RHS is pure and we're not modifying globals
        elif isinstance(node, ast.Assign):
            # Check RHS
            value_result = self._analyze_expression(node.value, location)
            if value_result.level != PurityLevel.PURE:
                return value_result

            # Check if we're assigning to local variables (pure) vs attributes/subscripts (potentially impure)
            for target in node.targets:
                if isinstance(target, ast.Name):
                    continue  # Local variable assignment is pure
                else:
                    return PurityResult(
                        PurityLevel.IMPURE,
                        "Assignment to attribute or subscript (potentially side-effecting)",
                        location,
                    )

            return PurityResult(
                PurityLevel.PURE,
                "Assignment to local variables with pure RHS",
                location,
            )

        # Assert statements are pure if the test expression is pure
        elif isinstance(node, ast.Assert):
            test_result = self._analyze_expression(node.test, location)
            if node.msg:
                msg_result = self._analyze_expression(node.msg, location)
                if msg_result.level != PurityLevel.PURE:
                    return msg_result
            return test_result

        # Pass statements are pure
        elif isinstance(node, ast.Pass):
            return PurityResult(PurityLevel.PURE, "Pass statement", location)

        # Analyze if statements properly instead of blanket rejection
        elif isinstance(node, ast.If):
            return self._analyze_if_statement(node, location)

        # Other control flow statements are still complex and potentially impure
        elif isinstance(node, (ast.For, ast.While, ast.Try, ast.With)):
            return PurityResult(
                PurityLevel.IMPURE,
                f"Control flow statement: {type(node).__name__}",
                location,
            )

        # Function and class definitions are impure (they modify the namespace)
        elif isinstance(node, (ast.FunctionDef, ast.ClassDef, ast.AsyncFunctionDef)):
            return PurityResult(
                PurityLevel.IMPURE,
                f"Definition statement: {type(node).__name__}",
                location,
            )

        # Import statements are impure
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            return PurityResult(PurityLevel.IMPURE, "Import statement", location)

        # Most other statements are impure by default
        else:
            return PurityResult(
                PurityLevel.IMPURE,
                f"Statement type {type(node).__name__} assumed impure",
                location,
            )

    def _analyze_function_call(
        self, node: ast.Call, location: Optional[SourceLocation] = None
    ) -> PurityResult:
        """Analyze a function call for purity."""

        # First check if arguments are pure
        for arg in node.args:
            arg_result = self._analyze_expression(arg, location)
            if arg_result.level != PurityLevel.PURE:
                return arg_result

        for keyword in node.keywords:
            kw_result = self._analyze_expression(keyword.value, location)
            if kw_result.level != PurityLevel.PURE:
                return kw_result

        # Determine what function is being called
        func_name = self._get_function_name(node.func)

        if func_name in self.IMPURE_BUILTINS:
            return PurityResult(
                PurityLevel.IMPURE, f"Call to impure builtin: {func_name}", location
            )

        if func_name in self.PURE_BUILTINS:
            return PurityResult(
                PurityLevel.PURE, f"Call to pure builtin: {func_name}", location
            )

        if func_name in self.pure_functions:
            return PurityResult(
                PurityLevel.PURE, f"Call to known pure function: {func_name}", location
            )

        if func_name in self.impure_functions:
            return PurityResult(
                PurityLevel.IMPURE,
                f"Call to known impure function: {func_name}",
                location,
            )

        # Check module-qualified calls
        if "." in func_name:
            module_name = func_name.split(".")[0]
            if module_name in self.PURE_MODULES:
                return PurityResult(
                    PurityLevel.PURE,
                    f"Call to function in pure module: {func_name}",
                    location,
                )

        # Default: unknown function calls are considered impure
        return PurityResult(
            PurityLevel.IMPURE,
            f"Unknown function call (conservative): {func_name}",
            location,
        )

    def _analyze_comprehension(
        self, node: ast.expr, location: Optional[SourceLocation] = None
    ) -> PurityResult:
        """Analyze list/set/dict comprehensions and generator expressions."""

        if isinstance(node, ast.ListComp):
            elt_result = self._analyze_expression(node.elt, location)
            if elt_result.level != PurityLevel.PURE:
                return elt_result
        elif isinstance(node, ast.SetComp):
            elt_result = self._analyze_expression(node.elt, location)
            if elt_result.level != PurityLevel.PURE:
                return elt_result
        elif isinstance(node, ast.DictComp):
            key_result = self._analyze_expression(node.key, location)
            value_result = self._analyze_expression(node.value, location)
            if key_result.level != PurityLevel.PURE:
                return key_result
            if value_result.level != PurityLevel.PURE:
                return value_result
        elif isinstance(node, ast.GeneratorExp):
            elt_result = self._analyze_expression(node.elt, location)
            if elt_result.level != PurityLevel.PURE:
                return elt_result

        # Check generators (for clauses)
        generators = getattr(node, "generators", [])
        for gen in generators:
            iter_result = self._analyze_expression(gen.iter, location)
            if iter_result.level != PurityLevel.PURE:
                return iter_result

            # Check conditions
            for if_clause in gen.ifs:
                if_result = self._analyze_expression(if_clause, location)
                if if_result.level != PurityLevel.PURE:
                    return if_result

        return PurityResult(
            PurityLevel.PURE, "Comprehension with pure components", location
        )

    def _analyze_if_statement(self, node: ast.If, location: str) -> PurityResult:
        """
        Analyze an if statement for purity.
        
        An if statement is pure if:
        1. The test condition is pure
        2. All statements in the if body are pure  
        3. All statements in elif bodies are pure
        4. All statements in the else body are pure
        
        Args:
            node: The if statement AST node
            location: Location string for error reporting
            
        Returns:
            PurityResult indicating if the if statement is pure
        """
        # Check the test condition
        test_result = self._analyze_expression(node.test, f"{location}.test")
        if test_result.level != PurityLevel.PURE:
            return PurityResult(
                PurityLevel.IMPURE,
                f"If statement test is impure: {test_result.reason}",
                location,
            )

        # Check the if body
        for stmt in node.body:
            stmt_result = self._analyze_statement(stmt, f"{location}.if_body")
            if stmt_result.level != PurityLevel.PURE:
                return PurityResult(
                    PurityLevel.IMPURE,
                    f"If statement body is impure: {stmt_result.reason}",
                    location,
                )

        # Check elif clauses 
        for elif_clause in node.orelse:
            if isinstance(elif_clause, ast.If):  # elif is represented as nested if
                elif_result = self._analyze_if_statement(elif_clause, f"{location}.elif")
                if elif_result.level != PurityLevel.PURE:
                    return PurityResult(
                        PurityLevel.IMPURE,
                        f"Elif clause is impure: {elif_result.reason}",
                        location,
                    )
            else:
                # else clause (non-if statement in orelse)
                stmt_result = self._analyze_statement(elif_clause, f"{location}.else_body")
                if stmt_result.level != PurityLevel.PURE:
                    return PurityResult(
                        PurityLevel.IMPURE,
                        f"Else clause is impure: {stmt_result.reason}",
                        location,
                    )

        # If all parts are pure, the if statement is pure
        return PurityResult(
            PurityLevel.PURE,
            "Pure conditional statement",
            location,
        )

    def _get_function_name(self, func_node: ast.expr) -> str:
        """Extract function name from a call node."""
        if isinstance(func_node, ast.Name):
            return func_node.id
        elif isinstance(func_node, ast.Attribute):
            # For method calls like obj.method() or module.func()
            value_name = self._get_function_name(func_node.value)
            return f"{value_name}.{func_node.attr}"
        else:
            # Complex function expressions
            return "<complex>"

    def mark_function_pure(self, func_name: str):
        """Mark a user-defined function as pure."""
        self.pure_functions.add(func_name)
        self.impure_functions.discard(func_name)

    def mark_function_impure(self, func_name: str):
        """Mark a user-defined function as impure."""
        self.impure_functions.add(func_name)
        self.pure_functions.discard(func_name)
