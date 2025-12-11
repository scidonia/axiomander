"""
Assertion discovery and analysis for axiomander.

This module finds assert statements in Python code and analyzes their context
for verification purposes.
"""

import ast
from typing import List, Dict, Optional, Set, Tuple, Any
from dataclasses import dataclass
from enum import Enum

from .parser import ParsedCode, SourceLocation, ASTTraverser


# Temporary stubs for type checking - will be replaced with actual imports
class PurityLevel(Enum):
    PURE = "pure"


class PurityResult:
    def __init__(self, level, reason, location=None):
        self.level = level
        self.reason = reason
        self.location = location


class PurityAnalyzer:
    def __init__(self, parsed_code):
        self.parsed_code = parsed_code

    def analyze_node(self, node):
        return PurityResult(PurityLevel.PURE, "stub")


class AssertionType(Enum):
    """Types of assertions we can handle."""

    PRECONDITION = "precondition"  # At function start
    POSTCONDITION = "postcondition"  # Before function return
    LOOP_INVARIANT = "loop_invariant"  # At loop beginning
    GENERAL = "general"  # General assertion in code
    TERMINATION = "termination"  # Termination measure for recursion


@dataclass
class AssertionInfo:
    """Information about a discovered assertion."""

    node: ast.Assert
    location: SourceLocation
    assertion_type: AssertionType
    containing_function: Optional[ast.FunctionDef] = None
    containing_loop: Optional[ast.stmt] = None
    test_expression: Optional[ast.expr] = None
    message: Optional[ast.expr] = None
    is_pure: Optional[bool] = None
    purity_result: Optional[PurityResult] = None


@dataclass
class FunctionContract:
    """Contract information for a function."""

    function: ast.FunctionDef
    preconditions: List[AssertionInfo]
    postconditions: List[AssertionInfo]
    loop_invariants: Dict[ast.stmt, List[AssertionInfo]]  # loop -> invariants
    general_assertions: List[AssertionInfo]
    is_recursive: bool = False
    termination_measures: Optional[List[AssertionInfo]] = None


class AssertionFinder:
    """Finds and categorizes assert statements in Python code."""

    def __init__(self, parsed_code: ParsedCode):
        self.parsed_code = parsed_code
        self.traverser = ASTTraverser(parsed_code)
        self.purity_analyzer = PurityAnalyzer(parsed_code)
        self.source_map = parsed_code.source_map

        # Results
        self.assertions: List[AssertionInfo] = []
        self.function_contracts: Dict[ast.FunctionDef, FunctionContract] = {}

    def find_all_assertions(self) -> List[AssertionInfo]:
        """Find all assertions in the parsed code."""
        self.assertions = []
        self.function_contracts = {}

        # Find all assert statements
        assert_nodes = self.traverser.find_assertions()

        for assert_node in assert_nodes:
            assertion_info = self._analyze_assertion(assert_node)
            self.assertions.append(assertion_info)

            # Organize by function
            if assertion_info.containing_function:
                self._add_to_function_contract(assertion_info)

        return self.assertions

    def get_function_contracts(self) -> Dict[ast.FunctionDef, FunctionContract]:
        """Get contracts for all functions."""
        return self.function_contracts

    def get_assertions_in_function(self, func: ast.FunctionDef) -> List[AssertionInfo]:
        """Get all assertions within a specific function."""
        return [
            assertion
            for assertion in self.assertions
            if assertion.containing_function == func
        ]

    def get_verification_targets(self) -> List[AssertionInfo]:
        """Get assertions that should be verified (excluding preconditions)."""
        return [
            assertion
            for assertion in self.assertions
            if assertion.assertion_type
            in {
                AssertionType.POSTCONDITION,
                AssertionType.GENERAL,
                AssertionType.LOOP_INVARIANT,
            }
        ]

    def _analyze_assertion(self, assert_node: ast.Assert) -> AssertionInfo:
        """Analyze a single assert statement."""
        location = self.source_map.get(assert_node)
        if not location:
            location = SourceLocation("<unknown>", 0, 0)

        # Find containing function and loop
        containing_function = self.traverser.get_function_containing_node(assert_node)
        containing_loop = self._get_containing_loop(assert_node)

        # Determine assertion type based on context
        assertion_type = self._classify_assertion(
            assert_node, containing_function, containing_loop
        )

        # Analyze purity of the test expression
        purity_result = self.purity_analyzer.analyze_node(assert_node.test)
        is_pure = purity_result.level == PurityLevel.PURE

        return AssertionInfo(
            node=assert_node,
            location=location,
            assertion_type=assertion_type,
            containing_function=containing_function,
            containing_loop=containing_loop,
            test_expression=assert_node.test,
            message=assert_node.msg,
            is_pure=is_pure,
            purity_result=purity_result,
        )

    def _classify_assertion(
        self,
        assert_node: ast.Assert,
        containing_function: Optional[ast.FunctionDef],
        containing_loop: Optional[ast.stmt],
    ) -> AssertionType:
        """Classify an assertion based on its position and context."""

        if not containing_function:
            return AssertionType.GENERAL

        assert_location = self.source_map.get(assert_node)
        func_location = self.source_map.get(containing_function)

        if not assert_location or not func_location:
            return AssertionType.GENERAL

        # Check if this is at the very beginning of the function (precondition)
        if self._is_at_function_start(assert_node, containing_function):
            return AssertionType.PRECONDITION

        # Check if this is right before a return statement (postcondition)
        if self._is_before_return(assert_node, containing_function):
            return AssertionType.POSTCONDITION

        # Check if this is at the beginning of a loop (invariant)
        if containing_loop and self._is_at_loop_start(assert_node, containing_loop):
            return AssertionType.LOOP_INVARIANT

        # Check if this looks like a termination measure
        if self._is_termination_measure(assert_node, containing_function):
            return AssertionType.TERMINATION

        return AssertionType.GENERAL

    def _is_at_function_start(
        self, assert_node: ast.Assert, func: ast.FunctionDef
    ) -> bool:
        """Check if assertion is at the start of the function (allows consecutive assertions)."""
        if not func.body:
            return False

        # Find position of assert in function body
        try:
            assert_index = func.body.index(assert_node)

            # Check if everything before this assertion is either:
            # 1. A docstring (string literal)
            # 2. Another assertion
            # 3. Nothing (this is the first statement)

            for i in range(assert_index):
                stmt = func.body[i]

                # Allow docstrings
                if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Str):
                    continue  # Skip docstring
                elif isinstance(stmt, ast.Expr) and isinstance(
                    stmt.value, ast.Constant
                ):
                    if isinstance(stmt.value.value, str):
                        continue  # Skip string constant (docstring)

                # Allow other assertions
                elif isinstance(stmt, ast.Assert):
                    continue  # Other assertions are OK

                # Any other statement means this is not at function start
                else:
                    return False

            return True
        except ValueError:
            # Assert not directly in function body (might be nested)
            return False

    def _is_before_return(self, assert_node: ast.Assert, func: ast.FunctionDef) -> bool:
        """Check if assertion is before a return statement (allows consecutive assertions)."""
        if not func.body:
            return False

        try:
            assert_index = func.body.index(assert_node)

            # Check if everything after this assertion until the end is either:
            # 1. Another assertion
            # 2. A return statement

            found_return = False
            for i in range(assert_index + 1, len(func.body)):
                stmt = func.body[i]

                if isinstance(stmt, ast.Return):
                    found_return = True
                    break
                elif isinstance(stmt, ast.Assert):
                    continue  # Other assertions are OK
                else:
                    # Some other statement between assertion and return
                    return False

            return found_return
        except ValueError:
            pass

        return False

    def _is_at_loop_start(self, assert_node: ast.Assert, loop: ast.stmt) -> bool:
        """Check if assertion is at the beginning of a loop."""
        if isinstance(loop, (ast.For, ast.While)):
            if loop.body and len(loop.body) > 0:
                return loop.body[0] == assert_node
        return False

    def _is_termination_measure(
        self, assert_node: ast.Assert, func: ast.FunctionDef
    ) -> bool:
        """Heuristically detect if assertion is a termination measure."""
        # Look for patterns like: assert n > 0, assert n - 1 < n, etc.
        # This is a simple heuristic and can be extended

        if not isinstance(assert_node.test, ast.Compare):
            return False

        # Look for comparisons involving function parameters
        func_params = {arg.arg for arg in func.args.args}

        # Check if assertion involves parameters and comparison operators
        if self._expression_involves_params(assert_node.test, func_params):
            # Look for operators like <, >, <=, >= which are common in termination measures
            has_ordering = any(
                isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE))
                for op in assert_node.test.ops
            )
            return has_ordering

        return False

    def _expression_involves_params(self, expr: ast.expr, params: Set[str]) -> bool:
        """Check if expression involves function parameters."""
        for node in ast.walk(expr):
            if isinstance(node, ast.Name) and node.id in params:
                return True
        return False

    def _get_containing_loop(self, node: ast.AST) -> Optional[ast.stmt]:
        """Find the loop that contains the given node."""
        # This is a simplified implementation
        # In practice, we'd need to traverse up the AST tree

        for potential_loop in ast.walk(self.parsed_code.ast_tree):
            if isinstance(potential_loop, (ast.For, ast.While)):
                # Check if node is contained within this loop
                if self._node_in_loop_body(node, potential_loop):
                    return potential_loop

        return None

    def _node_in_loop_body(self, node: ast.AST, loop: ast.stmt) -> bool:
        """Check if node is in the body of the loop."""
        if isinstance(loop, (ast.For, ast.While)):
            for stmt in loop.body:
                if stmt == node or self._node_is_descendant(node, stmt):
                    return True
        return False

    def _node_is_descendant(self, node: ast.AST, ancestor: ast.AST) -> bool:
        """Check if node is a descendant of ancestor in the AST."""
        for descendant in ast.walk(ancestor):
            if descendant == node:
                return True
        return False

    def _add_to_function_contract(self, assertion_info: AssertionInfo):
        """Add assertion to the appropriate function contract."""
        func = assertion_info.containing_function
        if not func:
            return

        if func not in self.function_contracts:
            self.function_contracts[func] = FunctionContract(
                function=func,
                preconditions=[],
                postconditions=[],
                loop_invariants={},
                general_assertions=[],
                termination_measures=[],
            )

        contract = self.function_contracts[func]

        if assertion_info.assertion_type == AssertionType.PRECONDITION:
            contract.preconditions.append(assertion_info)
        elif assertion_info.assertion_type == AssertionType.POSTCONDITION:
            contract.postconditions.append(assertion_info)
        elif assertion_info.assertion_type == AssertionType.LOOP_INVARIANT:
            loop = assertion_info.containing_loop
            if loop is not None:
                if loop not in contract.loop_invariants:
                    contract.loop_invariants[loop] = []
                contract.loop_invariants[loop].append(assertion_info)
        elif assertion_info.assertion_type == AssertionType.TERMINATION:
            if contract.termination_measures is None:
                contract.termination_measures = []
            contract.termination_measures.append(assertion_info)
        else:
            contract.general_assertions.append(assertion_info)

        # Check if function is recursive
        if self._is_recursive_function(func):
            contract.is_recursive = True

    def _is_recursive_function(self, func: ast.FunctionDef) -> bool:
        """Check if function is recursive by looking for self-calls."""
        func_name = func.name

        for node in ast.walk(func):
            if isinstance(node, ast.Call):
                # Check for direct recursive call
                if isinstance(node.func, ast.Name) and node.func.id == func_name:
                    return True

        return False

    def get_impure_assertions(self) -> List[AssertionInfo]:
        """Get assertions that contain impure expressions."""
        return [assertion for assertion in self.assertions if not assertion.is_pure]

    def get_pure_assertions(self) -> List[AssertionInfo]:
        """Get assertions that contain only pure expressions."""
        return [assertion for assertion in self.assertions if assertion.is_pure]
