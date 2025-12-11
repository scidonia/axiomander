"""
Weakest precondition calculator implementing Dijkstra's method.

This module implements backward assertion propagation through pure code
to compute the weakest precondition that would ensure an assertion holds.
"""

import ast
from typing import Dict, List, Optional, Set, Union, Any, Tuple
from dataclasses import dataclass
from enum import Enum

# Temporary import stubs - will be fixed when imports are resolved
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ..ast.parser import ParsedCode, SourceLocation, ASTTraverser
else:
    # Create temporary stubs
    class ParsedCode:
        def __init__(self, ast_tree, source_code, file_path, source_map):
            self.ast_tree = ast_tree
            self.source_code = source_code
            self.file_path = file_path
            self.source_map = source_map

    class SourceLocation:
        def __init__(self, file, line, column):
            self.file = file
            self.line = line
            self.column = column

    class ASTTraverser:
        def __init__(self, parsed_code):
            self.parsed_code = parsed_code

        def get_function_containing_node(self, node):
            return None

        def get_statements_before_node(self, node):
            return []


class WPCalculationError(Exception):
    """Raised when weakest precondition calculation fails."""

    pass


class PropagationResult(Enum):
    """Result of attempting to propagate an assertion backward."""

    SUCCESS = "success"  # Successfully moved backward
    BLOCKED = "blocked"  # Hit impure boundary, cannot continue
    IMPOSSIBLE = "impossible"  # Logically impossible to satisfy
    ERROR = "error"  # Calculation error


@dataclass
class WPResult:
    """Result of weakest precondition calculation."""

    result: PropagationResult
    condition: Optional[ast.expr]  # The weakest precondition
    location: Optional[SourceLocation]  # Where calculation stopped
    reason: str  # Human-readable explanation
    intermediate_steps: List[Tuple[ast.stmt, ast.expr]]  # Steps taken


class WeakestPreconditionCalculator:
    """Implements Dijkstra's weakest precondition calculus."""

    def __init__(self, parsed_code: ParsedCode):
        self.parsed_code = parsed_code
        self.traverser = ASTTraverser(parsed_code)
        self.source_map = parsed_code.source_map

        # State tracking
        self.current_substitutions: Dict[str, ast.expr] = {}
        self.calculation_steps: List[Tuple[ast.stmt, ast.expr]] = []

    def calculate_weakest_precondition(
        self, assertion: ast.Assert, max_steps: int = 50
    ) -> WPResult:
        """Calculate the weakest precondition for an assertion."""

        # Reset state
        self.current_substitutions = {}
        self.calculation_steps = []

        try:
            # Start with the assertion condition
            current_condition = assertion.test
            current_location = self.source_map.get(assertion)

            # Get statements that come before this assertion in the same function
            containing_func = self.traverser.get_function_containing_node(assertion)
            if not containing_func:
                return WPResult(
                    PropagationResult.BLOCKED,
                    current_condition,
                    current_location,
                    "Assertion not contained in a function",
                    [],
                )

            preceding_statements = self.traverser.get_statements_before_node(assertion)

            # Process statements backward
            for stmt in reversed(preceding_statements):
                if len(self.calculation_steps) >= max_steps:
                    return WPResult(
                        PropagationResult.BLOCKED,
                        current_condition,
                        self.source_map.get(stmt),
                        f"Maximum steps ({max_steps}) reached",
                        self.calculation_steps,
                    )

                # Try to propagate backward through this statement
                propagation_result = self._propagate_through_statement(
                    current_condition, stmt
                )

                if propagation_result.result == PropagationResult.SUCCESS:
                    if propagation_result.condition is not None:
                        current_condition = propagation_result.condition
                        current_location = propagation_result.location
                        self.calculation_steps.append((stmt, current_condition))

                elif propagation_result.result == PropagationResult.BLOCKED:
                    return WPResult(
                        PropagationResult.BLOCKED,
                        current_condition,
                        propagation_result.location or self.source_map.get(stmt),
                        f"Blocked by impure statement: {propagation_result.reason}",
                        self.calculation_steps,
                    )

                else:
                    return propagation_result

            # Successfully propagated through all statements
            return WPResult(
                PropagationResult.SUCCESS,
                current_condition,
                current_location,
                "Successfully calculated weakest precondition",
                self.calculation_steps,
            )

        except Exception as e:
            return WPResult(
                PropagationResult.ERROR,
                None,
                None,
                f"Calculation error: {str(e)}",
                self.calculation_steps,
            )

    def _propagate_through_statement(
        self, condition: ast.expr, statement: ast.stmt
    ) -> WPResult:
        """Propagate a condition backward through a single statement."""

        stmt_location = self.source_map.get(statement)

        # Handle different statement types
        if isinstance(statement, ast.Assign):
            return self._propagate_through_assignment(
                condition, statement, stmt_location
            )

        elif isinstance(statement, ast.AugAssign):
            return self._propagate_through_aug_assignment(
                condition, statement, stmt_location
            )

        elif isinstance(statement, ast.Expr):
            # Expression statements (like function calls) - check if pure
            return self._propagate_through_expression_stmt(
                condition, statement, stmt_location
            )

        elif isinstance(statement, ast.Pass):
            # Pass statements don't change anything
            return WPResult(
                PropagationResult.SUCCESS,
                condition,
                stmt_location,
                "Pass statement has no effect",
                [],
            )

        elif isinstance(statement, ast.Assert):
            # Another assertion - we can use it to strengthen our precondition
            return self._propagate_through_assertion(
                condition, statement, stmt_location
            )

        elif isinstance(statement, ast.If):
            # Handle conditional statements with proper weakest precondition semantics
            return self._propagate_through_if_statement(
                condition, statement, stmt_location
            )

        else:
            # All other statement types are considered impure boundaries
            return WPResult(
                PropagationResult.BLOCKED,
                condition,
                stmt_location,
                f"Impure statement type: {type(statement).__name__}",
                [],
            )

    def _propagate_through_assignment(
        self,
        condition: ast.expr,
        assignment: ast.Assign,
        location: Optional[SourceLocation],
    ) -> WPResult:
        """Propagate through an assignment statement."""

        # For now, handle only simple single-target assignments
        if len(assignment.targets) != 1:
            return WPResult(
                PropagationResult.BLOCKED,
                condition,
                location,
                "Multiple assignment targets not supported",
                [],
            )

        target = assignment.targets[0]

        # Only handle simple name assignments (x = expr)
        if not isinstance(target, ast.Name):
            return WPResult(
                PropagationResult.BLOCKED,
                condition,
                location,
                "Complex assignment targets not supported",
                [],
            )

        var_name = target.id
        rhs_expr = assignment.value

        # Check if the RHS is pure - if not, we can't propagate
        # For now, assume it's pure (this would use the purity analyzer in full implementation)

        # Substitute the variable in the condition with the RHS expression
        try:
            substituted_condition = self._substitute_variable(
                condition, var_name, rhs_expr
            )

            return WPResult(
                PropagationResult.SUCCESS,
                substituted_condition,
                location,
                f"Substituted {var_name} with assigned expression",
                [],
            )

        except Exception as e:
            return WPResult(
                PropagationResult.ERROR,
                condition,
                location,
                f"Substitution error: {str(e)}",
                [],
            )

    def _propagate_through_aug_assignment(
        self,
        condition: ast.expr,
        aug_assign: ast.AugAssign,
        location: Optional[SourceLocation],
    ) -> WPResult:
        """Propagate through an augmented assignment (x += y, etc.)."""

        if not isinstance(aug_assign.target, ast.Name):
            return WPResult(
                PropagationResult.BLOCKED,
                condition,
                location,
                "Complex augmented assignment targets not supported",
                [],
            )

        var_name = aug_assign.target.id

        # Convert augmented assignment to regular assignment
        # x += y becomes x = x + y
        bin_op = ast.BinOp(
            left=ast.Name(id=var_name, ctx=ast.Load()),
            op=aug_assign.op,
            right=aug_assign.value,
        )

        # Create equivalent regular assignment
        equivalent_assign = ast.Assign(
            targets=[ast.Name(id=var_name, ctx=ast.Store())], value=bin_op
        )

        return self._propagate_through_assignment(
            condition, equivalent_assign, location
        )

    def _propagate_through_expression_stmt(
        self,
        condition: ast.expr,
        expr_stmt: ast.Expr,
        location: Optional[SourceLocation],
    ) -> WPResult:
        """Propagate through an expression statement."""

        # Expression statements should have no side effects to be passable
        # For now, we'll be conservative and block on most expression statements
        # except for certain known-pure cases

        expr = expr_stmt.value

        # Allow certain pure expressions to pass through
        if isinstance(expr, (ast.Constant, ast.Num, ast.Str, ast.NameConstant)):
            return WPResult(
                PropagationResult.SUCCESS,
                condition,
                location,
                "Pure literal expression has no effect",
                [],
            )

        # Block on function calls and other potentially side-effecting expressions
        else:
            return WPResult(
                PropagationResult.BLOCKED,
                condition,
                location,
                "Expression statement may have side effects",
                [],
            )

    def _propagate_through_assertion(
        self,
        condition: ast.expr,
        assertion: ast.Assert,
        location: Optional[SourceLocation],
    ) -> WPResult:
        """Propagate through another assertion - strengthen the precondition."""

        # The assertion provides additional information we can use
        # The weakest precondition becomes: assertion.test AND condition

        combined_condition = ast.BoolOp(
            op=ast.And(), values=[assertion.test, condition]
        )

        return WPResult(
            PropagationResult.SUCCESS,
            combined_condition,
            location,
            "Combined with preceding assertion",
            [],
        )

    def _substitute_variable(
        self, expr: ast.expr, var_name: str, replacement: ast.expr
    ) -> ast.expr:
        """Substitute all occurrences of a variable with a replacement expression."""

        class VariableSubstitutor(ast.NodeTransformer):
            def __init__(self, var_name: str, replacement: ast.expr):
                self.var_name = var_name
                self.replacement = replacement

            def visit_Name(self, node: ast.Name) -> ast.expr:
                if isinstance(node.ctx, ast.Load) and node.id == self.var_name:
                    # Replace with a copy of the replacement expression
                    return self._copy_node(self.replacement)
                return node

            def _copy_node(self, node: ast.AST) -> ast.expr:
                """Create a deep copy of an AST node."""
                import copy

                return copy.deepcopy(node)  # type: ignore

        substitutor = VariableSubstitutor(var_name, replacement)
        return substitutor.visit(expr)

    def get_calculation_trace(self) -> List[str]:
        """Get a human-readable trace of the calculation steps."""
        trace = []
        for i, (stmt, condition) in enumerate(self.calculation_steps):
            stmt_str = (
                ast.unparse(stmt) if hasattr(ast, "unparse") else f"<statement {i}>"
            )
            condition_str = (
                ast.unparse(condition)
                if hasattr(ast, "unparse")
                else f"<condition {i}>"
            )
            trace.append(f"Step {i + 1}: After {stmt_str} -> {condition_str}")
        return trace

    def condition_to_string(self, condition: ast.expr) -> str:
        """Convert a condition to a readable string."""
        if hasattr(ast, "unparse"):
            return ast.unparse(condition)
        else:
            # Fallback for older Python versions
            return f"<condition at line {getattr(condition, 'lineno', '?')}>"

    def _propagate_through_if_statement(
        self, condition: ast.expr, if_stmt: ast.If, location: Optional["SourceLocation"]
    ) -> WPResult:
        """
        Propagate a condition backward through an if statement.
        
        Implements the standard weakest precondition rule for conditionals:
        wp(if B then S1 else S2, P) = (B ⇒ wp(S1, P)) ∧ (¬B ⇒ wp(S2, P))
        
        This means:
        - If the test condition B holds, then wp(S1, P) must hold  
        - If the test condition B doesn't hold, then wp(S2, P) must hold
        
        Args:
            condition: The postcondition to propagate backward
            if_stmt: The if statement AST node  
            location: Source location for error reporting
            
        Returns:
            WPResult with the calculated weakest precondition
        """
        try:
            test_condition = if_stmt.test
            if_body = if_stmt.body
            else_body = if_stmt.orelse
            
            # Step 1: Calculate wp(if_body, condition) 
            if_wp_result = self._calculate_wp_for_statements(if_body, condition)
            if if_wp_result.result != PropagationResult.SUCCESS:
                return WPResult(
                    if_wp_result.result,
                    condition,
                    location,
                    f"Failed to calculate WP for if branch: {if_wp_result.reason}",
                    self.calculation_steps,
                )
            
            if_wp_condition = if_wp_result.condition
            
            # Step 2: Calculate wp(else_body, condition)
            if else_body:
                else_wp_result = self._calculate_wp_for_statements(else_body, condition)
                if else_wp_result.result != PropagationResult.SUCCESS:
                    return WPResult(
                        else_wp_result.result,
                        condition,  
                        location,
                        f"Failed to calculate WP for else branch: {else_wp_result.reason}",
                        self.calculation_steps,
                    )
                else_wp_condition = else_wp_result.condition
            else:
                # No else clause - the condition must hold when test is false
                else_wp_condition = condition
            
            # Step 3: Construct the combined weakest precondition
            # (test ⇒ wp_if) ∧ (¬test ⇒ wp_else)
            
            # Create test ⇒ wp_if (if test_condition then if_wp_condition)
            if_implication = self._create_implication(test_condition, if_wp_condition)
            
            # Create ¬test ⇒ wp_else (if not test_condition then else_wp_condition) 
            negated_test = self._create_negation(test_condition)
            else_implication = self._create_implication(negated_test, else_wp_condition)
            
            # Combine both implications with conjunction
            combined_condition = self._create_conjunction(if_implication, else_implication)
            
            # Add calculation step
            step_info = f"If statement WP: ({ast.unparse(test_condition) if hasattr(ast, 'unparse') else 'test'} => {ast.unparse(if_wp_condition) if hasattr(ast, 'unparse') else 'if_wp'}) AND (not {ast.unparse(test_condition) if hasattr(ast, 'unparse') else 'test'} => {ast.unparse(else_wp_condition) if hasattr(ast, 'unparse') else 'else_wp'})"
            self.calculation_steps.append(step_info)
            
            return WPResult(
                PropagationResult.SUCCESS,
                combined_condition,
                location,
                "Successfully calculated WP for if statement",
                self.calculation_steps,
            )
            
        except Exception as e:
            return WPResult(
                PropagationResult.ERROR,
                condition,
                location,
                f"Error calculating WP for if statement: {str(e)}",
                self.calculation_steps,
            )
    
    def _calculate_wp_for_statements(
        self, statements: List[ast.stmt], condition: ast.expr
    ) -> WPResult:
        """Helper to calculate WP for a list of statements."""
        current_condition = condition
        current_location = None
        
        # Process statements in reverse order
        for stmt in reversed(statements):
            result = self._propagate_through_statement(current_condition, stmt)
            if result.result != PropagationResult.SUCCESS:
                return result
            current_condition = result.condition
            current_location = result.location
            
        return WPResult(
            PropagationResult.SUCCESS,
            current_condition,
            current_location,
            "Successfully processed statement list",
            [],
        )
    
    def _create_implication(self, antecedent: ast.expr, consequent: ast.expr) -> ast.expr:
        """Create an implication: antecedent ⇒ consequent (equivalent to ¬antecedent ∨ consequent)."""
        # Create: (not antecedent) or consequent 
        negated_antecedent = self._create_negation(antecedent)
        return ast.BoolOp(op=ast.Or(), values=[negated_antecedent, consequent])
    
    def _create_negation(self, expr: ast.expr) -> ast.expr:
        """Create a negation: ¬expr."""
        return ast.UnaryOp(op=ast.Not(), operand=expr)
    
    def _create_conjunction(self, left: ast.expr, right: ast.expr) -> ast.expr:
        """Create a conjunction: left ∧ right."""
        return ast.BoolOp(op=ast.And(), values=[left, right])


class RecursiveWPCalculator(WeakestPreconditionCalculator):
    """Extended WP calculator that handles recursive functions."""

    def __init__(self, parsed_code: ParsedCode):
        super().__init__(parsed_code)
        self.recursive_calls: Set[str] = set()
        self.termination_measures: Dict[str, List[ast.expr]] = {}

    def analyze_recursive_function(
        self, func: ast.FunctionDef, postcondition: ast.expr
    ) -> WPResult:
        """Analyze a recursive function with termination measures."""

        # This is a placeholder for recursive analysis
        # Full implementation would:
        # 1. Identify recursive calls
        # 2. Find termination measures
        # 3. Apply structural induction
        # 4. Verify termination

        return WPResult(
            PropagationResult.BLOCKED,
            postcondition,
            self.source_map.get(func),
            "Recursive function analysis not yet implemented",
            [],
        )
