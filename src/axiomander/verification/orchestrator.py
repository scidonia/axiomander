"""
Verification Orchestrator

This module provides the main orchestrator that connects all pipeline components
for Z3-based formal verification of Python functions with contracts.

The orchestrator coordinates:
- AST parsing and analysis
- Assertion discovery and classification
- Purity analysis
- Weakest precondition calculation
- SMT translation and Z3 solving
- Result reporting
"""

import ast
import logging
from typing import Dict, List, Optional, Tuple, Any, Union
from dataclasses import dataclass
from pathlib import Path

from ..ast.parser import ASTParser, ParsedCode
from ..ast.assertion_finder import AssertionFinder, AssertionInfo, AssertionType
from ..ast.purity_analyzer import PurityAnalyzer
from ..logic.weakest_precondition import WeakestPreconditionCalculator
from ..logic.smt_translator import SMTTranslator, VariableType


logger = logging.getLogger(__name__)


@dataclass
class VerificationResult:
    """Results of verification for a single function."""

    function_name: str
    file_path: str
    success: bool
    verified_assertions: List[str]
    failed_assertions: List[str]
    counterexamples: List[Dict[str, Any]]
    errors: List[str]
    execution_time: float


class VerificationOrchestrator:
    """
    Main orchestrator for verification operations.

    Coordinates the parsing, constraint analysis, and verification of Python functions
    using SMT solvers and contracts.
    """

    def __init__(
        self,
        parser: Optional[ASTParser] = None,
        smt_translator: Optional[SMTTranslator] = None,
    ):
        self.parser = parser or ASTParser()
        self.smt_translator = smt_translator or SMTTranslator()

        # Add constraint accumulation for Z3 dumps
        self._accumulated_constraints = []
        self._accumulated_variables = {}

    def _accumulate_constraints_from_current_context(self, function_name: str):
        """
        Accumulate constraints and variables from current SMT translator context.

        Args:
            function_name: Name of the function being processed
        """
        try:
            # Get current constraints and variables
            current_constraints = self.smt_translator.get_solver_assertions()
            current_variables = self.smt_translator.get_variable_summary()

            # Add function context to constraints
            if current_constraints:
                function_constraints = []
                for constraint in current_constraints:
                    function_constraints.append(f"; Function: {function_name}")
                    function_constraints.append(f"(assert {constraint})")
                self._accumulated_constraints.extend(function_constraints)

            # Merge variables (with function prefix to avoid conflicts)
            for var_name, var_info in current_variables.items():
                prefixed_name = f"{function_name}_{var_name}"
                self._accumulated_variables[prefixed_name] = var_info

        except Exception as e:
            logger.warning(f"Failed to accumulate constraints for {function_name}: {e}")

    def clear_accumulated_constraints(self):
        """Clear all accumulated constraints and variables."""
        self._accumulated_constraints.clear()
        self._accumulated_variables.clear()

    def verify_file(self, file_path: Union[str, Path]) -> List[VerificationResult]:
        """
        Verify all functions in a Python file.

        Args:
            file_path: Path to the Python source file to verify

        Returns:
            List of verification results, one per function
        """
        # Clear previous accumulated constraints for new file
        self.clear_accumulated_constraints()

        file_path = Path(file_path)

        try:
            source_code = file_path.read_text()
        except Exception as e:
            logger.error(f"Failed to read file {file_path}: {e}")
            return []

        return self.verify_source(source_code, str(file_path))

    def verify_source(
        self, source_code: str, file_path: str = "<string>"
    ) -> List[VerificationResult]:
        """
        Verify all functions in Python source code.

        Args:
            source_code: Python source code to verify
            file_path: Optional file path for error reporting

        Returns:
            List of verification results for each function
        """
        results = []

        try:
            # Parse the source code
            parsed_code = self.parser.parse_source(source_code, file_path)
            if not parsed_code or not parsed_code.ast_tree:
                logger.error(f"Failed to parse source code from {file_path}")
                return []

        except Exception as e:
            logger.error(f"Parse error in {file_path}: {e}")
            return []

        # Find all function definitions
        for node in ast.walk(parsed_code.ast_tree):
            if isinstance(node, ast.FunctionDef):
                result = self.verify_function(parsed_code, node)
                results.append(result)

        return results

    def verify_function(
        self, parsed_code: ParsedCode, function_node: ast.FunctionDef
    ) -> VerificationResult:
        """
        Verify a single function using the complete pipeline.

        Args:
            parsed_code: Parsed source code container
            function_node: AST node of the function to verify

        Returns:
            Verification result for the function
        """
        import time

        start_time = time.time()

        function_name = function_node.name
        logger.info(f"Verifying function {function_name} in {parsed_code.file_path}")

        result = VerificationResult(
            function_name=function_name,
            file_path=parsed_code.file_path,
            success=False,
            verified_assertions=[],
            failed_assertions=[],
            counterexamples=[],
            errors=[],
            execution_time=0.0,
        )

        try:
            # Step 1: Discover assertions in the function
            assertion_finder = AssertionFinder(parsed_code)
            assertions = assertion_finder.find_all_assertions()

            # Filter assertions for this function
            function_assertions = [
                assertion
                for assertion in assertions
                if assertion.containing_function == function_node
            ]

            if not function_assertions:
                logger.warning(f"No assertions found in function {function_name}")
                result.success = True  # Nothing to verify is considered success
                return result

            logger.debug(
                f"Found {len(function_assertions)} assertions in {function_name}"
            )

            # Step 2: Analyze purity of the function
            purity_analyzer = PurityAnalyzer(parsed_code)
            purity_result = purity_analyzer.analyze_function(function_node)
            is_pure = (
                purity_result.level.name == "PURE"
            )  # Assuming PurityLevel has PURE

            if not is_pure:
                logger.warning(
                    f"Function {function_name} is not pure - limited verification available"
                )

            # Step 3: Setup SMT translator with function context
            self.smt_translator.reset()
            self.smt_translator.add_type_hints_from_function(function_node)

            # Add function parameters as variables
            for arg in function_node.args.args:
                var_type = (
                    self._infer_type_from_annotation(arg.annotation)
                    if arg.annotation
                    else VariableType.INT
                )
                self.smt_translator.get_or_create_variable(arg.arg, var_type)

            # Step 4.5: Model simple assignments as constraints
            try:
                self._add_assignment_constraints(function_node)
            except Exception as e:
                logger.debug(f"Could not model assignments: {e}")

            verification_count = 0

            # Step 4: Separate preconditions from postconditions and group consecutive preconditions
            preconditions, postconditions, other_assertions = (
                self._classify_and_group_assertions(function_assertions, function_node)
            )
            postconditions = [
                a
                for a in function_assertions
                if a.assertion_type == AssertionType.POSTCONDITION
            ]
            other_assertions = [
                a
                for a in function_assertions
                if a.assertion_type
                not in [AssertionType.PRECONDITION, AssertionType.POSTCONDITION]
            ]

            # Step 5: Add preconditions as assumptions to the solver
            precondition_constraints = []
            for precondition_info in preconditions:
                try:
                    z3_constraint = self.smt_translator.translate_assertion(
                        precondition_info.node
                    )
                    self.smt_translator.add_constraint(z3_constraint)
                    precondition_constraints.append(z3_constraint)

                    # Mark preconditions as verified (they are assumptions)
                    assertion_desc = f"{precondition_info.assertion_type.value}: {ast.unparse(precondition_info.node.test)}"
                    result.verified_assertions.append(assertion_desc)
                    verification_count += 1
                    logger.debug(f"Added precondition as assumption: {assertion_desc}")

                except Exception as e:
                    error_msg = f"Failed to process precondition: {e}"
                    logger.error(error_msg)
                    result.errors.append(error_msg)

            # Step 6: Verify postconditions given the precondition assumptions
            for postcondition_info in postconditions:
                try:
                    z3_constraint = self.smt_translator.translate_assertion(
                        postcondition_info.node
                    )

                    # Try to find a counterexample where preconditions hold but postcondition fails
                    has_counterexample, counterexample = (
                        self.smt_translator.find_counterexample(z3_constraint)
                    )

                    assertion_desc = f"{postcondition_info.assertion_type.value}: {ast.unparse(postcondition_info.node.test)}"

                    if not has_counterexample:
                        # No counterexample means postcondition is valid given preconditions
                        result.verified_assertions.append(assertion_desc)
                        verification_count += 1
                        logger.debug(f"Verified postcondition: {assertion_desc}")
                    else:
                        # Counterexample found - postcondition can fail even with preconditions
                        result.failed_assertions.append(assertion_desc)

                        if counterexample:
                            result.counterexamples.append(
                                {
                                    "assertion": assertion_desc,
                                    "counterexample": counterexample,
                                }
                            )
                            logger.debug(
                                f"Found counterexample for postcondition: {assertion_desc}"
                            )

                except Exception as e:
                    error_msg = f"SMT verification failed for postcondition: {e}"
                    logger.error(error_msg)
                    result.errors.append(error_msg)

            # Step 7: Verify other assertions (without precondition assumptions)
            # Reset solver to remove precondition assumptions for other assertions
            if other_assertions:
                self.smt_translator.reset()
                self.smt_translator.add_type_hints_from_function(function_node)

                # Re-add function parameters
                for arg in function_node.args.args:
                    var_type = (
                        self._infer_type_from_annotation(arg.annotation)
                        if arg.annotation
                        else VariableType.INT
                    )
                    self.smt_translator.get_or_create_variable(arg.arg, var_type)

                for assertion_info in other_assertions:
                    try:
                        z3_constraint = self.smt_translator.translate_assertion(
                            assertion_info.node
                        )
                        has_counterexample, counterexample = (
                            self.smt_translator.find_counterexample(z3_constraint)
                        )

                        assertion_desc = f"{assertion_info.assertion_type.value}: {ast.unparse(assertion_info.node.test)}"

                        if not has_counterexample:
                            result.verified_assertions.append(assertion_desc)
                            verification_count += 1
                            logger.debug(f"Verified assertion: {assertion_desc}")
                        else:
                            result.failed_assertions.append(assertion_desc)
                            if counterexample:
                                result.counterexamples.append(
                                    {
                                        "assertion": assertion_desc,
                                        "counterexample": counterexample,
                                    }
                                )
                                logger.debug(
                                    f"Found counterexample for assertion: {assertion_desc}"
                                )

                    except Exception as e:
                        error_msg = f"SMT verification failed for assertion: {e}"
                        logger.error(error_msg)
                        result.errors.append(error_msg)

            result.success = (
                len(result.errors) == 0 and len(result.failed_assertions) == 0
            )  # Success if no errors and no failed assertions
            logger.info(
                f"Z3 verification complete for {function_name}: {verification_count} verified, {len(result.failed_assertions)} failed"
            )

        except Exception as e:
            logger.error(f"Verification failed for {function_name}: {e}")
            result.errors.append(str(e))

        finally:
            result.execution_time = time.time() - start_time
            # Accumulate constraints before returning for potential Z3 dump
            self._accumulate_constraints_from_current_context(function_name)

        return result

    def _infer_type_from_annotation(self, annotation: ast.expr) -> VariableType:
        """Infer variable type from type annotation."""
        if isinstance(annotation, ast.Name):
            type_name = annotation.id
            if type_name == "int":
                return VariableType.INT
            elif type_name == "float":
                return VariableType.REAL
            elif type_name == "bool":
                return VariableType.BOOL
            elif type_name == "str":
                return VariableType.STRING

        # Default to int for unknown types
        return VariableType.INT

    def _add_assignment_constraints(self, function_node: ast.FunctionDef):
        """Add constraints for simple variable assignments."""
        for node in ast.walk(function_node):
            if isinstance(node, ast.Assign):
                # Handle simple assignments like result = x or result = x + 1
                if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
                    target_name = node.targets[0].id

                    # Create variable if it doesn't exist
                    target_var = self.smt_translator.get_or_create_variable(target_name)

                    try:
                        # Translate the value expression
                        value_expr = self.smt_translator.translate_expression(
                            node.value
                        )

                        # Add constraint: target == value
                        import z3

                        constraint = target_var.z3_var == value_expr
                        self.smt_translator.add_constraint(constraint)

                        logger.debug(
                            f"Added assignment constraint: {target_name} == {ast.unparse(node.value)}"
                        )

                    except Exception as e:
                        # If we can't translate the assignment, skip it
                        logger.debug(
                            f"Could not translate assignment {target_name} = {ast.unparse(node.value)}: {e}"
                        )
                        pass

    def _classify_and_group_assertions(self, function_assertions, function_node):
        """
        Classify assertions and group consecutive preconditions at function start.

        Returns:
            Tuple of (preconditions, postconditions, other_assertions)
        """
        from ..ast.assertion_finder import AssertionType

        # Sort assertions by their line number in the function
        sorted_assertions = sorted(
            function_assertions, key=lambda a: a.location.line if a.location else 0
        )

        preconditions = []
        postconditions = []
        other_assertions = []

        # Find consecutive assertions at the beginning of the function
        function_start_line = (
            function_node.lineno if hasattr(function_node, "lineno") else 0
        )

        consecutive_start_assertions = []
        for i, assertion_info in enumerate(sorted_assertions):
            if assertion_info.location:
                # Check if this assertion is near the function start and consecutive
                is_near_start = (
                    assertion_info.location.line - function_start_line <= 10
                )  # Within first 10 lines

                if is_near_start and (
                    not consecutive_start_assertions
                    or assertion_info.location.line
                    - consecutive_start_assertions[-1].location.line
                    <= 2
                ):
                    # This assertion is consecutive with previous ones at function start
                    consecutive_start_assertions.append(assertion_info)
                else:
                    # No longer consecutive at start
                    break

        # Classify the consecutive start assertions as preconditions
        logger.debug(
            f"Found {len(consecutive_start_assertions)} consecutive assertions at function start"
        )
        for assertion_info in consecutive_start_assertions:
            # Override classification - treat as precondition if at function start
            preconditions.append(assertion_info)
            logger.debug(
                f"Grouped as precondition: {ast.unparse(assertion_info.node.test)} (originally {assertion_info.assertion_type.value})"
            )

        # Classify remaining assertions (excluding those already classified as preconditions)
        remaining_assertions = sorted_assertions[len(consecutive_start_assertions) :]
        for assertion_info in remaining_assertions:
            if assertion_info.assertion_type == AssertionType.POSTCONDITION:
                postconditions.append(assertion_info)
            elif assertion_info.assertion_type == AssertionType.PRECONDITION:
                # Don't double-count preconditions already grouped at start
                if assertion_info not in preconditions:
                    preconditions.append(assertion_info)
            else:
                # Only add to other_assertions if not already a precondition
                if assertion_info not in preconditions:
                    other_assertions.append(assertion_info)

        return preconditions, postconditions, other_assertions

    def dump_z3_constraints(self, file_path: Optional[str] = None):
        """
        Dump accumulated Z3 constraints from all functions to a file or return as string.

        Args:
            file_path: Optional file path to write constraints. If None, returns string.

        Returns:
            String representation of constraints if file_path is None
        """
        try:
            output_lines = []
            output_lines.append("; Z3 Constraints Dump")
            output_lines.append(
                f"; Generated at: {__import__('datetime').datetime.now()}"
            )
            output_lines.append("")

            # Variable declarations in proper SMT-LIB format
            if self._accumulated_variables:
                output_lines.append("; Variable declarations:")
                for var_name, var_info in self._accumulated_variables.items():
                    # Convert variable type to SMT-LIB type
                    if "int" in str(var_info).lower():
                        smt_type = "Int"
                    elif (
                        "real" in str(var_info).lower()
                        or "float" in str(var_info).lower()
                    ):
                        smt_type = "Real"
                    elif "bool" in str(var_info).lower():
                        smt_type = "Bool"
                    else:
                        smt_type = "Int"  # Default

                    output_lines.append(f"(declare-const {var_name} {smt_type})")
                output_lines.append("")
            else:
                output_lines.append("; No variables found")
                output_lines.append("")

            # Constraints from all functions
            if self._accumulated_constraints:
                output_lines.append("; Constraints from all functions:")
                output_lines.extend(self._accumulated_constraints)
                output_lines.append("")
            else:
                output_lines.append("; No constraints accumulated")
                output_lines.append("")

            # Check satisfiability
            output_lines.append("; Check satisfiability")
            output_lines.append("(check-sat)")
            output_lines.append("(get-model)")

            result = "\n".join(output_lines)

            if file_path:
                with open(file_path, "w") as f:
                    f.write(result)
                logger.info(f"Z3 constraints dumped to {file_path}")
                return None
            else:
                return result

        except Exception as e:
            logger.error(f"Failed to dump Z3 constraints: {e}")
            return f"; Error generating dump: {e}" if not file_path else None


def create_orchestrator() -> VerificationOrchestrator:
    """Factory function to create a verification orchestrator."""
    return VerificationOrchestrator()
