"""
AST parser and traversal utilities for axiomander.

This module provides enhanced Python AST parsing capabilities with
source location tracking and specialized traversal methods.
"""

import ast
from typing import Dict, List, Optional, Set, Union, Any, Iterator, cast
from pathlib import Path
from dataclasses import dataclass


@dataclass
class SourceLocation:
    """Represents a location in source code."""

    file: str
    line: int
    column: int
    end_line: Optional[int] = None
    end_column: Optional[int] = None

    def __str__(self) -> str:
        if self.end_line and self.end_column:
            return f"{self.file}:{self.line}:{self.column}-{self.end_line}:{self.end_column}"
        return f"{self.file}:{self.line}:{self.column}"


@dataclass
class ParsedCode:
    """Container for parsed Python code with metadata."""

    ast_tree: ast.AST
    source_code: str
    file_path: str
    source_map: Dict[ast.AST, SourceLocation]


class ASTParser:
    """Enhanced AST parser with source location tracking."""

    def __init__(self):
        self.source_map: Dict[ast.AST, SourceLocation] = {}

    def parse_file(self, file_path: Union[str, Path]) -> ParsedCode:
        """Parse a Python file and return enhanced AST."""
        file_path = str(file_path)

        with open(file_path, "r", encoding="utf-8") as f:
            source_code = f.read()

        return self.parse_source(source_code, file_path)

    def parse_source(self, source_code: str, file_path: str = "<string>") -> ParsedCode:
        """Parse Python source code and return enhanced AST."""
        try:
            tree = ast.parse(source_code, filename=file_path)
        except SyntaxError as e:
            raise ValueError(f"Syntax error in {file_path}: {e}")

        # Build source location mapping
        source_map = self._build_source_map(tree, file_path)

        return ParsedCode(
            ast_tree=tree,
            source_code=source_code,
            file_path=file_path,
            source_map=source_map,
        )

    def _build_source_map(
        self, tree: ast.AST, file_path: str
    ) -> Dict[ast.AST, SourceLocation]:
        """Build mapping from AST nodes to source locations."""
        source_map = {}

        for node in ast.walk(tree):
            # Only stmt and expr nodes have line number information
            if hasattr(node, "lineno") and hasattr(node, "col_offset"):
                lineno = getattr(node, "lineno", 0)
                col_offset = getattr(node, "col_offset", 0)
                end_line = getattr(node, "end_lineno", None)
                end_column = getattr(node, "end_col_offset", None)

                source_map[node] = SourceLocation(
                    file=file_path,
                    line=lineno,
                    column=col_offset,
                    end_line=end_line,
                    end_column=end_column,
                )

        return source_map


class ASTTraverser:
    """Specialized AST traversal with visitor patterns."""

    def __init__(self, parsed_code: ParsedCode):
        self.parsed_code = parsed_code
        self.tree = parsed_code.ast_tree
        self.source_map = parsed_code.source_map

    def find_nodes_by_type(self, node_type: type) -> List[ast.AST]:
        """Find all nodes of a specific type."""
        return [node for node in ast.walk(self.tree) if isinstance(node, node_type)]

    def find_functions(self) -> List[ast.FunctionDef]:
        """Find all function definitions."""
        return [
            node for node in ast.walk(self.tree) if isinstance(node, ast.FunctionDef)
        ]

    def find_classes(self) -> List[ast.ClassDef]:
        """Find all class definitions."""
        return [node for node in ast.walk(self.tree) if isinstance(node, ast.ClassDef)]

    def find_assertions(self) -> List[ast.Assert]:
        """Find all assert statements."""
        return [node for node in ast.walk(self.tree) if isinstance(node, ast.Assert)]

    def get_function_containing_node(self, node: ast.AST) -> Optional[ast.FunctionDef]:
        """Find the function definition that contains the given node."""
        functions = self.find_functions()

        for func in functions:
            if self._node_contains(func, node):
                return func
        return None

    def get_statements_before_node(self, target_node: ast.AST) -> List[ast.stmt]:
        """Get all statements that come before the target node in the same scope."""
        containing_func = self.get_function_containing_node(target_node)
        if not containing_func:
            return []

        statements = []
        target_line = self.source_map.get(target_node, SourceLocation("", 0, 0)).line

        for stmt in containing_func.body:
            stmt_location = self.source_map.get(stmt)
            if stmt_location and stmt_location.line < target_line:
                statements.append(stmt)

        return statements

    def _node_contains(self, container: ast.AST, contained: ast.AST) -> bool:
        """Check if one AST node contains another."""
        container_loc = self.source_map.get(container)
        contained_loc = self.source_map.get(contained)

        if not container_loc or not contained_loc:
            return False

        # Check if contained node is within container's line range
        container_end = container_loc.end_line or container_loc.line
        return container_loc.line <= contained_loc.line <= container_end

    def get_source_text(self, node: ast.AST) -> str:
        """Get the source text for a given AST node."""
        location = self.source_map.get(node)
        if not location:
            return ""

        lines = self.parsed_code.source_code.splitlines()
        if location.end_line and location.end_line != location.line:
            # Multi-line node
            result_lines = []
            for i in range(location.line - 1, min(location.end_line, len(lines))):
                line = lines[i]
                if i == location.line - 1:
                    # First line - start from column
                    line = line[location.column :]
                if i == location.end_line - 1 and location.end_column:
                    # Last line - end at column
                    line = line[
                        : location.end_column
                        - (location.column if i == location.line - 1 else 0)
                    ]
                result_lines.append(line)
            return "\n".join(result_lines)
        else:
            # Single line
            if location.line <= len(lines):
                line = lines[location.line - 1]
                start_col = location.column
                end_col = location.end_column if location.end_column else len(line)
                return line[start_col:end_col]

        return ""


class ASTVisitor(ast.NodeVisitor):
    """Base visitor class with source location tracking."""

    def __init__(self, parsed_code: ParsedCode):
        self.parsed_code = parsed_code
        self.source_map = parsed_code.source_map
        self.results: List[Any] = []

    def get_location(self, node: ast.AST) -> Optional[SourceLocation]:
        """Get source location for a node."""
        return self.source_map.get(node)

    def visit(self, node: ast.AST) -> Any:
        """Visit a node with location context."""
        return super().visit(node)
