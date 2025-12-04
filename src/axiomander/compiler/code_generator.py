"""Code generation for compiled components."""

import re
from pathlib import Path
from typing import Dict, List, Optional, Set

from ..storage.models import Component
from .models import CompilerConfig, ComponentMapping


class CodeGenerator:
    """Generates Python code files from components."""
    
    def __init__(self, config: CompilerConfig, storage_manager=None):
        """Initialize with compiler configuration.
        
        Args:
            config: Compiler configuration settings
            storage_manager: Optional storage manager for loading component files
        """
        self.config = config
        self.storage_manager = storage_manager
    
    def generate_implementation_file(
        self,
        component: Component,
        mapping: ComponentMapping,
        all_mappings: Dict[str, ComponentMapping],
        all_components: Dict[str, Component]
    ) -> str:
        """Generate the implementation Python file for a component.
        
        Args:
            component: Component to generate code for
            mapping: Component mapping with uniquified name
            all_mappings: All component mappings for import resolution
            all_components: All components for dependency lookup
            
        Returns:
            Generated Python code as string
        """
        lines = []
        
        # Add UID tracking comment
        lines.append(f"# axiomander:component:{component.uid}")
        lines.append("")
        
        # Add module docstring if in development mode
        if self.config.mode.value == "development" and self.config.preserve_metadata:
            lines.append(f'"""Component: {component.name}')
            if component.description:
                lines.append(f"{component.description}")
            lines.append(f"Original UID: {component.uid}")
            lines.append('"""')
            lines.append("")
        
        # Add contract checking infrastructure
        if self.config.include_contracts:
            lines.extend(self._generate_contract_infrastructure())
            lines.append("")
        
        # Generate imports
        import_lines = self._generate_imports(component, mapping, all_mappings, all_components)
        lines.extend(import_lines)
        
        if import_lines:
            lines.append("")
        
        # Load and process implementation code with contract decorators
        impl_code = self._load_component_file(component.uid, "implementation.py")
        if impl_code:
            processed_code = self._add_contract_decorators(impl_code, component, mapping)
            lines.append(processed_code)
        
        return "\n".join(lines)
    
    def generate_logical_file(self, component: Component, mapping: ComponentMapping) -> str:
        """Generate the logical contracts file for a component.
        
        Args:
            component: Component to generate code for
            mapping: Component mapping with uniquified name
            
        Returns:
            Generated Python code as string
        """
        lines = []
        
        # Add UID tracking comment
        lines.append(f"# axiomander:component:{component.uid}")
        lines.append("")
        
        # Add module docstring if in development mode
        if self.config.mode.value == "development" and self.config.preserve_metadata:
            lines.append(f'"""Logical contracts for component: {component.name}')
            if component.description:
                lines.append(f"{component.description}")
            lines.append(f"Original UID: {component.uid}")
            lines.append('"""')
            lines.append("")
        
        # Load and add logical code
        logical_code = self._load_component_file(component.uid, "logical.py")
        if logical_code:
            lines.append(logical_code)
        
        return "\n".join(lines)
    
    def generate_test_file(
        self, 
        component: Component, 
        mapping: ComponentMapping, 
        module_name: str
    ) -> str:
        """Generate the test file for a component.
        
        Args:
            component: Component to generate code for
            mapping: Component mapping with uniquified name
            module_name: Name of the compiled module
            
        Returns:
            Generated Python code as string
        """
        lines = []
        
        # Add UID tracking comment
        lines.append(f"# axiomander:component:{component.uid}")
        lines.append("")
        
        # Add module docstring
        lines.append(f'"""Tests for component: {component.name}"""')
        lines.append("")
        
        # Generate test imports
        path_prefix = ""
        if mapping.path:
            path_parts = mapping.path.split("/")
            path_prefix = "." + ".".join(path_parts) + "."
        else:
            path_prefix = "."
        
        lines.append(f"from src.{module_name}{path_prefix}{mapping.uniquified_name} import *")
        lines.append(f"from src.{module_name}{path_prefix}{mapping.uniquified_name}_logical import *")
        lines.append("")
        
        # Standard test imports
        lines.append("import pytest")
        lines.append("import unittest")
        lines.append("from hypothesis import given, strategies as st")
        lines.append("")
        
        # Load and add test code
        test_code = self._load_component_file(component.uid, "test.py")
        if test_code:
            lines.append(test_code)
        
        return "\n".join(lines)
    
    def generate_module_init(
        self,
        components: Dict[str, Component],
        mappings: Dict[str, ComponentMapping],
        module_name: str,
        entry_point_uid: str
    ) -> str:
        """Generate the module __init__.py file.
        
        Args:
            components: All components in the module
            mappings: Component mappings
            module_name: Name of the module
            entry_point_uid: UID of the entry point component
            
        Returns:
            Generated Python code as string
        """
        lines = []
        
        # Module docstring
        lines.append(f'"""Generated module: {module_name}')
        lines.append("")
        lines.append("This module was automatically generated by Axiomander.")
        if self.config.preserve_metadata:
            lines.append(f"Entry point: {components[entry_point_uid].name}")
            lines.append(f"Components: {len(components)}")
        lines.append('"""')
        lines.append("")
        
        # Import all public components
        imports = []
        exports = []
        
        for uid, component in components.items():
            mapping = mappings[uid]
            
            if mapping.path:
                path_parts = mapping.path.split("/")
                import_path = ".".join(path_parts) + f".{mapping.uniquified_name}"
            else:
                import_path = f"{mapping.uniquified_name}"
            
            # Import main symbols from the component
            imports.append(f"from .{import_path} import *")
            exports.append(f'"{component.name}"')
        
        lines.extend(imports)
        lines.append("")
        
        # __all__ export list
        lines.append("__all__ = [")
        for export in exports:
            lines.append(f"    {export},")
        lines.append("]")
        lines.append("")
        
        # Add a main function that can be called from main.py
        entry_mapping = mappings[entry_point_uid]
        lines.append("def main():")
        lines.append(f'    """Main entry point for the {module_name} module."""')
        lines.append(f"    # Example usage of {components[entry_point_uid].name}")
        lines.append(f"    result = {components[entry_point_uid].name}(5)")
        lines.append("    print(f'Result: {result}')")
        lines.append("    return result")
        
        return "\n".join(lines)
    
    def generate_main_file(
        self,
        entry_component: Component,
        entry_mapping: ComponentMapping,
        all_mappings: Dict[str, ComponentMapping],
        all_components: Dict[str, Component]
    ) -> str:
        """Generate the main.py file for the module.
        
        Args:
            entry_component: Entry point component
            entry_mapping: Entry point component mapping
            all_mappings: All component mappings
            all_components: All components
            
        Returns:
            Generated Python code as string
        """
        lines = []
        
        # Module docstring
        lines.append(f'"""Main entry point for {entry_component.name}"""')
        lines.append("")
        
        # Import the entry point component using absolute import
        # This allows the main.py to be run directly
        lines.append(f"from {entry_mapping.uniquified_name} import *")
        lines.append("")
        
        # Generate main function if appropriate
        lines.append("def main():")
        lines.append(f'    """Main entry point for {entry_component.name}."""')
        lines.append(f"    # Call the main function from {entry_component.name}")
        lines.append(f"    result = {entry_component.name}(5)  # Example call")
        lines.append("    print(f'Result: {result}')")
        lines.append("")
        lines.append("")
        lines.append('if __name__ == "__main__":')
        lines.append("    main()")
        
        return "\n".join(lines)
    
    def _generate_contract_infrastructure(self) -> List[str]:
        """Generate the contract checking infrastructure."""
        lines = []
        
        lines.append("import os")
        lines.append("import functools")
        lines.append("from typing import Callable, Any")
        lines.append("")
        lines.append("# Import Axiomander exceptions")
        lines.append("from axiomander.exceptions import (")
        lines.append("    PreconditionViolationError,")
        lines.append("    PostconditionViolationError,")
        lines.append("    InvariantViolationError,")
        lines.append("    ImplementThisError,")
        lines.append("    DontImplementThisError,")
        lines.append("    UnimplementedError,")
        lines.append("    implement_this,")
        lines.append("    dont_implement_this,")
        lines.append("    unimplemented")
        lines.append(")")
        lines.append("")
        lines.append("# Contract checking can be disabled by setting AXIOMANDER_DISABLE_CONTRACTS=1")
        lines.append("CONTRACTS_ENABLED = os.getenv('AXIOMANDER_DISABLE_CONTRACTS', '0') != '1'")
        lines.append("")
        lines.append("def precondition(contract_text: str, check_func: Callable):")
        lines.append('    """Decorator for precondition contracts."""')
        lines.append("    def decorator(func: Callable) -> Callable:")
        lines.append("        if not CONTRACTS_ENABLED:")
        lines.append("            return func")
        lines.append("        ")
        lines.append("        @functools.wraps(func)")
        lines.append("        def wrapper(*args, **kwargs):")
        lines.append("            if not check_func(*args, **kwargs):")
        lines.append("                raise PreconditionViolationError(func.__name__, contract_text, args, kwargs)")
        lines.append("            return func(*args, **kwargs)")
        lines.append("        ")
        lines.append("        # Add contract text as attribute for introspection")
        lines.append("        wrapper.__precondition__ = contract_text")
        lines.append("        return wrapper")
        lines.append("    return decorator")
        lines.append("")
        lines.append("def postcondition(contract_text: str, check_func: Callable):")
        lines.append('    """Decorator for postcondition contracts."""')
        lines.append("    def decorator(func: Callable) -> Callable:")
        lines.append("        if not CONTRACTS_ENABLED:")
        lines.append("            return func")
        lines.append("        ")
        lines.append("        @functools.wraps(func)")
        lines.append("        def wrapper(*args, **kwargs):")
        lines.append("            result = func(*args, **kwargs)")
        lines.append("            if not check_func(result, *args, **kwargs):")
        lines.append("                raise PostconditionViolationError(func.__name__, contract_text, result, args, kwargs)")
        lines.append("            return result")
        lines.append("        ")
        lines.append("        # Add contract text as attribute for introspection")
        lines.append("        wrapper.__postcondition__ = contract_text")
        lines.append("        return wrapper")
        lines.append("    return decorator")
        lines.append("")
        lines.append("def invariant(contract_text: str, check_func: Callable):")
        lines.append('    """Decorator for class invariant contracts."""')
        lines.append("    def decorator(cls):")
        lines.append("        if not CONTRACTS_ENABLED:")
        lines.append("            return cls")
        lines.append("        ")
        lines.append("        # Store original __init__ and methods")
        lines.append("        original_init = cls.__init__")
        lines.append("        ")
        lines.append("        def check_invariant(self):")
        lines.append("            if not check_func(self):")
        lines.append("                raise InvariantViolationError(cls.__name__, contract_text, self)")
        lines.append("        ")
        lines.append("        def new_init(self, *args, **kwargs):")
        lines.append("            original_init(self, *args, **kwargs)")
        lines.append("            check_invariant(self)")
        lines.append("        ")
        lines.append("        cls.__init__ = new_init")
        lines.append("        cls.__check_invariant__ = check_invariant")
        lines.append("        cls.__invariant__ = contract_text")
        lines.append("        ")
        lines.append("        return cls")
        lines.append("    return decorator")
        
        return lines
    
    def _add_contract_decorators(self, impl_code: str, component: Component, mapping: ComponentMapping) -> str:
        """Add contract decorators to function definitions in implementation code.
        
        Args:
            impl_code: Original implementation code
            component: Component with contract information
            mapping: Component mapping
            
        Returns:
            Implementation code with contract decorators added
        """
        if not self.config.include_contracts:
            return impl_code
        
        lines = impl_code.split('\n')
        processed_lines = []
        
        for i, line in enumerate(lines):
            # Look for function definitions
            if line.strip().startswith('def ') and ':' in line:
                # Extract function name
                func_def = line.strip()
                func_name_start = func_def.find('def ') + 4
                func_name_end = func_def.find('(')
                if func_name_end > func_name_start:
                    func_name = func_def[func_name_start:func_name_end].strip()
                    
                    # Add contract decorators before function definition
                    indent = len(line) - len(line.lstrip())
                    decorator_lines = self._generate_contract_decorator(component, func_name)
                    if decorator_lines:
                        for decorator_line in decorator_lines.split('\n'):
                            if decorator_line.strip():
                                processed_lines.append(' ' * indent + decorator_line)
            
            processed_lines.append(line)
        
        return '\n'.join(processed_lines)
    
    def _generate_contract_decorator(self, component: Component, func_name: str) -> str:
        """Generate contract decorators for a specific function.
        
        Args:
            component: Component with contract information
            func_name: Name of the function to decorate
            
        Returns:
            Contract decorator strings (may be multiple lines)
        """
        decorators = []
        
        # Add precondition decorator if present
        if component.precondition and component.pre_contract:
            pre_text = component.pre_contract.replace('"', '\\"')  # Escape quotes
            decorators.append(f'@precondition("{pre_text}", {component.precondition})')
        
        # Add postcondition decorator if present  
        if component.postcondition and component.post_contract:
            post_text = component.post_contract.replace('"', '\\"')  # Escape quotes
            decorators.append(f'@postcondition("{post_text}", {component.postcondition})')
        
        return '\n'.join(decorators) if decorators else ""
    
    def _generate_imports(
        self,
        component: Component,
        mapping: ComponentMapping,
        all_mappings: Dict[str, ComponentMapping],
        all_components: Dict[str, Component]
    ) -> List[str]:
        """Generate import statements for a component.
        
        Args:
            component: Component to generate imports for
            mapping: Component mapping
            all_mappings: All component mappings for dependency resolution
            all_components: All components
            
        Returns:
            List of import statement lines
        """
        lines = []
        
        # Always import the logical file first
        lines.append(f"from {mapping.uniquified_name}_logical import *")
        
        # Generate imports for dependencies
        for dep_uid in component.dependencies:
            if dep_uid not in all_mappings:
                continue
            
            dep_mapping = all_mappings[dep_uid]
            dep_component = all_components[dep_uid]
            
            # Determine relative import path
            current_path = mapping.path or ""
            dep_path = dep_mapping.path or ""
            
            if current_path == dep_path:
                # Same directory - use simple import
                import_path = f"{dep_mapping.uniquified_name}"
            else:
                # Different directories - use absolute path within module
                if dep_path:
                    path_parts = dep_path.split("/")
                    import_path = ".".join(path_parts) + f".{dep_mapping.uniquified_name}"
                else:
                    import_path = f"{dep_mapping.uniquified_name}"
            
            # Add import statement
            lines.append(f"from {import_path} import *")
        
        return lines
    
    def _load_component_file(self, component_uid: str, filename: str) -> Optional[str]:
        """Load a component file from storage.
        
        Args:
            component_uid: UID of the component
            filename: Name of the file to load
            
        Returns:
            File contents or None if not found
        """
        try:
            if self.storage_manager:
                component_dir = self.storage_manager.axiomander_dir / "components" / component_uid
            else:
                component_dir = Path(".axiomander/components") / component_uid
            
            file_path = component_dir / filename
            
            if file_path.exists():
                return file_path.read_text(encoding="utf-8")
            else:
                return f"# {filename} not found for component {component_uid}"
        except Exception as e:
            return f"# Error loading {filename} for component {component_uid}: {str(e)}"
