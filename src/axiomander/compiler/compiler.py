"""Main component compiler implementation."""

import json
import re
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from collections import defaultdict

from ..storage.models import Component, ComponentGraph
from ..storage.manager import ComponentStorageManager
from .models import CompilerConfig, CompilerMode, CompilationResult, ComponentMapping
from .name_resolver import NameResolver
from .dependency_resolver import DependencyResolver
from .code_generator import CodeGenerator


class ComponentCompiler:
    """
    Main component compiler that orchestrates the compilation process.
    
    Handles:
    - Component loading and validation
    - Dependency resolution
    - Name uniquification
    - Code generation
    - File system operations
    """
    
    def __init__(self, storage_manager: ComponentStorageManager, config: CompilerConfig):
        """Initialize the compiler with storage manager and configuration.
        
        Args:
            storage_manager: Manager for component storage operations
            config: Compiler configuration settings
        """
        self.storage_manager = storage_manager
        self.config = config
        self.name_resolver = NameResolver()
        self.dependency_resolver = DependencyResolver(storage_manager)
        self.code_generator = CodeGenerator(config, storage_manager)
    
    def compile_components(
        self, 
        component_uids: List[str], 
        module_name: str,
        entry_point_uid: Optional[str] = None
    ) -> CompilationResult:
        """Compile a set of components into a Python module.
        
        Args:
            component_uids: List of component UIDs to compile
            module_name: Name of the target module
            entry_point_uid: UID of the entry point component (defaults to first)
            
        Returns:
            CompilationResult with success status and details
        """
        result = CompilationResult(
            success=False,
            module_name=module_name
        )
        
        try:
            # Load and validate components
            components = self._load_components(component_uids, result)
            if not components:
                return result
            
            # Resolve dependencies
            all_component_uids = self.dependency_resolver.resolve_dependencies(
                component_uids, result
            )
            if result.errors:
                return result
            
            # Load all components including dependencies
            all_components = self._load_components(all_component_uids, result)
            if not all_components:
                return result
            
            # Create component mappings with uniquified names
            mappings = self._create_component_mappings(all_components, result)
            if result.errors:
                return result
            
            # Generate code files
            generated_files = self._generate_code_files(
                all_components, mappings, module_name, entry_point_uid or component_uids[0], result
            )
            
            result.compiled_components = all_component_uids
            result.generated_files = generated_files
            result.success = True
            
        except Exception as e:
            result.errors.append(f"Compilation failed: {str(e)}")
        
        return result
    
    def _load_components(self, component_uids: List[str], result: CompilationResult) -> Dict[str, Component]:
        """Load components from storage and validate them."""
        components = {}
        
        for uid in component_uids:
            component = self.storage_manager.load_component(uid)
            if not component:
                result.errors.append(f"Component not found: {uid}")
                continue
            
            # Validate component has required files
            component_dir = self.storage_manager.axiomander_dir / "components" / uid
            if not (component_dir / "implementation.py").exists():
                result.errors.append(f"Component {uid} missing implementation.py")
                continue
            
            components[uid] = component
        
        return components
    
    def _create_component_mappings(
        self, 
        components: Dict[str, Component], 
        result: CompilationResult
    ) -> Dict[str, ComponentMapping]:
        """Create component mappings with uniquified names."""
        mappings = {}
        
        # Group components by path for name resolution
        path_groups = defaultdict(list)
        for uid, component in components.items():
            path = component.path or ""
            path_groups[path].append((uid, component))
        
        # Resolve names within each path group
        for path, path_components in path_groups.items():
            names_in_path = [comp.name for _, comp in path_components]
            uniquified_names = self.name_resolver.uniquify_names(
                [(uid, comp.name) for uid, comp in path_components]
            )
            
            for (uid, component), uniquified_name in zip(path_components, uniquified_names):
                mappings[uid] = ComponentMapping(
                    uid=uid,
                    original_name=component.name,
                    uniquified_name=uniquified_name,
                    path=path if path else None,
                    dependencies=set(component.dependencies)
                )
        
        return mappings
    
    def _generate_code_files(
        self,
        components: Dict[str, Component],
        mappings: Dict[str, ComponentMapping],
        module_name: str,
        entry_point_uid: str,
        result: CompilationResult
    ) -> List[Path]:
        """Generate all code files for the compiled module."""
        generated_files = []
        
        # Create module directory structure
        module_dir = self.config.target_directory / module_name
        module_dir.mkdir(parents=True, exist_ok=True)
        
        # Create test directory structure if needed
        test_dir = None
        if self.config.include_tests:
            test_dir = Path("tests")
            test_dir.mkdir(parents=True, exist_ok=True)
        
        # Generate component files
        for uid, component in components.items():
            mapping = mappings[uid]
            
            # Create path directories if needed
            component_dir = module_dir
            test_component_dir = test_dir
            
            if mapping.path:
                path_parts = mapping.path.split("/")
                for part in path_parts:
                    component_dir = component_dir / part
                    component_dir.mkdir(exist_ok=True)
                    
                    # Create __init__.py in each directory
                    init_file = component_dir / "__init__.py"
                    if not init_file.exists():
                        init_file.write_text("")
                        generated_files.append(init_file)
                    
                    if test_component_dir:
                        test_component_dir = test_component_dir / part
                        test_component_dir.mkdir(exist_ok=True)
                        
                        test_init_file = test_component_dir / "__init__.py"
                        if not test_init_file.exists():
                            test_init_file.write_text("")
                            generated_files.append(test_init_file)
            
            # Generate implementation file
            impl_file = component_dir / f"{mapping.uniquified_name}.py"
            impl_content = self.code_generator.generate_implementation_file(
                component, mapping, mappings, components, module_name
            )
            impl_file.write_text(impl_content)
            generated_files.append(impl_file)
            
            # Generate logical file
            logical_file = component_dir / f"{mapping.uniquified_name}_logical.py"
            logical_content = self.code_generator.generate_logical_file(component, mapping)
            logical_file.write_text(logical_content)
            generated_files.append(logical_file)
            
            # Generate test file if enabled
            if self.config.include_tests and test_component_dir:
                test_file = test_component_dir / f"test_{mapping.uniquified_name}.py"
                test_content = self.code_generator.generate_test_file(
                    component, mapping, module_name
                )
                test_file.write_text(test_content)
                generated_files.append(test_file)
        
        # Generate module __init__.py
        init_file = module_dir / "__init__.py"
        init_content = self.code_generator.generate_module_init(
            components, mappings, module_name, entry_point_uid
        )
        init_file.write_text(init_content)
        generated_files.append(init_file)
        
        # Generate main.py if entry point exists
        if entry_point_uid in components:
            main_file = module_dir / "main.py"
            main_content = self.code_generator.generate_main_file(
                components[entry_point_uid], mappings[entry_point_uid], mappings, components
            )
            main_file.write_text(main_content)
            generated_files.append(main_file)
        
        return generated_files
