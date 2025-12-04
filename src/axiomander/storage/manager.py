"""Component storage manager for handling file operations and persistence."""

import json
import os
from pathlib import Path
from typing import Optional, List, Dict

from .models import Component, ComponentGraph, AxiomanderConfig


class ComponentStorageManager:
    """
    Manages the storage and retrieval of components in the .axiomander directory structure.
    
    Handles:
    - Component creation, updates, and deletion
    - Graph management and dependency tracking
    - File system operations for component directories
    - Validation of storage consistency
    """
    
    def __init__(self, project_root: Path):
        """
        Initialize the storage manager for a project.
        
        Args:
            project_root: Root directory of the project containing .axiomander
        """
        self.project_root = Path(project_root)
        self.axiomander_dir = self.project_root / ".axiomander"
        self.components_dir = self.axiomander_dir / "components"
        self.graph_file = self.axiomander_dir / "graph.json"
        self.config_file = self.axiomander_dir / "config.json"
    
    def initialize_project(self, config: Optional[AxiomanderConfig] = None) -> None:
        """
        Initialize the .axiomander directory structure for a new project.
        
        Args:
            config: Optional configuration. If None, creates default config.
        """
        # Create directory structure
        self.axiomander_dir.mkdir(exist_ok=True)
        self.components_dir.mkdir(exist_ok=True)
        
        # Create default config if none provided
        if config is None:
            config = AxiomanderConfig(project_root=str(self.project_root))
        
        # Save config
        self._save_config(config)
        
        # Initialize empty graph
        graph = ComponentGraph()
        self._save_graph(graph)
    
    def create_component(self, component: Component) -> None:
        """
        Create a new component with its directory structure and files.
        
        Args:
            component: Component to create
            
        Raises:
            ValueError: If component UID already exists
        """
        component_dir = self.components_dir / component.uid
        
        if component_dir.exists():
            raise ValueError(f"Component with UID {component.uid} already exists")
        
        # Create component directory
        component_dir.mkdir(parents=True)
        
        # Save component metadata
        self._save_component_metadata(component)
        
        # Create stub files
        self._create_stub_files(component)
        
        # Update graph
        self._add_component_to_graph(component)
    
    def load_component(self, uid: str) -> Optional[Component]:
        """
        Load a component by its UID.
        
        Args:
            uid: Unique identifier of the component
            
        Returns:
            Component if found, None otherwise
        """
        component_file = self.components_dir / uid / "component.json"
        
        if not component_file.exists():
            return None
        
        with open(component_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        return Component(**data)
    
    def update_component(self, component: Component) -> None:
        """
        Update an existing component's metadata.
        
        Args:
            component: Component with updated data
            
        Raises:
            ValueError: If component doesn't exist
        """
        component_dir = self.components_dir / component.uid
        
        if not component_dir.exists():
            raise ValueError(f"Component with UID {component.uid} does not exist")
        
        # Update timestamp
        from datetime import datetime
        component.updated_at = datetime.now().isoformat()
        
        # Save updated metadata
        self._save_component_metadata(component)
        
        # Update graph if needed
        self._update_component_in_graph(component)
    
    def delete_component(self, uid: str) -> None:
        """
        Delete a component and its directory.
        
        Args:
            uid: Unique identifier of the component to delete
            
        Raises:
            ValueError: If component doesn't exist
        """
        component_dir = self.components_dir / uid
        
        if not component_dir.exists():
            raise ValueError(f"Component with UID {uid} does not exist")
        
        # Remove from graph first
        self._remove_component_from_graph(uid)
        
        # Remove directory and all files
        import shutil
        shutil.rmtree(component_dir)
    
    def list_components(self) -> List[str]:
        """
        List all component UIDs in the project.
        
        Returns:
            List of component UIDs
        """
        if not self.components_dir.exists():
            return []
        
        return [d.name for d in self.components_dir.iterdir() if d.is_dir()]
    
    def load_graph(self) -> ComponentGraph:
        """
        Load the component graph.
        
        Returns:
            ComponentGraph instance
        """
        if not self.graph_file.exists():
            return ComponentGraph()
        
        with open(self.graph_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        return ComponentGraph(**data)
    
    def load_config(self) -> Optional[AxiomanderConfig]:
        """
        Load the project configuration.
        
        Returns:
            AxiomanderConfig if exists, None otherwise
        """
        if not self.config_file.exists():
            return None
        
        with open(self.config_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        return AxiomanderConfig(**data)
    
    def validate_storage(self) -> List[str]:
        """
        Validate the consistency of the storage system.
        
        Returns:
            List of validation errors (empty if valid)
        """
        errors = []
        
        # Check if .axiomander directory exists
        if not self.axiomander_dir.exists():
            errors.append(".axiomander directory does not exist")
            return errors
        
        # Check config
        config = self.load_config()
        if config is None:
            errors.append("config.json is missing or invalid")
        
        # Check graph
        try:
            graph = self.load_graph()
        except Exception as e:
            errors.append(f"graph.json is invalid: {e}")
            return errors
        
        # Validate components
        component_uids = self.list_components()
        
        for uid in component_uids:
            component = self.load_component(uid)
            if component is None:
                errors.append(f"Component {uid} has invalid metadata")
                continue
            
            # Check if component is in graph
            if uid not in graph.nodes:
                errors.append(f"Component {uid} not found in graph")
            
            # Check required files exist
            component_dir = self.components_dir / uid
            required_files = [
                component.logical_file,
                component.implementation_file,
                component.test_file
            ]
            
            for file_name in required_files:
                file_path = component_dir / file_name
                if not file_path.exists():
                    errors.append(f"Component {uid} missing file: {file_name}")
        
        # Check for orphaned graph nodes
        for uid in graph.nodes:
            if uid not in component_uids:
                errors.append(f"Graph contains orphaned node: {uid}")
        
        return errors
    
    def _save_component_metadata(self, component: Component) -> None:
        """Save component metadata to component.json."""
        component_file = self.components_dir / component.uid / "component.json"
        
        with open(component_file, 'w', encoding='utf-8') as f:
            json.dump(component.model_dump(), f, indent=2)
    
    def _create_stub_files(self, component: Component) -> None:
        """Create stub files for a new component."""
        component_dir = self.components_dir / component.uid
        
        # Create logical.py stub
        logical_file = component_dir / component.logical_file
        logical_content = f'"""Logical specification for {component.name}."""\n\n# Contract definitions go here\n'
        logical_file.write_text(logical_content, encoding='utf-8')
        
        # Create implementation.py stub
        impl_file = component_dir / component.implementation_file
        impl_content = f'"""Implementation for {component.name}."""\n\n# Implementation goes here\n'
        impl_file.write_text(impl_content, encoding='utf-8')
        
        # Create test.py stub
        test_file = component_dir / component.test_file
        test_content = f'"""Tests for {component.name}."""\n\n# Contract validation tests go here\n'
        test_file.write_text(test_content, encoding='utf-8')
    
    def _save_graph(self, graph: ComponentGraph) -> None:
        """Save the component graph to graph.json."""
        with open(self.graph_file, 'w', encoding='utf-8') as f:
            json.dump(graph.model_dump(), f, indent=2)
    
    def _save_config(self, config: AxiomanderConfig) -> None:
        """Save the configuration to config.json."""
        with open(self.config_file, 'w', encoding='utf-8') as f:
            json.dump(config.model_dump(), f, indent=2)
    
    def _add_component_to_graph(self, component: Component) -> None:
        """Add a component to the graph."""
        graph = self.load_graph()
        graph.nodes[component.uid] = component.name
        
        # Add dependency edges
        for dep in component.dependencies:
            edge = {
                "from_uid": component.uid,
                "to_uid": dep.uid,
                "relationship_type": "depends_on"
            }
            graph.edges.append(edge)
        
        # Update timestamp
        from datetime import datetime
        graph.updated_at = datetime.now().isoformat()
        
        self._save_graph(graph)
    
    def _update_component_in_graph(self, component: Component) -> None:
        """Update a component in the graph."""
        graph = self.load_graph()
        graph.nodes[component.uid] = component.name
        
        # Remove old dependency edges for this component
        graph.edges = [
            edge for edge in graph.edges 
            if edge.get("from_uid") != component.uid or edge.get("relationship_type") != "depends_on"
        ]
        
        # Add new dependency edges
        for dep in component.dependencies:
            edge = {
                "from_uid": component.uid,
                "to_uid": dep.uid,
                "relationship_type": "depends_on"
            }
            graph.edges.append(edge)
        
        # Update timestamp
        from datetime import datetime
        graph.updated_at = datetime.now().isoformat()
        
        self._save_graph(graph)
    
    def _remove_component_from_graph(self, uid: str) -> None:
        """Remove a component from the graph."""
        graph = self.load_graph()
        
        # Remove node
        if uid in graph.nodes:
            del graph.nodes[uid]
        
        # Remove all edges involving this component
        graph.edges = [
            edge for edge in graph.edges
            if edge.get("from_uid") != uid and edge.get("to_uid") != uid
        ]
        
        # Update timestamp
        from datetime import datetime
        graph.updated_at = datetime.now().isoformat()
        
        self._save_graph(graph)
