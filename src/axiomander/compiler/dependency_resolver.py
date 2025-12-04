"""Dependency resolution for component compilation."""

from typing import List, Set, Dict, Optional
from collections import deque

from ..storage.manager import ComponentStorageManager
from .models import CompilationResult


class DependencyResolver:
    """Resolves component dependencies and detects circular dependencies."""
    
    def __init__(self, storage_manager: ComponentStorageManager):
        """Initialize with storage manager.
        
        Args:
            storage_manager: Manager for component storage operations
        """
        self.storage_manager = storage_manager
    
    def resolve_dependencies(
        self, 
        root_component_uids: List[str], 
        result: CompilationResult
    ) -> List[str]:
        """Resolve all transitive dependencies for a set of root components.
        
        Args:
            root_component_uids: List of root component UIDs
            result: Compilation result to record errors
            
        Returns:
            List of all component UIDs including dependencies
        """
        # Load component graph
        try:
            graph = self.storage_manager.load_graph()
        except Exception as e:
            result.errors.append(f"Failed to load component graph: {str(e)}")
            return []
        
        # Build adjacency list from graph
        # ComponentGraph.nodes is Dict[str, str] mapping UID to component name
        adjacency = {}
        
        for uid, name in graph.nodes.items():
            component = self.storage_manager.load_component(uid)
            if component:
                adjacency[uid] = list(component.dependencies)
            else:
                result.warnings.append(f"Component {uid} in graph but not found in storage")
                adjacency[uid] = []
        
        # Collect all dependencies using BFS
        all_components = set()
        queue = deque(root_component_uids)
        
        while queue:
            current_uid = queue.popleft()
            
            if current_uid in all_components:
                continue
            
            all_components.add(current_uid)
            
            # Add dependencies to queue
            if current_uid in adjacency:
                for dep_uid in adjacency[current_uid]:
                    if dep_uid not in all_components:
                        queue.append(dep_uid)
            else:
                result.warnings.append(f"Component {current_uid} not found in graph")
        
        # Check for circular dependencies
        circular_deps = self._detect_circular_dependencies(adjacency, list(all_components))
        if circular_deps:
            for cycle in circular_deps:
                result.errors.append(f"Circular dependency detected: {' -> '.join(cycle)}")
            return []
        
        # Validate all dependencies exist
        missing_deps = []
        for uid in all_components:
            component = self.storage_manager.load_component(uid)
            if not component:
                missing_deps.append(uid)
        
        if missing_deps:
            for uid in missing_deps:
                result.errors.append(f"Missing dependency component: {uid}")
            return []
        
        return list(all_components)
    
    def _detect_circular_dependencies(
        self, 
        adjacency: Dict[str, List[str]], 
        component_uids: List[str]
    ) -> List[List[str]]:
        """Detect circular dependencies using DFS.
        
        Args:
            adjacency: Adjacency list representation of dependencies
            component_uids: List of component UIDs to check
            
        Returns:
            List of circular dependency cycles
        """
        WHITE, GRAY, BLACK = 0, 1, 2
        colors = {uid: WHITE for uid in component_uids}
        cycles = []
        
        def dfs(node: str, path: List[str]) -> None:
            if colors[node] == GRAY:
                # Found a cycle
                cycle_start = path.index(node)
                cycle = path[cycle_start:] + [node]
                cycles.append(cycle)
                return
            
            if colors[node] == BLACK:
                return
            
            colors[node] = GRAY
            path.append(node)
            
            for neighbor in adjacency.get(node, []):
                if neighbor in colors:  # Only check components in our set
                    dfs(neighbor, path)
            
            path.pop()
            colors[node] = BLACK
        
        for uid in component_uids:
            if colors[uid] == WHITE:
                dfs(uid, [])
        
        return cycles
