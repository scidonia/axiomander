"""Component indexing system for the LSP server."""

import logging
from typing import Dict, List, Optional, Set
from pathlib import Path
from datetime import datetime
import json

from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler, FileModifiedEvent, FileCreatedEvent, FileDeletedEvent

from ..storage.manager import ComponentStorageManager
from ..storage.models import Component
from .models import ComponentIndexEntry, ComponentDiagnosticType
from .utils import create_diagnostic, get_component_uid_from_path, is_component_file

logger = logging.getLogger(__name__)


class ComponentFileHandler(FileSystemEventHandler):
    """File system event handler for component changes."""
    
    def __init__(self, index: 'ComponentIndex'):
        self.index = index
    
    def on_modified(self, event):
        if not event.is_directory and is_component_file(Path(event.src_path)):
            self.index.handle_file_change(Path(event.src_path))
    
    def on_created(self, event):
        if not event.is_directory and is_component_file(Path(event.src_path)):
            self.index.handle_file_change(Path(event.src_path))
    
    def on_deleted(self, event):
        if not event.is_directory and is_component_file(Path(event.src_path)):
            self.index.handle_file_deletion(Path(event.src_path))


class ComponentIndex:
    """In-memory index of all components with file watching."""
    
    def __init__(self, project_root: Path):
        self.project_root = project_root
        self.storage_manager = ComponentStorageManager(project_root)
        self.components: Dict[str, ComponentIndexEntry] = {}
        self.observer: Optional[Observer] = None
        self.change_callbacks: List[callable] = []
        
    def start(self) -> None:
        """Start the component index and file watching."""
        logger.info("Starting component index...")
        
        # Load all components
        self.reload_all_components()
        
        # Start file watching
        self.start_file_watching()
        
        logger.info(f"Component index started with {len(self.components)} components")
    
    def stop(self) -> None:
        """Stop file watching and cleanup."""
        if self.observer:
            self.observer.stop()
            self.observer.join()
            self.observer = None
        logger.info("Component index stopped")
    
    def add_change_callback(self, callback: callable) -> None:
        """Add a callback to be called when components change."""
        self.change_callbacks.append(callback)
    
    def reload_all_components(self) -> None:
        """Reload all components from storage."""
        self.components.clear()
        
        try:
            component_uids = self.storage_manager.list_components()
            for uid in component_uids:
                self.load_component(uid)
        except Exception as e:
            logger.error(f"Error reloading components: {e}")
    
    def load_component(self, uid: str) -> Optional[ComponentIndexEntry]:
        """Load a single component into the index."""
        try:
            component = self.storage_manager.load_component(uid)
            if not component:
                return None
            
            # Build file paths
            component_dir = self.project_root / ".axiomander" / "components" / uid
            files = {
                "component.json": component_dir / "component.json",
                "logical.py": component_dir / component.logical_file,
                "implementation.py": component_dir / component.implementation_file,
                "test.py": component_dir / component.test_file
            }
            
            # Get last modified time
            last_modified = datetime.now()
            if files["component.json"].exists():
                last_modified = datetime.fromtimestamp(files["component.json"].stat().st_mtime)
            
            # Generate diagnostics
            diagnostics = self.generate_diagnostics(component, files)
            
            # Build dependency lists (simplified for now)
            dependencies = [dep.uid for dep in component.dependencies]
            dependents = self.find_dependents(uid)
            
            entry = ComponentIndexEntry(
                uid=uid,
                name=component.name,
                component_type=component.component_type,
                file_path=component_dir,
                metadata=component,
                files=files,
                last_modified=last_modified,
                diagnostics=diagnostics,
                dependencies=dependencies,
                dependents=dependents
            )
            
            self.components[uid] = entry
            return entry
            
        except Exception as e:
            logger.error(f"Error loading component {uid}: {e}")
            return None
    
    def generate_diagnostics(self, component: Component, files: Dict[str, Path]) -> List:
        """Generate diagnostics for a component."""
        diagnostics = []
        
        # Check for missing files
        for file_type, file_path in files.items():
            if not file_path.exists():
                diagnostics.append(create_diagnostic(
                    f"Missing {file_type}",
                    source="axiomander-missing-file"
                ))
        
        # Check for invalid component.json
        if files["component.json"].exists():
            try:
                with open(files["component.json"], 'r') as f:
                    json.load(f)
            except json.JSONDecodeError as e:
                diagnostics.append(create_diagnostic(
                    f"Invalid JSON in component.json: {e}",
                    source="axiomander-invalid-json"
                ))
        
        # Check contract completeness
        if not component.contract_status.has_preconditions and not component.contract_status.has_postconditions:
            diagnostics.append(create_diagnostic(
                "Component has no contracts defined",
                severity=1,  # Warning
                source="axiomander-missing-contracts"
            ))
        
        return diagnostics
    
    def find_dependents(self, uid: str) -> List[str]:
        """Find components that depend on the given component."""
        dependents = []
        for other_uid, entry in self.components.items():
            if uid in entry.dependencies:
                dependents.append(other_uid)
        return dependents
    
    def start_file_watching(self) -> None:
        """Start watching component files for changes."""
        components_dir = self.project_root / ".axiomander" / "components"
        if not components_dir.exists():
            logger.warning("Components directory does not exist, skipping file watching")
            return
        
        self.observer = Observer()
        handler = ComponentFileHandler(self)
        self.observer.schedule(handler, str(components_dir), recursive=True)
        self.observer.start()
        logger.info("File watching started")
    
    def handle_file_change(self, file_path: Path) -> None:
        """Handle a file change event."""
        uid = get_component_uid_from_path(file_path)
        if uid:
            logger.info(f"Component file changed: {file_path}")
            self.load_component(uid)
            self.notify_change_callbacks(uid)
    
    def handle_file_deletion(self, file_path: Path) -> None:
        """Handle a file deletion event."""
        uid = get_component_uid_from_path(file_path)
        if uid and uid in self.components:
            logger.info(f"Component file deleted: {file_path}")
            # Reload to update diagnostics
            self.load_component(uid)
            self.notify_change_callbacks(uid)
    
    def notify_change_callbacks(self, uid: str) -> None:
        """Notify all change callbacks about a component change."""
        for callback in self.change_callbacks:
            try:
                callback(uid)
            except Exception as e:
                logger.error(f"Error in change callback: {e}")
    
    def get_component(self, uid: str) -> Optional[ComponentIndexEntry]:
        """Get a component by UID."""
        return self.components.get(uid)
    
    def get_component_by_name(self, name: str) -> List[ComponentIndexEntry]:
        """Get components by name (may return multiple)."""
        return [entry for entry in self.components.values() if entry.name == name]
    
    def get_all_components(self) -> List[ComponentIndexEntry]:
        """Get all components."""
        return list(self.components.values())
    
    def get_components_with_diagnostics(self) -> List[ComponentIndexEntry]:
        """Get components that have diagnostics."""
        return [entry for entry in self.components.values() if entry.diagnostics]
