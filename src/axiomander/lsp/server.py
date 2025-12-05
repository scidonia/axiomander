"""Main LSP server implementation for Axiomander."""

import logging
import sys
from pathlib import Path
from typing import List, Optional, Any, Dict

from lsprotocol.types import (
    TextDocumentSyncKind,
    Hover,
    HoverParams,
    InitializeParams,
    InitializeResult,
    MarkupContent,
    MarkupKind,
    ServerCapabilities,
    TextDocumentSyncOptions,
    WorkDoneProgressBegin,
    WorkDoneProgressEnd,
    WorkDoneProgressReport,
    MessageType,
    ShowMessageParams,
    LogMessageParams,
    PublishDiagnosticsParams,
    ExecuteCommandParams,
    CodeActionParams,
    CodeAction,
    CodeActionKind,
    WorkspaceEdit,
    TextEdit,
    Range,
    Position,
    ExecuteCommandOptions
)
from pygls.lsp.server import LanguageServer
from pygls.workspace import Document

from .index import ComponentIndex
from .utils import uri_to_path, path_to_uri, format_component_hover_text, get_component_uid_from_path

logger = logging.getLogger(__name__)


class AxiomanderLanguageServer(LanguageServer):
    """Axiomander Language Server implementation."""
    
    def __init__(self):
        super().__init__("axiomander-lsp", "0.1.0")
        self.component_index: Optional[ComponentIndex] = None
        self.project_root: Optional[Path] = None
        
    def setup_logging(self):
        """Setup logging for the LSP server."""
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
            handlers=[logging.StreamHandler(sys.stderr)]
        )


# Create the server instance
server = AxiomanderLanguageServer()


@server.feature("initialize")
def initialize(params: InitializeParams) -> InitializeResult:
    """Initialize the language server."""
    logger.info("Initializing Axiomander LSP server...")
    
    # Get project root from workspace folders
    if params.workspace_folders and len(params.workspace_folders) > 0:
        workspace_uri = params.workspace_folders[0].uri
        server.project_root = uri_to_path(workspace_uri)
    elif params.root_uri:
        server.project_root = uri_to_path(params.root_uri)
    else:
        server.project_root = Path.cwd()
    
    logger.info(f"Project root: {server.project_root}")
    
    # Initialize component index
    server.component_index = ComponentIndex(server.project_root)
    server.component_index.add_change_callback(on_component_change)
    
    return InitializeResult(
        capabilities=ServerCapabilities(
            text_document_sync=TextDocumentSyncOptions(
                open_close=True,
                change=TextDocumentSyncKind.Incremental,
                save=True
            ),
            hover_provider=True,
            execute_command_provider=ExecuteCommandOptions(
                commands=[
                    "axiomander.compile",
                    "axiomander.validate", 
                    "axiomander.createComponent",
                    "axiomander.analyzeProject"
                ]
            ),
            code_action_provider=True,
            workspace_symbol_provider=True
        )
    )


@server.feature("initialized")
def initialized(params):
    """Called after the client has received the initialize result."""
    logger.info("LSP server initialized, starting component index...")
    
    if server.component_index:
        server.component_index.start()
        
        # Send initial diagnostics
        publish_all_diagnostics()
        
        server.show_message(
            f"Axiomander LSP server ready. Found {len(server.component_index.components)} components.",
            MessageType.Info
        )


@server.feature("shutdown")
def shutdown(params):
    """Shutdown the language server."""
    logger.info("Shutting down LSP server...")
    if server.component_index:
        server.component_index.stop()


@server.feature("textDocument/hover")
def hover(params: HoverParams) -> Optional[Hover]:
    """Provide hover information for components."""
    if not server.component_index:
        return None
    
    document_uri = params.text_document.uri
    file_path = uri_to_path(document_uri)
    
    # Check if this is a component file
    uid = get_component_uid_from_path(file_path)
    if not uid:
        return None
    
    component_entry = server.component_index.get_component(uid)
    if not component_entry:
        return None
    
    hover_text = format_component_hover_text(component_entry.metadata)
    
    return Hover(
        contents=MarkupContent(
            kind=MarkupKind.Markdown,
            value=hover_text
        )
    )


@server.feature("textDocument/codeAction")
def code_action(params: CodeActionParams) -> List[CodeAction]:
    """Provide code actions for component files."""
    if not server.component_index:
        return []
    
    document_uri = params.text_document.uri
    file_path = uri_to_path(document_uri)
    
    actions = []
    
    # Check if this is in a component directory
    uid = get_component_uid_from_path(file_path)
    if uid:
        component_entry = server.component_index.get_component(uid)
        if component_entry:
            # Add action to compile this component
            actions.append(CodeAction(
                title=f"Compile component '{component_entry.name}'",
                kind=CodeActionKind.Source,
                command={
                    "command": "axiomander.compile",
                    "arguments": [uid]
                }
            ))
            
            # Add action to validate component
            actions.append(CodeAction(
                title=f"Validate component '{component_entry.name}'",
                kind=CodeActionKind.Source,
                command={
                    "command": "axiomander.validate",
                    "arguments": [uid]
                }
            ))
    
    # Add general actions
    actions.append(CodeAction(
        title="Create new component",
        kind=CodeActionKind.Source,
        command={
            "command": "axiomander.createComponent",
            "arguments": []
        }
    ))
    
    return actions


@server.feature("workspace/executeCommand")
def execute_command(params: ExecuteCommandParams) -> Any:
    """Execute custom commands."""
    command = params.command
    arguments = params.arguments or []
    
    logger.info(f"Executing command: {command} with args: {arguments}")
    
    if command == "axiomander.compile":
        return handle_compile_command(arguments)
    elif command == "axiomander.validate":
        return handle_validate_command(arguments)
    elif command == "axiomander.createComponent":
        return handle_create_component_command(arguments)
    elif command == "axiomander.analyzeProject":
        return handle_analyze_project_command(arguments)
    else:
        server.show_message(f"Unknown command: {command}", MessageType.Error)
        return None


def handle_compile_command(arguments: List[Any]) -> Dict[str, Any]:
    """Handle the compile command."""
    if not server.component_index or not server.project_root:
        return {"success": False, "error": "Server not properly initialized"}
    
    try:
        # For now, just show a message
        # In the future, this would call the actual compiler
        server.show_message("Compile command received (not yet implemented)", MessageType.Info)
        return {"success": True, "message": "Compile command executed"}
    except Exception as e:
        logger.error(f"Error in compile command: {e}")
        return {"success": False, "error": str(e)}


def handle_validate_command(arguments: List[Any]) -> Dict[str, Any]:
    """Handle the validate command."""
    if not server.component_index:
        return {"success": False, "error": "Server not properly initialized"}
    
    try:
        # Reload components and publish diagnostics
        server.component_index.reload_all_components()
        publish_all_diagnostics()
        
        components_with_issues = server.component_index.get_components_with_diagnostics()
        
        if components_with_issues:
            server.show_message(
                f"Validation found issues in {len(components_with_issues)} components",
                MessageType.Warning
            )
        else:
            server.show_message("All components validated successfully", MessageType.Info)
        
        return {"success": True, "issues_count": len(components_with_issues)}
    except Exception as e:
        logger.error(f"Error in validate command: {e}")
        return {"success": False, "error": str(e)}


def handle_create_component_command(arguments: List[Any]) -> Dict[str, Any]:
    """Handle the create component command."""
    # For now, just show a message
    # In the future, this would open a dialog or create a component
    server.show_message("Create component command received (not yet implemented)", MessageType.Info)
    return {"success": True, "message": "Create component command executed"}


def handle_analyze_project_command(arguments: List[Any]) -> Dict[str, Any]:
    """Handle the analyze project command."""
    if not server.component_index:
        return {"success": False, "error": "Server not properly initialized"}
    
    try:
        components = server.component_index.get_all_components()
        components_with_issues = server.component_index.get_components_with_diagnostics()
        
        analysis = {
            "total_components": len(components),
            "components_with_issues": len(components_with_issues),
            "component_types": {},
            "missing_contracts": 0
        }
        
        for component in components:
            comp_type = component.component_type.value
            analysis["component_types"][comp_type] = analysis["component_types"].get(comp_type, 0) + 1
            
            if not component.metadata.contract_status.has_preconditions and not component.metadata.contract_status.has_postconditions:
                analysis["missing_contracts"] += 1
        
        server.show_message(
            f"Project analysis: {analysis['total_components']} components, "
            f"{analysis['components_with_issues']} with issues, "
            f"{analysis['missing_contracts']} missing contracts",
            MessageType.Info
        )
        
        return {"success": True, "analysis": analysis}
    except Exception as e:
        logger.error(f"Error in analyze project command: {e}")
        return {"success": False, "error": str(e)}


def on_component_change(uid: str) -> None:
    """Called when a component changes."""
    if not server.component_index:
        return
    
    component_entry = server.component_index.get_component(uid)
    if not component_entry:
        return
    
    # Publish diagnostics for the changed component
    for file_type, file_path in component_entry.files.items():
        if file_path.exists():
            server.publish_diagnostics(
                PublishDiagnosticsParams(
                    uri=path_to_uri(file_path),
                    diagnostics=component_entry.diagnostics
                )
            )


def publish_all_diagnostics() -> None:
    """Publish diagnostics for all components."""
    if not server.component_index:
        return
    
    for component_entry in server.component_index.get_all_components():
        for file_type, file_path in component_entry.files.items():
            if file_path.exists():
                server.publish_diagnostics(
                    PublishDiagnosticsParams(
                        uri=path_to_uri(file_path),
                        diagnostics=component_entry.diagnostics
                    )
                )


def start_server():
    """Start the Axiomander LSP server."""
    server.setup_logging()
    logger.info("Starting Axiomander LSP server...")
    
    # Start the server on stdin/stdout
    server.start_io()
