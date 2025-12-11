"""
LSP server for axiomander.

Provides Language Server Protocol integration for real-time verification
feedback in editors.
"""

import asyncio
import logging
from typing import Dict, List, Optional, Any, Union
from pathlib import Path
import time
import ast
import sys

import lsprotocol.types as lsp
from pygls.protocol import LanguageServerProtocol, default_converter
from pygls.server import run

from ..verification.orchestrator import VerificationOrchestrator, VerificationResult
from ..ast.assertion_finder import AssertionFinder, AssertionType


logger = logging.getLogger(__name__)


# Global state for the server
verification_cache: Dict[str, List[VerificationResult]] = {}
last_verification: Dict[str, float] = {}
pending_verifications: Dict[str, asyncio.Task] = {}
orchestrator = VerificationOrchestrator()
verification_delay = 1.0  # seconds


class AxiomanderLSP(LanguageServerProtocol):
    """Axiomander Language Server Protocol implementation."""
    
    def __init__(self, server_info, converter):
        super().__init__(server_info, converter)
        self.verification_cache = verification_cache
        self.pending_verifications = pending_verifications
        self.orchestrator = orchestrator

    async def lsp_initialize(self, params: lsp.InitializeParams) -> lsp.InitializeResult:
        """Initialize the language server."""
        logger.info("Axiomander LSP server initializing...")
        return lsp.InitializeResult(
            capabilities=lsp.ServerCapabilities(
                text_document_sync=lsp.TextDocumentSyncOptions(
                    open_close=True,
                    change=lsp.TextDocumentSyncKind.FULL
                ),
                hover_provider=True,
                completion_provider=lsp.CompletionOptions(
                    trigger_characters=["assert ", "def "]
                )
            )
        )

    async def lsp_text_document__did_open(self, params: lsp.DidOpenTextDocumentParams):
        """Handle document open events."""
        await self._verify_document(params.text_document.uri, params.text_document.text)

    async def lsp_text_document__did_change(self, params: lsp.DidChangeTextDocumentParams):
        """Handle document change events with debouncing."""
        uri = params.text_document.uri
        
        # Cancel any pending verification for this document
        if uri in self.pending_verifications:
            self.pending_verifications[uri].cancel()
        
        # Get the updated document content
        document = self.workspace.get_document(uri)
        
        # Schedule debounced verification
        self.pending_verifications[uri] = asyncio.create_task(
            self._debounced_verify(uri, document.source)
        )

    async def lsp_text_document__did_close(self, params: lsp.DidCloseTextDocumentParams):
        """Handle document close events."""
        uri = params.text_document.uri
        
        # Cancel pending verification
        if uri in self.pending_verifications:
            self.pending_verifications[uri].cancel()
            del self.pending_verifications[uri]
        
        # Clear cache for closed document
        if uri in self.verification_cache:
            del self.verification_cache[uri]
        if uri in last_verification:
            del last_verification[uri]

    async def lsp_text_document__hover(self, params: lsp.HoverParams) -> Optional[lsp.Hover]:
        """Provide hover information for assertions and functions."""
        try:
            uri = params.text_document.uri
            document = self.workspace.get_document(uri)
            
            # Get the line at cursor position
            line_num = params.position.line
            lines = document.source.split('\n')
            
            if line_num >= len(lines):
                return None
            
            line_content = lines[line_num]
            
            # Check if hovering over an assertion
            if "assert" in line_content:
                # Get verification results for this document
                if uri in self.verification_cache:
                    results = self.verification_cache[uri]
                    
                    hover_content = []
                    hover_content.append("**Axiomander Verification**")
                    
                    # Find relevant assertion information
                    for result in results:
                        for assertion in result.verified_assertions + result.failed_assertions:
                            if any(word in assertion.lower() for word in line_content.lower().split()):
                                status = "✅ Verified" if assertion in result.verified_assertions else "❌ Failed"
                                hover_content.append(f"- {status}: {assertion}")
                    
                    if len(hover_content) > 1:
                        return lsp.Hover(
                            contents=lsp.MarkupContent(
                                kind=lsp.MarkupKind.MARKDOWN,
                                value="\n".join(hover_content)
                            )
                        )
            
            # Check if hovering over a function definition
            if line_content.strip().startswith("def "):
                if uri in self.verification_cache:
                    results = self.verification_cache[uri]
                    
                    for result in results:
                        if result.function_name in line_content:
                            verified_count = len(result.verified_assertions)
                            failed_count = len(result.failed_assertions)
                            error_count = len(result.errors)
                            
                            status_emoji = "✅" if failed_count == 0 and error_count == 0 else "❌"
                            
                            hover_content = [
                                f"**{status_emoji} Function: {result.function_name}**",
                                f"- Verified assertions: {verified_count}",
                                f"- Failed assertions: {failed_count}",
                                f"- Errors: {error_count}",
                                f"- Execution time: {result.execution_time:.3f}s"
                            ]
                            
                            return lsp.Hover(
                                contents=lsp.MarkupContent(
                                    kind=lsp.MarkupKind.MARKDOWN,
                                    value="\n".join(hover_content)
                                )
                            )
            
        except Exception as e:
            logger.error(f"Hover handler error: {e}")
        
        return None

    async def lsp_text_document__completion(self, params: lsp.CompletionParams) -> Optional[lsp.CompletionList]:
        """Provide code completion for contract patterns."""
        try:
            document = self.workspace.get_document(params.text_document.uri)
            line_num = params.position.line
            lines = document.source.split('\n')
            
            if line_num >= len(lines):
                return None
            
            line_content = lines[line_num]
            
            completions = []
            
            # Provide assertion completions
            if "assert" in line_content or line_content.strip().endswith("assert"):
                contract_completions = [
                    lsp.CompletionItem(
                        label="assert precondition",
                        kind=lsp.CompletionItemKind.SNIPPET,
                        insert_text="assert ${1:condition}, \"${2:Precondition message}\"",
                        insert_text_format=lsp.InsertTextFormat.SNIPPET,
                        documentation="Add a precondition assertion",
                        detail="Precondition contract"
                    ),
                    lsp.CompletionItem(
                        label="assert postcondition",
                        kind=lsp.CompletionItemKind.SNIPPET,
                        insert_text="assert ${1:condition}, \"${2:Postcondition message}\"",
                        insert_text_format=lsp.InsertTextFormat.SNIPPET,
                        documentation="Add a postcondition assertion",
                        detail="Postcondition contract"
                    ),
                    lsp.CompletionItem(
                        label="assert loop invariant",
                        kind=lsp.CompletionItemKind.SNIPPET,
                        insert_text="assert ${1:invariant_condition}, \"Loop invariant\"",
                        insert_text_format=lsp.InsertTextFormat.SNIPPET,
                        documentation="Add a loop invariant assertion",
                        detail="Loop invariant contract"
                    )
                ]
                completions.extend(contract_completions)
            
            # Provide function template completions
            if line_content.strip().startswith("def") or "def " in line_content:
                function_completions = [
                    lsp.CompletionItem(
                        label="def with contracts",
                        kind=lsp.CompletionItemKind.SNIPPET,
                        insert_text="""def ${1:function_name}(${2:param}: ${3:int}) -> ${4:int}:
    assert ${5:precondition}, "${6:Precondition message}"
    ${7:# Function body}
    assert ${8:postcondition}, "${9:Postcondition message}"
    return ${10:result}""",
                        insert_text_format=lsp.InsertTextFormat.SNIPPET,
                        documentation="Function template with pre/postconditions",
                        detail="Contracted function template"
                    )
                ]
                completions.extend(function_completions)
            
            if completions:
                return lsp.CompletionList(
                    is_incomplete=False,
                    items=completions
                )
            
        except Exception as e:
            logger.error(f"Completion handler error: {e}")
        
        return None

    async def _debounced_verify(self, uri: str, content: str):
        """Verify document after debounce delay."""
        try:
            await asyncio.sleep(verification_delay)
            await self._verify_document(uri, content)
        except asyncio.CancelledError:
            logger.debug(f"Verification cancelled for {uri}")
        except Exception as e:
            logger.error(f"Debounced verification failed for {uri}: {e}")

    async def _verify_document(self, uri: str, content: str):
        """Verify a document and publish diagnostics."""
        try:
            # Skip verification for non-Python files
            if not uri.endswith('.py'):
                return
            
            logger.debug(f"Verifying document: {uri}")
            
            # Run verification in a thread to avoid blocking
            loop = asyncio.get_event_loop()
            results = await loop.run_in_executor(
                None, 
                self._run_verification, 
                content, 
                uri
            )
            
            # Cache results
            self.verification_cache[uri] = results
            last_verification[uri] = time.time()
            
            # Convert results to diagnostics and publish
            diagnostics = self._convert_to_diagnostics(results, content)
            await self._publish_diagnostics(uri, diagnostics)
            
        except Exception as e:
            logger.error(f"Verification failed for {uri}: {e}")
            # Publish error diagnostic
            error_diagnostic = lsp.Diagnostic(
                range=lsp.Range(
                    start=lsp.Position(line=0, character=0),
                    end=lsp.Position(line=0, character=0)
                ),
                message=f"Verification error: {str(e)}",
                severity=lsp.DiagnosticSeverity.ERROR,
                source="axiomander"
            )
            await self._publish_diagnostics(uri, [error_diagnostic])

    def _run_verification(self, content: str, uri: str) -> List[VerificationResult]:
        """Run verification synchronously (called from thread executor)."""
        try:
            return self.orchestrator.verify_source(content, uri)
        except Exception as e:
            logger.error(f"Orchestrator verification failed: {e}")
            # Return empty results on error
            return []

    def _convert_to_diagnostics(self, results: List[VerificationResult], content: str) -> List[lsp.Diagnostic]:
        """Convert verification results to LSP diagnostics."""
        diagnostics = []
        lines = content.split('\n')
        
        for result in results:
            try:
                # Parse the content to find function and assertion locations
                tree = ast.parse(content)
                
                # Find the function node
                function_node = None
                for node in ast.walk(tree):
                    if isinstance(node, ast.FunctionDef) and node.name == result.function_name:
                        function_node = node
                        break
                
                if not function_node:
                    continue
                
                # Add diagnostics for failed assertions
                for failed_assertion in result.failed_assertions:
                    diagnostic = self._create_assertion_diagnostic(
                        failed_assertion, 
                        function_node, 
                        content, 
                        lsp.DiagnosticSeverity.ERROR,
                        result.counterexamples
                    )
                    if diagnostic:
                        diagnostics.append(diagnostic)
                
                # Add informational diagnostics for verified assertions
                for verified_assertion in result.verified_assertions:
                    diagnostic = self._create_assertion_diagnostic(
                        verified_assertion, 
                        function_node, 
                        content, 
                        lsp.DiagnosticSeverity.INFORMATION
                    )
                    if diagnostic:
                        diagnostics.append(diagnostic)
                
                # Add diagnostics for errors
                for error in result.errors:
                    error_diagnostic = lsp.Diagnostic(
                        range=lsp.Range(
                            start=lsp.Position(line=function_node.lineno - 1, character=0),
                            end=lsp.Position(line=function_node.lineno - 1, character=len(lines[function_node.lineno - 1]) if function_node.lineno <= len(lines) else 0)
                        ),
                        message=f"Verification error in {result.function_name}: {error}",
                        severity=lsp.DiagnosticSeverity.WARNING,
                        source="axiomander"
                    )
                    diagnostics.append(error_diagnostic)
                    
            except Exception as e:
                logger.error(f"Error creating diagnostics for {result.function_name}: {e}")
        
        return diagnostics

    def _create_assertion_diagnostic(
        self, 
        assertion_desc: str, 
        function_node: ast.FunctionDef, 
        content: str,
        severity: lsp.DiagnosticSeverity,
        counterexamples: Optional[List[Dict[str, Any]]] = None
    ) -> Optional[lsp.Diagnostic]:
        """Create diagnostic for a specific assertion."""
        try:
            lines = content.split('\n')
            
            # Extract the assertion text from the description
            # Format is typically "AssertionType: assertion_text"
            if ": " in assertion_desc:
                assertion_text = assertion_desc.split(": ", 1)[1]
            else:
                assertion_text = assertion_desc
            
            # Find the assertion in the function
            for node in ast.walk(function_node):
                if isinstance(node, ast.Assert):
                    node_text = ast.unparse(node.test)
                    if node_text == assertion_text:
                        # Create diagnostic at the assertion location
                        line_num = node.lineno - 1  # Convert to 0-based
                        line_content = lines[line_num] if line_num < len(lines) else ""
                        
                        # Find the assert statement in the line
                        assert_start = line_content.find("assert")
                        if assert_start == -1:
                            assert_start = 0
                        
                        message = assertion_desc
                        
                        # Add counterexample information if available
                        if counterexamples and severity == lsp.DiagnosticSeverity.ERROR:
                            relevant_ce = next(
                                (ce for ce in counterexamples if assertion_text in ce.get("assertion", "")), 
                                None
                            )
                            if relevant_ce and "counterexample" in relevant_ce:
                                ce_text = ", ".join(f"{k}={v}" for k, v in relevant_ce["counterexample"].items())
                                message += f" | Counterexample: {ce_text}"
                        
                        return lsp.Diagnostic(
                            range=lsp.Range(
                                start=lsp.Position(line=line_num, character=assert_start),
                                end=lsp.Position(line=line_num, character=len(line_content))
                            ),
                            message=message,
                            severity=severity,
                            source="axiomander",
                            code="assertion_verification"
                        )
            
        except Exception as e:
            logger.error(f"Error creating assertion diagnostic: {e}")
        
        return None

    async def _publish_diagnostics(self, uri: str, diagnostics: List[lsp.Diagnostic]):
        """Publish diagnostics to the client."""
        self.publish_diagnostics(uri, diagnostics)
        logger.debug(f"Published {len(diagnostics)} diagnostics for {uri}")


def create_axiomander_server():
    """Create a language server protocol instance with Axiomander features."""
    # Create a simple server info object 
    class ServerInfo:
        name = "axiomander-lsp"
        version = "v0.1.0"
    
    server_info = ServerInfo()
    
    # Create protocol with proper parameters
    return AxiomanderLSP(server_info, default_converter())


def main():
    """Main entry point for LSP server."""
    
    # Setup logging
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        handlers=[
            logging.FileHandler('/tmp/axiomander-lsp.log'),
            logging.StreamHandler(sys.stderr) if len(sys.argv) > 1 and '--debug' in sys.argv else logging.NullHandler()
        ]
    )
    
    logger.info("Starting Axiomander LSP server...")
    
    async def run_server():
        """Run the LSP server asynchronously."""
        import threading
        from pygls.server import StdinAsyncReader, StdoutWriter, run_async
        
        # Create the protocol
        protocol = create_axiomander_server()
        
        # Create I/O handlers for stdin/stdout
        reader = StdinAsyncReader(sys.stdin)
        writer = StdoutWriter(sys.stdout)
        
        # Set up the protocol with the writer
        protocol.set_writer(writer)
        
        # Create stop event
        stop_event = threading.Event()
        
        # Run the server
        await run_async(stop_event, reader, protocol)
    
    # Create and run the server
    try:
        asyncio.run(run_server())
    except Exception as e:
        logger.error(f"Failed to start LSP server: {e}")
        sys.exit(1)


# Legacy compatibility functions
def create_server():
    """Create and return a server instance for compatibility."""
    return create_axiomander_server()


class AxiomanderLSPServer:
    """Legacy wrapper for backwards compatibility."""
    
    def __init__(self):
        logger.warning("AxiomanderLSPServer class is deprecated, use main() function instead")
        self._server = None
    
    def start_server(self, host: str = "localhost", port: int = 0):
        """Legacy method - just calls main()."""
        main()


if __name__ == "__main__":
    main()
