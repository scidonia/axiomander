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
import tempfile
import os

import lsprotocol.types as lsp
from pygls.lsp.server import LanguageServer

from ..verification.orchestrator import VerificationOrchestrator, VerificationResult
from ..ast.assertion_finder import AssertionFinder, AssertionType, AssertionInfo
from ..ast.parser import ASTParser, ParsedCode


logger = logging.getLogger(__name__)

# Global state for the server
verification_cache: Dict[str, List[VerificationResult]] = {}
last_verification: Dict[str, float] = {}
pending_verifications: Dict[str, asyncio.Task] = {}
orchestrator = VerificationOrchestrator()
verification_delay = 1.0  # seconds

# Create the language server instance
server = LanguageServer("axiomander-lsp", "v1.0")


async def debounced_verify_document(uri: str, delay: float = verification_delay):
    """Verify a document after a delay to avoid too frequent checks."""
    # Cancel any pending verification for this document
    if uri in pending_verifications:
        pending_verifications[uri].cancel()

    async def verify_after_delay():
        await asyncio.sleep(delay)
        await verify_document(uri)
        if uri in pending_verifications:
            del pending_verifications[uri]

    # Start new verification task
    pending_verifications[uri] = asyncio.create_task(verify_after_delay())


async def verify_document(uri: str):
    """Verify a document and publish diagnostics."""
    try:
        # Get the document content
        doc = server.workspace.get_text_document(uri)
        content = doc.source

        # Parse the AST to find function definitions and their line numbers
        try:
            tree = ast.parse(content)
        except SyntaxError as e:
            logger.warning(f"Syntax error in {uri}: {e}")
            # Publish syntax error as diagnostic
            diagnostic = lsp.Diagnostic(
                range=lsp.Range(
                    start=lsp.Position(
                        line=max(0, (e.lineno or 1) - 1),
                        character=max(0, (e.offset or 1) - 1),
                    ),
                    end=lsp.Position(
                        line=max(0, (e.lineno or 1) - 1),
                        character=max(0, (e.offset or 1) - 1) + 10,
                    ),
                ),
                message=f"Syntax error: {e.msg}",
                severity=lsp.DiagnosticSeverity.Error,
                source="axiomander",
                code="syntax_error",
            )
            server.text_document_publish_diagnostics(
                lsp.PublishDiagnosticsParams(uri=uri, diagnostics=[diagnostic])
            )
            return

        # Build a map of function names to their line numbers
        function_lines = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                function_lines[node.name] = node.lineno - 1  # Convert to 0-based

        # Use orchestrator to verify the source
        try:
            results = orchestrator.verify_source(content, uri)

            # Cache results
            verification_cache[uri] = results
            last_verification[uri] = time.time()

            # Convert results to diagnostics
            diagnostics = []

            for result in results:
                # Get the line number for this function
                func_line = function_lines.get(result.function_name, 0)

                # Create diagnostics for each verification result
                if result.success:
                    # Create a single success diagnostic per function instead of one per assertion
                    success_count = len(result.verified_assertions)
                    diagnostic = lsp.Diagnostic(
                        range=lsp.Range(
                            start=lsp.Position(line=func_line, character=0),
                            end=lsp.Position(line=func_line, character=50),
                        ),
                        message=f"✅ {result.function_name}: {success_count} assertions verified successfully",
                        severity=lsp.DiagnosticSeverity.Hint,
                        source="axiomander",
                        code="verification_success",
                    )
                    diagnostics.append(diagnostic)

                # Create error diagnostics for failed assertions
                for failed_assertion in result.failed_assertions:
                    diagnostic = lsp.Diagnostic(
                        range=lsp.Range(
                            start=lsp.Position(line=func_line, character=0),
                            end=lsp.Position(line=func_line, character=50),
                        ),
                        message=f"❌ Contract violation: {failed_assertion}",
                        severity=lsp.DiagnosticSeverity.Error,
                        source="axiomander",
                        code="verification_failed",
                    )
                    diagnostics.append(diagnostic)

                # Create error diagnostics for verification errors
                for error in result.errors:
                    diagnostic = lsp.Diagnostic(
                        range=lsp.Range(
                            start=lsp.Position(line=func_line, character=0),
                            end=lsp.Position(line=func_line, character=50),
                        ),
                        message=f"🔥 {result.function_name}: {error}",
                        severity=lsp.DiagnosticSeverity.Error,
                        source="axiomander",
                        code="verification_error",
                    )
                    diagnostics.append(diagnostic)

            # Publish diagnostics
            server.text_document_publish_diagnostics(
                lsp.PublishDiagnosticsParams(uri=uri, diagnostics=diagnostics)
            )

        except SyntaxError as e:
            logger.warning(f"Syntax error in {uri}: {e}")
            # Publish syntax error as diagnostic
            diagnostic = lsp.Diagnostic(
                range=lsp.Range(
                    start=lsp.Position(
                        line=max(0, (e.lineno or 1) - 1),
                        character=max(0, (e.offset or 1) - 1),
                    ),
                    end=lsp.Position(
                        line=max(0, (e.lineno or 1) - 1),
                        character=max(0, (e.offset or 1) - 1) + 10,
                    ),
                ),
                message=f"Syntax error: {e.msg}",
                severity=lsp.DiagnosticSeverity.Error,
                source="axiomander",
                code="syntax_error",
            )
            server.text_document_publish_diagnostics(
                lsp.PublishDiagnosticsParams(uri=uri, diagnostics=[diagnostic])
            )
            return

    except Exception as e:
        logger.error(f"Unexpected error verifying {uri}: {e}")
        # Publish general error
        diagnostic = lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=0, character=0),
                end=lsp.Position(line=0, character=100),
            ),
            message=f"Verification error: {str(e)}",
            severity=lsp.DiagnosticSeverity.Error,
            source="axiomander",
            code="general_error",
        )
        server.text_document_publish_diagnostics(
            lsp.PublishDiagnosticsParams(uri=uri, diagnostics=[diagnostic])
        )


@server.feature(lsp.TEXT_DOCUMENT_DID_OPEN)
async def did_open(params: lsp.DidOpenTextDocumentParams) -> None:
    """Handle document open event."""
    logger.info(f"Document opened: {params.text_document.uri}")
    await debounced_verify_document(params.text_document.uri)


@server.feature(lsp.TEXT_DOCUMENT_DID_CHANGE)
async def did_change(params: lsp.DidChangeTextDocumentParams) -> None:
    """Handle document change event."""
    logger.info(f"Document changed: {params.text_document.uri}")
    await debounced_verify_document(params.text_document.uri)


@server.feature(lsp.TEXT_DOCUMENT_DID_CLOSE)
async def did_close(params: lsp.DidCloseTextDocumentParams) -> None:
    """Handle document close event."""
    uri = params.text_document.uri
    logger.info(f"Document closed: {uri}")

    # Cancel any pending verification
    if uri in pending_verifications:
        pending_verifications[uri].cancel()
        del pending_verifications[uri]

    # Clear cache
    if uri in verification_cache:
        del verification_cache[uri]
    if uri in last_verification:
        del last_verification[uri]


@server.feature(lsp.TEXT_DOCUMENT_HOVER)
async def hover(params: lsp.HoverParams) -> Optional[lsp.Hover]:
    """Provide hover information."""
    uri = params.text_document.uri
    position = params.position

    # Get cached verification results
    if uri not in verification_cache:
        return None

    results = verification_cache[uri]

    # Create hover information from verification results
    if results:
        content_lines = []
        for result in results:
            content_lines.append(f"**Function: {result.function_name}**")

            if result.success:
                content_lines.append("✅ **Status**: All assertions verified")
            else:
                content_lines.append("❌ **Status**: Some assertions failed")

            content_lines.append(f"**Execution time**: {result.execution_time:.3f}s")

            if result.verified_assertions:
                content_lines.append("**Verified assertions**:")
                for assertion in result.verified_assertions:
                    content_lines.append(f"  - ✅ {assertion}")

            if result.failed_assertions:
                content_lines.append("**Failed assertions**:")
                for assertion in result.failed_assertions:
                    content_lines.append(f"  - ❌ {assertion}")

            if result.counterexamples:
                content_lines.append("**Counterexamples**:")
                for i, example in enumerate(result.counterexamples):
                    content_lines.append(f"  - Example {i + 1}: {example}")

            if result.errors:
                content_lines.append("**Errors**:")
                for error in result.errors:
                    content_lines.append(f"  - 🔥 {error}")

            content_lines.append("---")

        content = "\n".join(content_lines)

        return lsp.Hover(
            contents=lsp.MarkupContent(kind=lsp.MarkupKind.Markdown, value=content)
        )

    return None


@server.feature(
    lsp.TEXT_DOCUMENT_COMPLETION, lsp.CompletionOptions(trigger_characters=[".", "@"])
)
async def completion(params: lsp.CompletionParams) -> lsp.CompletionList:
    """Provide code completions for contract constructs."""
    completions = []

    # Basic contract completions
    completions.extend(
        [
            lsp.CompletionItem(
                label="@contract",
                kind=lsp.CompletionItemKind.Snippet,
                detail="Contract decorator",
                documentation="Add a contract decorator to a function",
                insert_text="@contract\ndef ${1:function_name}(${2:args}):\n    '''\n    requires: ${3:precondition}\n    ensures: ${4:postcondition}\n    '''\n    ${0:pass}",
                insert_text_format=lsp.InsertTextFormat.Snippet,
            ),
            lsp.CompletionItem(
                label="requires",
                kind=lsp.CompletionItemKind.Keyword,
                detail="Precondition",
                documentation="Add a precondition to a contract",
                insert_text="requires: ${1:condition}",
            ),
            lsp.CompletionItem(
                label="ensures",
                kind=lsp.CompletionItemKind.Keyword,
                detail="Postcondition",
                documentation="Add a postcondition to a contract",
                insert_text="ensures: ${1:condition}",
            ),
            lsp.CompletionItem(
                label="invariant",
                kind=lsp.CompletionItemKind.Keyword,
                detail="Loop invariant",
                documentation="Add a loop invariant",
                insert_text="invariant: ${1:condition}",
            ),
            lsp.CompletionItem(
                label="assert",
                kind=lsp.CompletionItemKind.Keyword,
                detail="Assertion",
                documentation="Add an assertion",
                insert_text="assert ${1:condition}, '${2:message}'",
            ),
        ]
    )

    return lsp.CompletionList(is_incomplete=False, items=completions)


@server.command("axiomander.verifyContract")
async def verify_contract_command(uri: str) -> None:
    """Command to verify contracts in a specific file."""
    logger.info(f"Verifying contracts in: {uri}")
    await verify_document(uri)


@server.command("axiomander.showSMT")
async def show_smt_command(uri: str) -> str:
    """Command to show SMT-LIB representation."""
    logger.info(f"Generating SMT for: {uri}")

    try:
        doc = server.workspace.get_text_document(uri)
        content = doc.source

        # Create a temporary file to use with the orchestrator
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".py", delete=False
        ) as temp_file:
            temp_file.write(content)
            temp_path = temp_file.name

        try:
            # Use orchestrator to get verification details - this would generate SMT internally
            results = orchestrator.verify_source(content, uri)

            smt_content = f"; SMT-LIB representation for {uri}\n\n"

            for result in results:
                smt_content += f"; Function: {result.function_name}\n"
                smt_content += f"; Success: {result.success}\n"
                smt_content += f"; Execution time: {result.execution_time}s\n\n"

                if result.verified_assertions:
                    smt_content += "; Verified assertions:\n"
                    for assertion in result.verified_assertions:
                        smt_content += f";   - {assertion}\n"
                    smt_content += "\n"

                if result.failed_assertions:
                    smt_content += "; Failed assertions:\n"
                    for assertion in result.failed_assertions:
                        smt_content += f";   - {assertion}\n"
                    smt_content += "\n"

                # Note: The actual SMT generation is internal to the orchestrator
                # In a full implementation, we'd need to expose the SMT translator
                smt_content += "; (Detailed SMT-LIB code would be generated here)\n\n"

        finally:
            # Clean up temporary file
            os.unlink(temp_path)

        return smt_content

    except Exception as e:
        return f"; Error generating SMT: {e}"


@server.command("axiomander.generateTest")
async def generate_test_command(uri: str) -> str:
    """Command to generate test cases for contracts."""
    logger.info(f"Generating tests for: {uri}")

    try:
        doc = server.workspace.get_text_document(uri)
        content = doc.source

        # Get verification results to understand what to test
        results = orchestrator.verify_source(content, uri)

        test_content = f"# Generated test cases for {uri}\n\n"
        test_content += "import pytest\n\n"

        for result in results:
            test_content += f"def test_{result.function_name}_contracts():\n"
            test_content += f'    """Test contracts for {result.function_name}"""\n'

            if result.verified_assertions:
                test_content += "    # Verified assertions:\n"
                for assertion in result.verified_assertions:
                    test_content += f"    #   - {assertion}\n"

            if result.failed_assertions:
                test_content += "    # Failed assertions (need fixing):\n"
                for assertion in result.failed_assertions:
                    test_content += f"    #   - {assertion}\n"

            if result.counterexamples:
                test_content += "    # Counterexamples found:\n"
                for i, example in enumerate(result.counterexamples):
                    test_content += f"    #   Example {i + 1}: {example}\n"

            test_content += "    # TODO: Implement actual test cases\n"
            test_content += "    pass\n\n"

        return test_content

    except Exception as e:
        return f"# Error generating tests: {e}"


def main():
    """Main entry point for the LSP server."""
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    )

    logger.info("Starting Axiomander LSP server...")

    # Start the server
    server.start_io()


if __name__ == "__main__":
    main()
