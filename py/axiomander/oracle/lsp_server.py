"""
LSP server for axiomander — real-time verification diagnostics.

Publishes diagnostics after each document change using the incremental
verification cache for fast feedback.

Usage: python3 -m oracle.lsp_server
"""

import ast
import asyncio
import logging
import time

from lsprotocol import types as lsp
from pygls.lsp.server import LanguageServer

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("axiomander-lsp")

server = LanguageServer("axiomander-lsp", "v0.4.0")
DEBOUNCE_SECONDS = 1.0

_pending: dict[str, asyncio.Task | None] = {}


def _compute_diagnostics(source: str) -> list[lsp.Diagnostic]:
    diagnostics: list[lsp.Diagnostic] = []

    try:
        tree = ast.parse(source)
        funcs = [n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)]
    except SyntaxError as e:
        return [lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=max(0, (e.lineno or 1) - 1), character=0),
                end=lsp.Position(line=max(0, (e.lineno or 1) - 1), character=99),
            ),
            message=f"Syntax error: {e.msg}",
            severity=lsp.DiagnosticSeverity.Error,
            source="axiomander",
        )]

    if not funcs:
        return diagnostics

    from axiomander.oracle.mcp_server import tool_verify_changed
    from axiomander.oracle.cache import VerificationCache
    try:
        result = tool_verify_changed({"source": source})
    except Exception:
        return diagnostics

    # Handle "All functions up to date" — check cache for each function
    if "All functions up to date" in result:
        cache = VerificationCache()
        for node in funcs:
            from axiomander.oracle.mcp_server import _compute_hashes
            h = _compute_hashes(source, node.name)
            if h:
                cached = cache.lookup(node.name, h)
                if cached and cached.is_proved():
                    diagnostics.append(lsp.Diagnostic(
                        range=lsp.Range(
                            start=lsp.Position(line=node.lineno - 1, character=0),
                            end=lsp.Position(line=node.lineno - 1, character=0),
                        ),
                        message=f"✓ {node.name} proved (cached)",
                        severity=lsp.DiagnosticSeverity.Information,
                        source="axiomander",
                    ))
                else:
                    diagnostics.append(lsp.Diagnostic(
                        range=lsp.Range(
                            start=lsp.Position(line=node.lineno - 1, character=0),
                            end=lsp.Position(line=node.lineno - 1, character=0),
                        ),
                        message=f"⚠ {node.name} not proved",
                        severity=lsp.DiagnosticSeverity.Warning,
                        source="axiomander",
                    ))
        return diagnostics

    in_table = False
    for line in result.splitlines():
        line = line.strip()
        if line.startswith("| Function"):
            in_table = True
            continue
        if not in_table or not line.startswith("| `"):
            continue

        parts = [p.strip() for p in line.split("|")]
        if len(parts) < 4:
            continue
        func_name = parts[1].strip("`")
        status = parts[2].strip()
        note = parts[5].strip() if len(parts) > 5 else ""

        func_line = 0
        for node in funcs:
            if node.name == func_name:
                func_line = node.lineno - 1
                break

        if status == "✓":
            severity = lsp.DiagnosticSeverity.Information
            msg = f"✓ {func_name} proved"
            if note and "cached" in note:
                msg += " (cached)"
        elif status == "✗":
            severity = lsp.DiagnosticSeverity.Warning
            msg = f"✗ {func_name} — {note}" if note else f"✗ {func_name} not proved"
        else:
            continue

        diagnostics.append(lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=func_line, character=0),
                end=lsp.Position(line=func_line, character=0),
            ),
            message=msg,
            severity=severity,
            source="axiomander",
        ))

    return diagnostics


async def _verify_after_delay(uri: str, source: str):
    await asyncio.sleep(DEBOUNCE_SECONDS)
    t0 = time.time()
    diagnostics = _compute_diagnostics(source)
    elapsed = (time.time() - t0) * 1000
    server.text_document_publish_diagnostics(
        lsp.PublishDiagnosticsParams(uri=uri, diagnostics=diagnostics)
    )
    logger.info(f"{uri.rsplit('/', 1)[-1]}: {len(diagnostics)} diags ({elapsed:.0f}ms)")


def _trigger_verify(uri: str, source: str):
    if not uri.endswith(".py"):
        return
    task = _pending.get(uri)
    if task and not task.done():
        task.cancel()
    _pending[uri] = asyncio.ensure_future(_verify_after_delay(uri, source))


@server.feature(lsp.TEXT_DOCUMENT_DID_OPEN)
def did_open(ls: LanguageServer, params: lsp.DidOpenTextDocumentParams):
    _trigger_verify(params.text_document.uri, params.text_document.text)


@server.feature(lsp.TEXT_DOCUMENT_DID_CHANGE)
def did_change(ls: LanguageServer, params: lsp.DidChangeTextDocumentParams):
    changes = params.content_changes
    if changes:
        _trigger_verify(params.text_document.uri, changes[-1].text)


@server.feature(lsp.TEXT_DOCUMENT_DID_SAVE)
def did_save(ls: LanguageServer, params: lsp.DidSaveTextDocumentParams):
    doc = ls.workspace.get_text_document(params.text_document.uri)
    _trigger_verify(params.text_document.uri, doc.source)


@server.feature(lsp.TEXT_DOCUMENT_DID_CLOSE)
def did_close(ls: LanguageServer, params: lsp.DidCloseTextDocumentParams):
    ls.text_document_publish_diagnostics(
        lsp.PublishDiagnosticsParams(uri=params.text_document.uri, diagnostics=[])
    )


def main():
    logger.info("axiomander LSP server starting")
    server.start_io()


if __name__ == "__main__":
    main()
