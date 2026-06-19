"""
LSP server for axiomander -- real-time verification diagnostics.

Publishes diagnostics after each document change using the Iris
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

    from oracle.iris_pipeline import _iris_cache_get

    for node in funcs:
        try:
            cached = _iris_cache_get(source, node.name)
        except Exception:
            continue
        if cached and cached.is_proved():
            diagnostics.append(lsp.Diagnostic(
                range=lsp.Range(
                    start=lsp.Position(line=node.lineno - 1, character=0),
                    end=lsp.Position(line=node.lineno - 1, character=0),
                ),
                message=f"{node.name} proved (cached)",
                severity=lsp.DiagnosticSeverity.Information,
                source="axiomander",
            ))
        elif cached:
            diagnostics.append(lsp.Diagnostic(
                range=lsp.Range(
                    start=lsp.Position(line=node.lineno - 1, character=0),
                    end=lsp.Position(line=node.lineno - 1, character=0),
                ),
                message=f"{node.name} not proved",
                severity=lsp.DiagnosticSeverity.Warning,
                source="axiomander",
            ))

    return diagnostics


def _schedule_diagnostics(uri: str, source: str):
    async def _run():
        await asyncio.sleep(DEBOUNCE_SECONDS)
        task = _pending.get(uri)
        if task is None:
            return
        t0 = time.monotonic()
        diagnostics = _compute_diagnostics(source)
        elapsed = time.monotonic() - t0
        logger.info("diagnostics for %s: %d items in %.2fs", uri, len(diagnostics), elapsed)
        server.text_document_publish_diagnostics(
            lsp.PublishDiagnosticsParams(uri=uri, diagnostics=diagnostics)
        )

    task = asyncio.create_task(_run())
    _pending[uri] = task
    task.add_done_callback(lambda _: _pending.pop(uri, None))


@server.feature(lsp.TEXT_DOCUMENT_DID_OPEN)
def did_open(ls: LanguageServer, params: lsp.DidOpenTextDocumentParams):
    _schedule_diagnostics(params.text_document.uri, params.text_document.text)


@server.feature(lsp.TEXT_DOCUMENT_DID_CHANGE)
def did_change(ls: LanguageServer, params: lsp.DidChangeTextDocumentParams):
    text = params.content_changes[0].text
    _schedule_diagnostics(params.text_document.uri, text)


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
