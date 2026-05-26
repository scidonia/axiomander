"""
Async test for the axiomander LSP server.

Verifies the server accepts initialize, processes didOpen/didChange,
and publishes diagnostics with verification results.
"""

import asyncio
import json
import os
import sys
import time


async def _read_message(reader: asyncio.StreamReader) -> dict | None:
    """Read one LSP message (Content-Length header + body)."""
    header = b""
    while True:
        try:
            ch = await asyncio.wait_for(reader.read(1), timeout=15.0)
        except asyncio.TimeoutError:
            return None
        if not ch:
            return None
        header += ch
        if header.endswith(b"\r\n\r\n"):
            break
    content_length = 0
    for line in header.decode().split("\r\n"):
        if line.startswith("Content-Length:"):
            content_length = int(line.split(":")[1].strip())
    body = b""
    while len(body) < content_length:
        chunk = await asyncio.wait_for(
            reader.read(content_length - len(body)), timeout=10.0
        )
        if not chunk:
            return None
        body += chunk
    return json.loads(body.decode())


def _encode(msg: dict) -> bytes:
    body = json.dumps(msg)
    header = f"Content-Length: {len(body)}\r\n\r\n"
    return header.encode() + body.encode()


async def _send(writer: asyncio.StreamWriter, msg: dict):
    writer.write(_encode(msg))
    await writer.drain()


async def test_lsp_server():
    """Full lifecycle test: init → didOpen → diagnostics → shutdown."""
    root = "/home/gavin/dev/Scidonia/axiomander"
    venv_python = f"{root}/.venv/bin/python3"

    proc = await asyncio.create_subprocess_exec(
        venv_python, "-m", "src.axiomander.lsp.server",
        stdin=asyncio.subprocess.PIPE,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
        env={**os.environ, "PYTHONPATH": f"{root}/py:{root}/src"},
        cwd=root,
    )

    try:
        # Check stderr for startup errors
        time.sleep(0.5)
        stderr_data = b""
        try:
            while True:
                chunk = await asyncio.wait_for(proc.stderr.read(4096), timeout=0.5)
                if not chunk:
                    break
                stderr_data += chunk
        except asyncio.TimeoutError:
            pass
        if stderr_data:
            print(f"stderr: {stderr_data.decode()[:500]}")
        # 1. Initialize
        await _send(proc.stdin, {
            "jsonrpc": "2.0", "id": 1, "method": "initialize",
            "params": {"processId": os.getpid(), "capabilities": {}},
        })
        msg = await _read_message(proc.stdout)
        assert msg is not None, "No response to initialize"
        assert msg.get("result", {}).get("serverInfo", {}).get("name") == "axiomander-lsp"
        print("✓ initialize")

        # 2. DidOpen
        source = "def add(a, b):\n    assert True\n    result = a + b\n    assert result == a + b\n    return result\n"
        await _send(proc.stdin, {
            "jsonrpc": "2.0", "method": "textDocument/didOpen",
            "params": {"textDocument": {
                "uri": "file:///test.py", "languageId": "python",
                "version": 1, "text": source,
            }},
        })

        # 3. Wait for diagnostics (debounce = 1s + verify time)
        start = time.time()
        diagnostics = []
        while time.time() - start < 10:
            msg = await _read_message(proc.stdout)
            if msg is None:
                break
            diags = msg.get("params", {}).get("diagnostics")
            if diags is not None:
                diagnostics = diags
                break

        assert len(diagnostics) > 0, f"No diagnostics received. Got: {msg}"
        print(f"✓ diagnostics: {len(diagnostics)}")
        for d in diagnostics:
            print(f"  [{d['severity']}] {d['message']}")

        # Verify content
        msgs = " ".join(d["message"] for d in diagnostics)
        assert "add" in msgs, f"Expected 'add' in diagnostics: {msgs}"
        print("✓ diagnostic content correct")

        # 4. Shutdown
        await _send(proc.stdin, {
            "jsonrpc": "2.0", "id": 2, "method": "shutdown",
        })
        msg = await _read_message(proc.stdout)
        assert msg is not None, "No shutdown response"
        await _send(proc.stdin, {
            "jsonrpc": "2.0", "method": "exit",
        })

    finally:
        try:
            proc.stdin.close()
        except Exception:
            pass
        try:
            await asyncio.wait_for(proc.wait(), timeout=5)
        except asyncio.TimeoutError:
            proc.kill()
            await proc.wait()

    print("\n✓ All LSP tests passed")


if __name__ == "__main__":
    asyncio.run(test_lsp_server())
