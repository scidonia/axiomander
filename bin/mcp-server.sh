#!/bin/bash
# Launch script for the axiomander MCP server
# This is called by opencode as an MCP tool.
# Ensure opam environment and PYTHONPATH are set.

eval $(opam env) 2>/dev/null
export PYTHONPATH="/home/gavin/dev/Scidonia/axiomander/py"
export AXIOMANDER_ROOT="/home/gavin/dev/Scidonia/axiomander"
exec python3 -m py.oracle.mcp_server
