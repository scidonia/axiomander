#!/bin/bash
# Launch script for the verify-contracts MCP server
# This is called by opencode as an MCP tool.
# Ensure opam environment and PYTHONPATH are set.

eval $(opam env) 2>/dev/null
export PYTHONPATH="/home/gavin/dev/Personal/refactoring-robots"
export REFACTORING_ROBOTS_ROOT="/home/gavin/dev/Personal/refactoring-robots"
exec python3 -m py.oracle.mcp_server
