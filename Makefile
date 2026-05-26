.PHONY: setup build test clean

# ─── Dependencies ─────────────────────────────────────────────────

setup: setup-coq setup-python setup-coqlsp

setup-coq:
	@echo "=== Coq ==="
	opam install --deps-only . 2>/dev/null || true
	dune build

setup-python:
	@echo "=== Python ==="
	uv sync
	uv pip install -e .

setup-coqlsp:
	@echo "=== coq-lsp MCP ==="
	cd vendor/mcp-coq-lsp/mcp-coq-lsp && npm install --omit=dev && npm run build

# ─── Build ────────────────────────────────────────────────────────

build: setup-coq
	dune build

# ─── Test ─────────────────────────────────────────────────────────

test: build
	eval $$(opam env) && PYTHONPATH=py uv run pytest py/tests/ -v

# ─── Oracle (interactive coq-lsp proving) ─────────────────────────

oracle-test:
	eval $$(opam env) && PYTHONPATH=py uv run python3 -c "\
		from oracle.mcp_server import _try_coqlsp_oracle; \
		from oracle.reporting import GoalStatus, ProofLevel; \
		source = open('py/examples/demo.py').read(); \
		goal = GoalStatus(name='demo', goal_statement='', level=ProofLevel.UNPROVED); \
		r = _try_coqlsp_oracle(source, 'add', goal); \
		print(f'Result: {r.level.value}')"

# ─── MCP Server ───────────────────────────────────────────────────

run-mcp:
	eval $$(opam env) && PYTHONPATH=py uv run python3 -m oracle.mcp_server

# ─── Clean ────────────────────────────────────────────────────────

clean:
	dune clean
	rm -rf /tmp/axiomander_ai_prove.v /tmp/axiomander_ai_prove.hash
