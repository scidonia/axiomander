# Design-by-Contract Agent System – Software Development Plan

> **Working title:** Axiomander
> **Primary environment:** VSCode + LSP-driven agent graph
> **Repository:** `axiomander` (Python core), plus new VSCode / LSP projects

---

## 1. Vision and Objectives

### 1.1 Vision

Create an *interactive design-by-contract programming environment* where:

- Contracts are first‑class: preconditions, postconditions, invariants, and cross‑module specs.
- An **agentic graph** (LLM-powered) helps the developer:
  - Understand and navigate contracts.
  - Propose and implement code that satisfies those contracts.
  - Maintain a global map of functions, files, and specifications.
- The system integrates seamlessly with **VSCode** via:
  - Language Server Protocol (LSP) for analysis, navigation, and diagnostics.
  - A VSCode extension for UI, commands, and agent chat.
- Access to the AI is gated via **API key / subscription** to support a SaaS model.

### 1.2 Objectives

1. Provide a stable **Python contract core** that:
   - Expresses contracts declaratively.
   - Can be evaluated at runtime.
   - Exposes a machine-readable model of all contracts in a project.
2. Provide an **LSP server** that:
   - Indexes code and contracts.
   - Supplies diagnostics, code actions, and symbol info.
   - Interfaces with the agent graph backend.
3. Provide a **VSCode extension** that:
   - Offers visualizations of the contract graph and completeness.
   - Has commands to “switch gears” (e.g. spec mode, implementation mode, refinement mode, refactor mode).
   - Handles authentication & subscription.
4. Provide a **backend / agent graph orchestrator** that:
   - Executes multi-step reasoning flows over code + contracts.
   - Integrates with a model provider.
   - Enforces per-user quotas and subscription checks.

---

## 2. High-Level Architecture

### 2.1 Components

1. **Core Contract Library (Python)**
   - Decorators and DSL for preconditions, postconditions, invariants.
   - Adornments for higher-level “overview contracts.”
   - Introspective API to enumerate contracts and attach metadata.

2. **Project Contract Indexer**
   - Scans the project’s Python files.
   - Identifies contract-decorated functions and logic modules (`logic.py` per contract).
   - Builds a project-wide **contract graph**:
     - Functions, their specs, their dependencies, completeness flags.

3. **LSP Server**
   - Implements:
     - `textDocument/hover`, `textDocument/definition`, `textDocument/codeAction`,
       `textDocument/diagnostic`, `workspace/symbol`, etc.
   - Provides:
     - Contract-awareness (hover shows contract summary).
     - Diagnostics for missing / incomplete contracts.
     - Code actions to auto-generate contract stubs or tests.
   - Exposes a JSON-RPC/command interface for the agent graph.

4. **Agent Graph Backend**
   - Orchestrates multi-step LLM workflows (e.g. via a Python microservice):
     - “Analyze project → identify contract gaps → propose contracts.”
     - “Given aim → decompose into subcontracts → synthesize stubs.”
   - Maintains state per session (map of functions, files, contracts).
   - Gated by **API key**, integrated with billing/subscription backend.

5. **VSCode Extension**
   - UI elements:
     - Contract graph / completeness panel.
     - Tree view of contracts and their status.
     - Agent chat view (task-based commands).
   - Command palette integration:
     - “Design by Contract: Analyze Project”
     - “Design by Contract: Generate Contracts for Selection”
     - “Design by Contract: Switch to Spec Mode / Impl Mode / Refactor Mode”
   - Connects to LSP server and agent backend.
   - Manages auth (prompt for API key, etc.).

6. **Subscription & Auth Layer**
   - Minimal SaaS backend or usage of a third-party billing platform.
   - Tracks:
     - Users, API keys.
     - Subscription status.
     - Usage metrics (number of agent calls, tokens, etc.)

---

## 3. Development Phases & Milestones

### Phase 0 – Foundations & Cleanup (Week 1–2)

**Goals:**
- Make the existing `contracts` repo stable and introspectable.
- Clarify the contract DSL and metadata model.

**Tasks:**
1. **Audit current contracts library**
   - Document current decorators and behaviors.
   - Identify gaps (e.g., invariants, contract composition, async support).
2. **Define contract metadata schema**
   - Standard fields: `name`, `module`, `file`, `line`, `preconditions`, `postconditions`,
     `invariants`, `tags`, `status`, `docstring`
   - Decide on a representation (e.g. Python dataclasses + serializable JSON).
3. **Implement introspection API**
   - Functions to enumerate all contracts in a module/package.
   - Provide `to_dict()` / JSON export for each contract.
4. **Create a small test project**
   - Example “toy” project using contracts.
   - Used later for integration testing in LSP and VSCode.

**Deliverables:**
- Updated Python package (`axiomander`) with introspection.
- Documentation for the contract DSL and metadata format.
- Example project demonstrating typical usage.

**Exception Design:**
- Use exceptions instead of `pass` for unimplemented code to maintain type correctness.
- Create a root exception class for logical exceptions.
- Specific exceptions needed:
  - `ImplementThis` - for code that should be implemented
  - `DontImplementThis` - for code that should not be implemented
  - Validation exceptions - for contract validation failures

**Git Repository Requirement:**
- All projects using axiomander must be in a git repository.
- The agent system requires git history to track changes and understand project evolution.
- This enables the agent to provide better context-aware suggestions and maintain change history.

---

### Phase 1 – Contract Indexer & Contract Graph (Week 2–4)

**Goals:**
- Build a project-wide view of all contracts.
- Expose a “contract graph” that both LSP and agent backend can use.

**Tasks:**
1. **Project scanner**
   - Given a project root:
     - Recursively load Python modules.
     - Identify contract-decorated functions.
     - Identify `logic.py` files associated with contracts.
2. **Build contract graph**
   - Nodes:
     - Functions, methods, classes, “overview contract modules.”
   - Edges:
     - Calls/uses (approximate, maybe using static analysis or AST).
     - “Implements,” “refines,” or “depends on” relationships.
   - Annotate nodes with completeness:
     - e.g. `contract_defined`, `impl_missing`, `tests_missing`.
3. **Persistence and incremental updates**
   - Decide on an on-disk format (e.g. JSON) for the contract graph.
   - Support incremental re-scan based on file changes (later tied to LSP).
4. **CLI tool**
   - `contracts map` → prints or dumps contract graph.
   - Options to output:
     - JSON, GraphViz, or simple text summary.

**Deliverables:**
- Python library: `axiomander.index` module for scanning and graph building.
- CLI: `axiomander map` command.
- Contract graph output for the sample project.

---

### Phase 2 – LSP Server (Week 4–7)

**Goals:**
- Provide a basic LSP implementation focusing on contract-aware features.
- Integrate with the contract indexer and contract graph.

**Tasks:**
1. **LSP scaffolding**
   - Choose an LSP framework (e.g., `pygls` or custom).
   - Implement basic handlers:
     - `initialize`, `textDocument/didOpen`, `textDocument/didChange`, `textDocument/didSave`.
2. **Diagnostics and indexing**
   - On save / open:
     - Update the contract graph for changed files.
     - Recompute diagnostics:
       - Missing pre/post conditions.
       - Contract syntax issues.
       - Mismatched types (if you integrate with type hints).
3. **Hover and definitions**
   - Hover on a function:
     - Show contract summary (pre, post, invariants).
   - “Go to definition”:
     - Jump from contract metadata (e.g. in a contract panel) to code.
4. **Code actions**
   - Quick fixes:
     - “Generate contract stub” for a function lacking contracts.
     - “Convert docstring spec → contract decorators” (if feasible).
5. **Custom LSP commands for agent graph**
   - Define custom commands, e.g.:
     - `axiomander/analyzeProject`
     - `axiomander/generateContractsForRange`
     - `axiomander/decomposeAimIntoContracts`
   - These will call out to the agent backend.

**Deliverables:**
- Running LSP server with:
  - Basic diagnostics for contracts.
  - Hovers and code actions.
- Instructions on how to run LSP standalone (e.g., via CLI).

---

### Phase 3 – Agent Graph Backend (Week 6–10)

**Goals:**
- Provide an HTTP or WebSocket API that runs agent flows.
- Integrate with the contract graph and LSP commands.

**Tasks:**
1. **Backend scaffolding**
   - Implement lightweight service (e.g. FastAPI, Flask, or similar).
   - Endpoints:
     - `/analyze-project`
     - `/generate-contracts`
     - `/decompose-aim`
     - `/refactor-for-contracts`
2. **Agent graph design**
   - Define major *modes* or *flows*:
     - **Aim → Contract Decomposition**
       - Input: aim description + project context.
       - Output: list of high-level contracts / modules to create.
     - **Contract Completion**
       - Given a partially specified contract, propose missing parts.
     - **Implementation Synthesis**
       - Given a contract, propose or edit code to satisfy it.
     - **Refactor**
       - Analyze existing code to improve contract clarity and modularity.
   - Implement each mode as:
     - A sequence/graph of LLM calls.
     - Each step anchored to explicit inputs/outputs:
       - “Read contract graph,” “select region,” “propose diff,” etc.
3. **Project context loading**
   - API to ingest:
     - Current contract graph (from `axiomander.index`).
     - Relevant source snippets.
   - Mechanism to limit context size (e.g., top-N relevant nodes).
4. **Auth and API key handling**
   - Middleware to:
     - Validate API key.
     - Check subscription / quota.
5. **Observability**
   - Logging for:
     - Requests, responses, errors.
     - Token usage (where available from the model provider).
   - Simple metrics (for future billing/analytics).

**Deliverables:**
- Backend service with documented REST (or WS) API.
- Working agent flows for:
  - Analyzing project.
  - Generating and refining contracts.
  - Generating implementation suggestions.

---

### Phase 4 – VSCode Extension (Week 8–12)

**Goals:**
- Build the primary user interface.
- Connect LSP and agent backend into a coherent experience.

**Tasks:**
1. **Extension scaffolding**
   - Create VSCode extension project (TypeScript).
   - Activate on Python projects and/or presence of `axiomander` config.
2. **LSP integration**
   - Launch / connect to the LSP server.
   - Wire up:
     - Diagnostics in the VSCode “Problems” panel.
     - Hover and code actions from the LSP.
3. **Views & panels**
   - **Contract Graph Panel**
     - Tree view:
       - By module → function → contract.
       - Show completeness as icons / badges.
     - Click → jump to source.
   - **Agent Chat Panel**
     - Custom webview or panel.
     - Messages:
       - User: aim, commands.
       - Agent: responses, suggested diffs.
4. **Commands**
   - `designByContract.analyzeProject`
   - `designByContract.generateContractsForSelection`
   - `designByContract.decomposeAim`
   - `designByContract.refactorForContracts`
   - Bind commands to:
     - Context menu on files/functions.
     - Command Palette.
5. **Authentication UI**
   - Settings for:
     - API key entry.
     - Endpoint configuration (dev vs prod).
   - Status bar item showing connection/subscription status.
6. **Diff application**
   - When agent suggests code changes:
     - Show as an inline diff (using VSCode’s `WorkspaceEdit` and diff views).
     - User confirms before applying.

**Deliverables:**
- VSCode extension `.vsix` that:
  - Talks to LSP server.
  - Talks to agent backend.
  - Exposes contract graph panel and agent chat.
- Initial UX for flow: “Write aim → decompose into contracts → generate stubs → implement.”

---

### Phase 5 – Subscription & SaaS Hardening (Week 10–14)

**Goals:**
- Make the system shippable as a paid product.
- Ensure reliability, observability, and minimal friction.

**Tasks:**
1. **User management**
   - Integrate with a billing provider (e.g., Stripe) or custom minimal system.
   - API for:
     - Creating API keys.
     - Verifying subscription and quotas.
2. **Rate limiting / quotas**
   - Per-key usage limits.
   - Friendly error messages on overuse.
3. **Deployment**
   - Containerize backend (Docker).
   - Staging and production environments.
4. **Telemetry (opt-in)**
   - From VSCode extension:
     - High-level actions (e.g., “analyze project” used).
     - Errors.
   - From backend:
     - Latency, error rates, token usage (if accessible).
5. **Documentation & onboarding**
   - Quick-start guide:
     - Install `axiomander` Python package.
     - Install VSCode extension.
     - Add API key.
     - Run “Analyze project.”
   - Screencast or walkthrough (later).

**Deliverables:**
- Hosted backend (staging + prod).
- Billing integration.
- Public beta-ready release.

---

## 4. Detailed Work Breakdown (WBS)

### 4.1 Core & Storage

- [x] Finalize component metadata schema and storage structure.
- [x] Create exception hierarchy (root class, ImplementThis, DontImplementThis, validation exceptions).
- [x] Implement component storage manager.
- [x] Implement component compiler with dependency resolution.
- [x] Implement component graph builder.
- [x] Implement CLI for component management and compilation.
- [ ] Write unit tests for storage and compilation.

### 4.2 LSP Server

- [ ] LSP scaffolding (initialize, configuration).
- [ ] File change handling and incremental re-indexing.
- [ ] Diagnostics for components:
  - [ ] Missing components.
  - [ ] Incomplete components (preconditions without postconditions).
- [ ] Hover provider (component → contract summary).
- [ ] Code actions:
  - [ ] Generate component stubs.
  - [ ] Compile components to modules.
  - [ ] Resync changes from compiled modules.
- [ ] Custom commands for agent graph.
- [ ] Integration tests with sample project.

### 4.3 Agent Graph Backend

- [ ] Backend scaffolding and endpoints.
- [ ] Model provider integration.
- [ ] Implement mode-specific flows:
  - [ ] Specification Mode: Component contract generation and refinement.
  - [ ] Refinement Mode: Component decomposition and architecture.
  - [ ] Implementation Mode: Code synthesis from component contracts.
  - [ ] Verification Mode: Test generation and validation.
  - [ ] Refactor Mode: Component restructuring with contract preservation.
- [ ] Context loader for component graph + source.
- [ ] Mode transition logic and workflow guidance.
- [ ] Auth middleware: API keys and quotas.
- [ ] Logging, metrics, and error handling.

### 4.4 VSCode Extension

- [ ] Extension scaffolding.
- [ ] Connect to LSP server.
- [ ] Contract graph panel with refinement hierarchy.
- [ ] Mode-specific UI panels:
  - [ ] Specification panel for contract editing.
  - [ ] Refinement tree view for function decomposition.
  - [ ] Implementation diff view with contract annotations.
  - [ ] Verification dashboard for contract compliance.
  - [ ] Refactoring suggestions with impact analysis.
- [ ] Agent chat panel / webview.
- [ ] Mode switching commands and status bar indicator.
- [ ] Command palette integration for all modes.
- [ ] Authentication settings and status bar item.
- [ ] Diff application support with contract validation.
- [ ] Workflow guidance and mode transition suggestions.
- [ ] UX polish and iconography.

### 4.5 SaaS Layer & Ops

- [ ] Billing provider integration.
- [ ] Key provisioning API.
- [ ] Rate limiting & quotas.
- [ ] Dockerization & deployment.
- [ ] Monitoring dashboards and alerts.

---

## 5. UX Flows (“Switching Gears”)

### 5.1 Spec Mode

1. User selects a module or file.
2. Invokes “Design by Contract: Spec Mode”.
3. Agent:
   - Reads aim / existing contracts.
   - Proposes or refines high-level contracts.
4. LSP:
   - Generates contract stubs.
   - Highlights unsatisfied contracts.

### 5.2 Implementation Mode

1. User selects a contract in the Contract Graph panel.
2. Invokes “Design by Contract: Implement”.
3. Agent:
   - Retrieves relevant code and contract context.
   - Proposes an implementation or patch.
4. VSCode:
   - Shows diff; user accepts/rejects.

### 5.3 Refactor Mode

1. User runs “Analyze Project”.
2. Backend:
   - Identifies “contract smells” and structural issues.
3. Agent:
   - Proposes refactorings to improve contract clarity and modularity.
4. Developer:
   - Applies or rejects suggested changes.

---

## 6. Risks & Mitigations

- **Risk:** LSP and backend complexity slow progress.  
  **Mitigation:** Start with minimal viable features and iterate.

- **Risk:** Agent flows generate low-quality or unsafe code.  
  **Mitigation:** Always present changes as diffs requiring user approval; add “safety” checks in prompts.

- **Risk:** Performance issues on large projects.  
  **Mitigation:** Incremental indexing; limit scope of analysis; allow user to restrict to specific directories.

- **Risk:** Subscription complexity / billing bugs.  
  **Mitigation:** Start with simple monthly subscription + API key; add complexity later.

---

## 7. Immediate Next Steps (for you)

1. **Finalize DSL and metadata schema** in the `axiomander` repo.
2. **Prototype the contract indexer** and `axiomander map` CLI using a small sample project.
3. **Pick LSP stack** (e.g. `pygls`) and create a barebones LSP server linked to the indexer.
4. **Bootstrap VSCode extension** that:
   - Starts the LSP.
   - Shows basic diagnostics.
5. In parallel, **outline agent flows** in pseudo-code and decide how they will be configured (YAML, Python graph, etc.).

Once these are in place, you’ll have an **end-to-end thin slice**:  
from contracts in code → indexed graph → LSP diagnostics → VSCode UI → agent suggestions (even if very minimal).  
Then iterate toward completeness and polish.

