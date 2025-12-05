# LSP Server Implementation Plan

## Overview

The Axiomander LSP server will provide language server protocol support for component development, enabling rich IDE integration with VSCode and other LSP-compatible editors. The server will understand the component model and provide component-aware diagnostics, hover information, and code actions.

## Architecture

### Core Components

1. **LSP Server Foundation** (`src/axiomander/lsp/server.py`)
   - Built on `pygls` (Python LSP framework)
   - Handles standard LSP lifecycle (initialize, shutdown, etc.)
   - Manages workspace and document state

2. **Component Index** (`src/axiomander/lsp/index.py`)
   - Maintains in-memory index of all components
   - Tracks component file changes and dependencies
   - Provides fast lookup for component metadata

3. **Diagnostics Engine** (`src/axiomander/lsp/diagnostics.py`)
   - Analyzes components for completeness and correctness
   - Generates LSP diagnostics for missing/incomplete components
   - Validates contract consistency

4. **Hover Provider** (`src/axiomander/lsp/hover.py`)
   - Shows component metadata on hover
   - Displays contract information and dependencies
   - Provides quick documentation access

5. **Code Actions** (`src/axiomander/lsp/actions.py`)
   - "Create Component" action
   - "Generate missing files" (logical.py, implementation.py, test.py)
   - "Compile Components" action
   - "Resync from compiled output" action

6. **Custom Commands** (`src/axiomander/lsp/commands.py`)
   - Agent integration endpoints
   - Component management commands
   - Compilation and validation commands

8. **Agent Integration** (`src/axiomander/lsp/agent.py`)
   - Handles communication with agent backend
   - Progress updates for decomposition and analysis
   - Session state management with live updates

## File Structure

```
src/axiomander/lsp/
├── __init__.py
├── server.py          # Main LSP server
├── index.py           # Component indexing
├── diagnostics.py     # Diagnostic generation with progress streaming
├── hover.py           # Hover information
├── actions.py         # Code actions with progress updates
├── commands.py        # Custom LSP commands
├── sse.py             # Server-Sent Events manager
├── agent.py           # Agent backend integration with streaming
├── models.py          # LSP-specific data models
└── utils.py           # Utility functions
```

## Implementation Phases

### Phase 1: Foundation (Week 1)

**Goal:** Basic LSP server that can start and respond to initialization

**Tasks:**
1. Set up `pygls` dependency and basic server structure
2. Implement LSP lifecycle methods (initialize, initialized, shutdown)
3. Add workspace configuration handling
4. Create component index that loads from `.axiomander/components/`
5. Basic file watching for component directories

**Deliverables:**
- LSP server that starts without errors
- Can be connected to from VSCode
- Loads component index on startup
- Responds to basic LSP requests

### Phase 2: Component Awareness (Week 2)

**Goal:** Server understands component structure and provides basic diagnostics

**Tasks:**
1. Implement component file change detection
2. Add diagnostics for:
   - Missing component files (logical.py, implementation.py, test.py)
   - Invalid component.json structure
   - Missing required metadata fields
3. Basic hover support showing component metadata
4. Document symbol provider for component files

**Deliverables:**
- Real-time diagnostics for component issues
- Hover information showing component details
- File outline support for component files

### Phase 3: Advanced Features (Week 3)

**Goal:** Rich IDE experience with code actions and custom commands

**Tasks:**
1. Implement code actions:
   - "Create Component" from selection or cursor
   - "Generate missing component files"
   - "Add missing contracts"
2. Add custom LSP commands:
   - `axiomander/compile` - compile components
   - `axiomander/validate` - validate component graph
   - `axiomander/createComponent` - create new component
3. Enhanced diagnostics:
   - Contract validation errors
   - Dependency resolution issues
   - Compilation errors from component source

**Deliverables:**
- Full code action support
- Custom commands for component operations
- Comprehensive diagnostic coverage

### Phase 4: Agent Integration with Streaming (Week 4)

**Goal:** LSP server ready for agent backend integration with real-time streaming

**Tasks:**
1. Add agent integration commands:
   - `axiomander/analyzeProject` - project analysis with progress
   - `axiomander/generateContracts` - contract generation with LLM streaming
   - `axiomander/startDecomposition` - interactive decomposition with real-time updates
2. Session state management for agent interactions
3. Real-time LLM response streaming to VSCode
4. Progress reporting for all long-running operations
5. Error handling and recovery for agent failures

**Deliverables:**
- Agent-ready LSP server with streaming capabilities
- Session management for interactive workflows
- Real-time LLM response streaming
- Comprehensive progress reporting

## Technical Specifications

### LSP Capabilities

The server will advertise these capabilities:

```json
{
  "textDocumentSync": {
    "openClose": true,
    "change": 2,  // Incremental
    "save": true
  },
  "hoverProvider": true,
  "documentSymbolProvider": true,
  "codeActionProvider": {
    "codeActionKinds": [
      "quickfix",
      "refactor",
      "source"
    ]
  },
  "executeCommandProvider": {
    "commands": [
      "axiomander.compile",
      "axiomander.validate",
      "axiomander.createComponent",
      "axiomander.analyzeProject",
      "axiomander.generateContracts",
      "axiomander.startDecomposition"
    ]
  },
  "workspaceSymbolProvider": true
}
```

### Component Index Schema

```python
@dataclass
class ComponentIndexEntry:
    uid: str
    name: str
    component_type: ComponentType
    file_path: Path
    metadata: Component
    files: Dict[str, Path]  # logical.py, implementation.py, test.py
    last_modified: datetime
    diagnostics: List[Diagnostic]
    dependencies: List[str]
    dependents: List[str]
```

### Diagnostic Categories

1. **Error Level:**
   - Missing component.json
   - Invalid JSON structure
   - Missing required metadata fields
   - Circular dependencies

2. **Warning Level:**
   - Missing implementation files
   - Incomplete contracts
   - Unused components
   - Outdated compiled output

3. **Information Level:**
   - Component compilation successful
   - All contracts defined
   - Tests passing

### File Watching Strategy

- Watch `.axiomander/components/` recursively
- Debounce file changes (500ms) to avoid excessive reindexing
- Incremental updates for single component changes
- Full reindex for structural changes (new/deleted components)
- **SSE Integration**: Stream all file change events to connected clients

### Error Handling

1. **Component Loading Errors:**
   - Invalid JSON → diagnostic + skip component + SSE error event
   - Missing files → diagnostic + partial load + SSE warning
   - Permission errors → log + continue + SSE error notification

2. **LSP Protocol Errors:**
   - Malformed requests → return LSP error response
   - Internal errors → log + return generic error + SSE error event
   - Timeout on long operations → cancel + notify client via SSE

3. **SSE Connection Errors:**
   - Client disconnection → cleanup resources + log
   - Network issues → attempt reconnection with exponential backoff
   - Message delivery failures → queue messages + retry logic
   - Connection overflow → implement connection limits + queuing

4. **Agent Integration Errors:**
   - Backend unavailable → graceful degradation + SSE status update
   - Authentication failures → clear error messages via SSE
   - Rate limiting → queue requests with backoff + progress updates
   - Streaming interruption → resume from last checkpoint + notify client

5. **Real-time Update Errors:**
   - Failed to send SSE event → retry with exponential backoff
   - Client buffer overflow → implement flow control
   - Partial message delivery → implement message acknowledgment

## Configuration

### LSP Server Settings

```json
{
  "axiomander.lsp.componentPath": ".axiomander/components",
  "axiomander.lsp.compiledPath": "src",
  "axiomander.lsp.enableDiagnostics": true,
  "axiomander.lsp.enableCodeActions": true,
  "axiomander.lsp.agentBackendUrl": "https://api.axiomander.com",
  "axiomander.lsp.logLevel": "info",
  "axiomander.lsp.sse": {
    "enabled": true,
    "port": 8765,
    "maxConnections": 10,
    "heartbeatInterval": 30,
    "reconnectAttempts": 5,
    "messageQueueSize": 1000,
    "enableCompression": true
  },
  "axiomander.lsp.streaming": {
    "enableLLMStreaming": true,
    "chunkSize": 1024,
    "bufferTimeout": 100,
    "enableProgressUpdates": true,
    "progressUpdateInterval": 500
  }
}
```

### Workspace Configuration

The server will look for `.axiomander/config.json` and respect:
- Component storage paths
- Compilation settings
- Agent backend configuration
- Custom diagnostic rules

This plan provides a solid foundation for the LSP server.
