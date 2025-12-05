# LSP Server Implementation Plan

## Overview

The Axiomander LSP server will provide language server protocol support for component development, enabling rich IDE integration with VSCode and other LSP-compatible editors. The server will understand the component model and provide component-aware diagnostics, hover information, and code actions. **Crucially, all real-time interactions will use Server-Sent Events (SSE) for progress updates, streaming LLM responses, and incremental updates.**

## Architecture

### Core Components

1. **LSP Server Foundation** (`src/axiomander/lsp/server.py`)
   - Built on `pygls` (Python LSP framework)
   - Handles standard LSP lifecycle (initialize, shutdown, etc.)
   - Manages workspace and document state
   - **SSE Integration**: Establishes SSE connections for real-time updates

2. **Component Index** (`src/axiomander/lsp/index.py`)
   - Maintains in-memory index of all components
   - Tracks component file changes and dependencies
   - Provides fast lookup for component metadata
   - **SSE Updates**: Streams index changes to connected clients

3. **Diagnostics Engine** (`src/axiomander/lsp/diagnostics.py`)
   - Analyzes components for completeness and correctness
   - Generates LSP diagnostics for missing/incomplete components
   - Validates contract consistency
   - **SSE Progress**: Streams diagnostic progress for large projects

4. **Hover Provider** (`src/axiomander/lsp/hover.py`)
   - Shows component metadata on hover
   - Displays contract information and dependencies
   - Provides quick documentation access

5. **Code Actions** (`src/axiomander/lsp/actions.py`)
   - "Create Component" action
   - "Generate missing files" (logical.py, implementation.py, test.py)
   - "Compile Components" action
   - "Resync from compiled output" action
   - **SSE Progress**: Streams action execution progress

6. **Custom Commands** (`src/axiomander/lsp/commands.py`)
   - Agent integration endpoints
   - Component management commands
   - Compilation and validation commands
   - **SSE Orchestration**: Manages SSE streams for long-running operations

7. **SSE Manager** (`src/axiomander/lsp/sse.py`)
   - Manages Server-Sent Event connections
   - Handles client subscription/unsubscription
   - Routes events to appropriate clients
   - Manages connection lifecycle and error recovery

8. **Agent Integration** (`src/axiomander/lsp/agent.py`)
   - Handles communication with agent backend
   - **SSE Streaming**: Real-time LLM response streaming
   - Progress updates for decomposition and analysis
   - Session state management with live updates

## File Structure

```
src/axiomander/lsp/
├── __init__.py
├── server.py          # Main LSP server with SSE integration
├── index.py           # Component indexing with SSE updates
├── diagnostics.py     # Diagnostic generation with progress streaming
├── hover.py           # Hover information
├── actions.py         # Code actions with progress updates
├── commands.py        # Custom LSP commands with SSE orchestration
├── sse.py             # Server-Sent Events manager
├── agent.py           # Agent backend integration with streaming
├── models.py          # LSP-specific data models including SSE events
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

### Phase 4: SSE Integration (Week 4)

**Goal:** Real-time communication with VSCode extension via Server-Sent Events

**Tasks:**
1. Implement SSE manager for client connection handling
2. Add SSE endpoints for:
   - Component index updates
   - Diagnostic progress streaming
   - Compilation progress
   - Agent interaction streaming
3. Integrate SSE with existing LSP commands
4. Client connection lifecycle management
5. Error handling and reconnection logic

**Deliverables:**
- SSE manager with client connection handling
- Real-time updates for all major operations
- Robust connection management

### Phase 5: Agent Integration with Streaming (Week 5)

**Goal:** LSP server ready for agent backend integration with real-time streaming

**Tasks:**
1. Add agent integration commands with SSE streaming:
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

### SSE Event Types

```python
class SSEEventType(str, Enum):
    # Component operations
    COMPONENT_CREATED = "component.created"
    COMPONENT_UPDATED = "component.updated"
    COMPONENT_DELETED = "component.deleted"
    
    # Compilation events
    COMPILATION_STARTED = "compilation.started"
    COMPILATION_PROGRESS = "compilation.progress"
    COMPILATION_COMPLETED = "compilation.completed"
    COMPILATION_FAILED = "compilation.failed"
    
    # Diagnostic events
    DIAGNOSTICS_STARTED = "diagnostics.started"
    DIAGNOSTICS_PROGRESS = "diagnostics.progress"
    DIAGNOSTICS_COMPLETED = "diagnostics.completed"
    
    # Agent interaction events
    AGENT_THINKING = "agent.thinking"
    AGENT_RESPONSE_CHUNK = "agent.response.chunk"
    AGENT_RESPONSE_COMPLETED = "agent.response.completed"
    AGENT_ERROR = "agent.error"
    
    # Decomposition events
    DECOMPOSITION_STARTED = "decomposition.started"
    DECOMPOSITION_PROPOSAL = "decomposition.proposal"
    DECOMPOSITION_FEEDBACK_REQUEST = "decomposition.feedback_request"
    DECOMPOSITION_COMPLETED = "decomposition.completed"
    
    # Session events
    SESSION_STARTED = "session.started"
    SESSION_ENDED = "session.ended"
    CONNECTION_STATUS = "connection.status"
```

### SSE Architecture

```
┌─────────────────┐    SSE     ┌─────────────────┐    HTTP    ┌─────────────────┐
│   VSCode Ext    │◄──────────►│   LSP Server    │◄──────────►│  Agent Backend  │
│                 │            │                 │            │                 │
│ - Event Handler │            │ - SSE Manager   │            │ - LLM Streaming │
│ - UI Updates    │            │ - Event Router  │            │ - Progress API  │
│ - Progress Bars │            │ - Client Mgmt   │            │ - Session Mgmt  │
└─────────────────┘            └─────────────────┘            └─────────────────┘
```

### Dependencies

```toml
# Add to pyproject.toml
pygls = "^1.0.0"
watchdog = "^3.0.0"  # For file watching
fastapi = "^0.104.0"  # For SSE endpoint hosting
uvicorn = "^0.24.0"   # ASGI server for SSE
httpx = "^0.25.0"     # HTTP client for agent backend
```

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
- SSE connection preferences

## Testing Strategy

### Unit Tests
- Component index operations
- Diagnostic generation logic
- Hover information formatting
- Code action generation
- SSE event routing and delivery
- Connection lifecycle management

### Integration Tests
- Full LSP server lifecycle
- File watching and change detection
- Component compilation integration
- Error handling scenarios
- SSE connection handling
- Agent backend streaming integration

### Manual Testing
- VSCode extension integration
- Performance with large component graphs
- Real-world component development workflows
- SSE connection stability under load
- LLM streaming responsiveness

## Performance Considerations

### Indexing Performance
- Lazy loading of component files
- Incremental updates for file changes
- Caching of parsed component metadata
- Background reindexing for large changes

### Memory Usage
- Limit in-memory component cache size
- Periodic cleanup of unused entries
- Efficient storage of diagnostic information
- SSE message queue management

### Response Times
- Target <100ms for hover requests
- Target <500ms for code actions
- Background processing for expensive operations
- Progress reporting for long-running commands

### SSE Performance
- Message batching for high-frequency updates
- Connection pooling and reuse
- Efficient event serialization
- Client-side buffering and flow control

## Success Criteria

1. **Functional:**
   - LSP server starts and connects to VSCode
   - Provides accurate diagnostics for component issues
   - Hover shows useful component information
   - Code actions work for common operations
   - SSE connections establish and maintain reliably
   - Real-time updates stream without delays

2. **Performance:**
   - Startup time <2 seconds for typical projects
   - Hover response time <100ms
   - File change processing <500ms
   - Memory usage <100MB for 1000 components
   - SSE message delivery <50ms latency
   - LLM streaming with <200ms first token

3. **Reliability:**
   - No crashes during normal operation
   - Graceful handling of malformed components
   - Recovery from temporary file system issues
   - Clear error messages for user issues
   - Automatic SSE reconnection on network issues
   - Robust handling of agent backend failures

4. **Integration:**
   - Seamless VSCode extension integration
   - Compatible with existing component workflow
   - Ready for agent backend integration
   - Extensible for future features
   - Real-time collaboration capabilities
   - Streaming LLM responses in VSCode

This plan provides a solid foundation for the LSP server with comprehensive SSE integration, enabling real-time progress updates, streaming LLM responses, and incremental updates throughout the component development workflow.
