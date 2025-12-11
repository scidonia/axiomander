# Axiomander

**Formal Verification for Python using Z3 SMT Solver with Live LSP Integration**

Axiomander is a Python library that enables formal verification of Python code through Z3 SMT solver integration. It implements Dijkstra-style weakest precondition calculus to verify assertions by moving them backward through pure code blocks.

## 🚀 Features

- **Static Analysis**: Parse and analyze Python code for verification targets
- **Purity Analysis**: Conservative classification of code as pure (no side effects) vs impure
- **Assertion Discovery**: Find and categorize assertions as preconditions, postconditions, loop invariants, or termination measures
- **Weakest Precondition Calculus**: Move assertions backward through pure code using Dijkstra's method
- **Z3 SMT Integration**: Translate Python expressions to Z3 formulas for automated theorem proving
- **Live LSP Integration**: Real-time verification feedback in editors
- **Conservative Approach**: Unknown constructs default to impure for safety

## 🏗️ Architecture

```
src/axiomander/
├── ast/                        # AST analysis and manipulation
│   ├── parser.py              # Python AST parsing with source mapping
│   ├── purity_analyzer.py     # Pure vs impure function analysis
│   └── assertion_finder.py    # Assert statement discovery and classification
├── logic/                      # Logical reasoning and SMT integration
│   ├── smt_translator.py      # Python → Z3 formula translation
│   └── weakest_precondition.py # Backward assertion movement (WP calculus)
├── verification/              # Verification engine core
│   └── verifier.py           # Main verification orchestrator
├── lsp/                       # Language Server Protocol integration
│   └── server.py             # LSP server for live editor feedback
└── cli/                       # Command-line interface
    └── commands.py           # CLI commands
```

## 📦 Installation

```bash
# Install from source
git clone https://github.com/Scidonia/axiomander
cd axiomander
pip install -e .

# For development
pip install -e .[dev]
```

## 🚦 Current Status

**Phase 1 (Completed)**: Foundation and Architecture
- ✅ Project structure and dependencies
- ✅ AST parsing with source location tracking
- ✅ Purity analysis framework 
- ✅ Assertion discovery system
- ✅ Z3 translator stub (implementation pending full dependency resolution)
- ✅ Weakest precondition calculator framework
- ✅ Basic LSP server structure
- ✅ CLI interface

**Phase 2 (In Progress)**: Core Implementation
- 🔄 Full Z3 integration and SMT translation
- 🔄 Complete WP calculus implementation
- 🔄 Loop invariant processing
- 🔄 Recursive function verification with termination measures

**Phase 3 (Planned)**: Advanced Features
- ⏳ Real-time LSP diagnostics
- ⏳ Editor integration
- ⏳ Performance optimization and caching
- ⏳ Advanced recursive function handling

## 🎯 Usage

### Command Line Interface

```bash
# Verify assertions in a Python file
axiomander verify my_code.py

# Start LSP server for editor integration
axiomander lsp

# Show help
axiomander help
```

### Python API

```python
import axiomander

# Verify a file programmatically
axiomander.verify_file("my_code.py")

# Start LSP server
axiomander.start_lsp_server()
```

## 📝 Writing Verifiable Code

Axiomander works with standard Python `assert` statements:

### Preconditions and Postconditions

```python
def factorial(n: int) -> int:
    # Precondition
    assert n >= 0, "Factorial requires non-negative input"
    
    if n <= 1:
        result = 1
    else:
        result = n * factorial(n - 1)
    
    # Postcondition
    assert result >= 1, "Factorial is always positive"
    return result
```

### Loop Invariants

```python
def sum_array(arr: list) -> int:
    assert len(arr) >= 0  # Precondition
    
    total = 0
    i = 0
    
    while i < len(arr):
        # Loop invariant
        assert total >= 0, "Running sum is non-negative"
        assert 0 <= i < len(arr), "Index is within bounds"
        
        total += arr[i]
        i += 1
    
    assert total >= 0  # Postcondition
    return total
```

### Termination Measures (Recursive Functions)

```python
def gcd(a: int, b: int) -> int:
    assert a > 0 and b > 0  # Precondition
    
    if b == 0:
        return a
    
    # Termination measure: b decreases
    assert 0 < b < a  # or use mathematical ordering
    return gcd(b, a % b)
```

## 🔍 Verification Status Indicators

Axiomander provides real-time feedback on assertion status:

- 🟢 **Verified**: Weakest precondition fully computed and proven
- 🟡 **Checked**: Analysis complete but unverified  
- ⚫ **Checking**: SMT solver still running
- 🔴 **Counter-example**: Proof of incorrectness found with line numbers

## 🧠 How It Works

1. **Parse**: Extract Python AST with source location mapping
2. **Discover**: Find assert statements and classify them by type
3. **Analyze**: Determine purity of code constructs 
4. **Propagate**: Move assertions backward through pure code blocks
5. **Translate**: Convert Python expressions to Z3 SMT formulas
6. **Verify**: Use Z3 to check satisfiability and find counter-examples
7. **Report**: Provide live feedback via LSP or CLI

## 🔒 Conservative Approach

Axiomander prioritizes **safety over completeness**:

- Unknown constructs are considered impure by default
- Function calls block assertion movement unless marked pure
- Complex control flow requires explicit invariants
- Recursive functions need termination measures

## 🤝 Recursive Function Recommendations

### Structural Recursion
```python
def tree_height(node):
    assert node is not None  # Precondition
    
    if node.is_leaf():
        return 1
    
    # Termination: recursive calls on structurally smaller inputs
    left_height = tree_height(node.left) if node.left else 0
    right_height = tree_height(node.right) if node.right else 0
    
    result = 1 + max(left_height, right_height)
    assert result >= 1  # Postcondition
    return result
```

## 📚 Examples

See `src/example/factorial_example.py` for comprehensive examples demonstrating:

- Mathematical functions with verification
- Preconditions and postconditions
- Loop invariants
- Termination measures
- Safe division with error handling
- Array operations with bounds checking

## 🛠️ Development

```bash
# Install development dependencies
pip install -e .[dev]

# Run tests (when implemented)
pytest

# Type checking
mypy src/

# Code formatting
black src/
ruff check src/
```

## 🎓 Theoretical Background

Axiomander is based on:

- **Dijkstra's Weakest Precondition Calculus**: Systematic backward propagation of assertions
- **Hoare Logic**: Formal reasoning about program correctness
- **SMT Solving**: Automated theorem proving with Z3
- **Static Analysis**: Conservative approximation of program behavior

## 🔮 Future Directions

- **Enhanced Array Reasoning**: Better support for list/array operations
- **Object-Oriented Support**: Verification of classes and methods
- **Concurrency**: Thread-safe verification patterns
- **Integration**: Support for more SMT solvers beyond Z3
- **Performance**: Incremental verification and smart caching

## 📄 License

MIT License - see LICENSE file for details.

## 🙏 Acknowledgments

Built with:
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3) for SMT solving
- [pygls](https://github.com/openlawlibrary/pygls) for LSP integration
- Python's `ast` module for code analysis

---

**Note**: Axiomander is currently in early development. The core architecture is complete, but full Z3 integration and LSP features are pending dependency resolution and continued development.