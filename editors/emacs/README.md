# Axiomander Emacs Mode

A specialized Emacs major mode for editing Axiomander Python code with enhanced support for formal verification constructs, LSP integration, and development tooling.

## Features

- **Enhanced Python Support**: Built on top of `python-mode` with Axiomander-specific extensions
- **Syntax Highlighting**: Special highlighting for formal verification keywords (`requires`, `ensures`, `invariant`, etc.)
- **LSP Integration**: Seamless integration with Language Server Protocol for intelligent code completion and analysis  
- **Contract Support**: Special handling for `@contract`, `@pure`, `@axiom` decorators
- **Verification Commands**: Built-in commands for running verification, tests, and Z3 checks
- **Imenu Integration**: Easy navigation to contract functions and pure functions
- **Project Detection**: Automatic mode activation for Axiomander projects

## Installation

### Method 1: Manual Installation

1. Copy the `axiomander-mode.el` file to your Emacs load path
2. Add the following to your Emacs configuration:

```elisp
(require 'axiomander-mode)
```

### Method 2: Using use-package

```elisp
(use-package axiomander-mode
  :load-path "/path/to/axiomander/editors/emacs/"
  :mode (("\\.ax\\.py\\'" . axiomander-mode)
         ("/axiomander/.*\\.py\\'" . axiomander-mode))
  :config
  (setq axiomander-python-executable "python3"))
```

### Method 3: Local Development

For development on the Axiomander project itself:

```elisp
(add-to-list 'load-path "/home/gavin/dev/Scidonia/axiomander/editors/emacs/")
(require 'axiomander-mode)
```

## Prerequisites

### Required Packages

The mode depends on these Emacs packages:
- `python-mode` (or built-in `python.el`)
- `lsp-mode` (version 8.0.0+) - for LSP integration
- `flycheck` (optional) - for syntax checking

Install via package manager:

```elisp
(package-install 'lsp-mode)
(package-install 'flycheck)
```

### Python Environment Setup

1. Ensure your Python environment has the Axiomander package installed
2. Install Python LSP server:
   ```bash
   pip install python-lsp-server[all]
   ```

## Usage

### Automatic Mode Detection

The mode automatically activates for:
- Files with `.ax.py` extension
- Python files in `/axiomander/` directories
- Files in projects with `pyproject.toml` containing axiomander dependencies

### Manual Activation

```elisp
M-x axiomander-mode
```

### Key Bindings

| Key Binding | Command | Description |
|-------------|---------|-------------|
| `C-c C-v` | `axiomander-verify-file` | Verify current file |
| `C-c C-t` | `axiomander-run-tests` | Run project tests |
| `C-c C-z` | `axiomander-z3-check` | Check file with Z3 |
| `C-c C-s` | `axiomander-show-smt` | Show SMT-LIB output |

### LSP Features

When LSP is active, you get:
- Code completion for Axiomander constructs
- Hover documentation
- Go to definition
- Find references
- Diagnostic errors and warnings

## Syntax Highlighting

The mode provides enhanced highlighting for:

### Contract Keywords
- `requires`, `ensures`, `invariant`
- `assert`, `assume`, `havoc`

### Logical Operators
- `forall`, `exists`, `implies`, `iff`

### Decorators
- `@contract`, `@pure`, `@axiom`, `@lemma`, `@theorem`

### Mathematical Operators
- `==`, `!=`, `<=`, `>=`, `&&`, `||`, `!`

## Configuration

### Customization Variables

```elisp
;; Python executable for Axiomander
(setq axiomander-python-executable "python3")

;; Custom LSP server command
(setq axiomander-lsp-server-command '("pylsp"))

;; Disable contract highlighting
(setq axiomander-enable-contract-highlighting nil)
```

### Complete Configuration Example

```elisp
(use-package axiomander-mode
  :load-path "/path/to/axiomander/editors/emacs/"
  :mode (("\\.ax\\.py\\'" . axiomander-mode)
         ("/axiomander/.*\\.py\\'" . axiomander-mode))
  :config
  ;; Python configuration
  (setq axiomander-python-executable "python3")
  
  ;; Enable LSP
  (add-hook 'axiomander-mode-hook #'lsp)
  
  ;; Enable flycheck
  (add-hook 'axiomander-mode-hook #'flycheck-mode)
  
  ;; Custom keybindings
  (define-key axiomander-mode-map (kbd "C-c C-d") 'lsp-describe-thing-at-point))
```

## Imenu Integration

The mode provides special imenu support for:
- Contract functions (`@contract` decorated)
- Pure functions (`@pure` decorated)

Access via `M-x imenu` or your preferred imenu interface.

## Troubleshooting

### LSP Not Starting

1. Check Python LSP server installation:
   ```bash
   python3 -m pylsp --help
   ```

2. Verify LSP mode is loaded:
   ```elisp
   M-x lsp-describe-session
   ```

3. Check Python executable path:
   ```elisp
   M-x customize-variable RET axiomander-python-executable
   ```

### Syntax Highlighting Issues

1. Ensure font-lock is enabled:
   ```elisp
   M-x font-lock-mode
   ```

2. Reload the mode:
   ```elisp
   M-x revert-buffer
   ```

### Command Not Found Errors

Ensure the Axiomander Python package is installed and accessible:
```bash
python3 -c "import axiomander; print('OK')"
```

## Development

### Contributing

1. Edit `axiomander-mode.el`
2. Test changes:
   ```elisp
   M-x eval-buffer
   M-x axiomander-mode
   ```
3. Submit improvements via pull request

### Adding New Features

The mode is designed to be extensible. Common extension points:
- Add new font-lock keywords to `axiomander-font-lock-keywords`
- Define new commands and bind them in `axiomander-mode-map`
- Extend imenu support in `axiomander-imenu-create-index`

## License

This mode is part of the Axiomander project. See the main project LICENSE file for details.