# Axiomander Emacs Integration

This directory contains Emacs configurations for Axiomander LSP integration with formal verification support.

## Files

- **`axiomander.el`** - Complete LSP configuration with hover improvements built-in
- **`axiomander-setup.el`** - Setup loader (symlink this to `~/.emacs.d/setup/axiomander.el`)
- **`axiomander-mode.el`** - Basic mode definition (legacy)
- **`axiomander-pkg.el`** - Package metadata

## Quick Setup

### Recommended: Automatic Setup

1. **Create the symlink:**
   ```bash
   ln -sf ~/dev/Scidonia/axiomander/editors/emacs/axiomander-setup.el ~/.emacs.d/setup/axiomander.el
   ```

2. **Load in your init.el:**
   ```elisp
   ;; In your ~/.emacs.d/init.el
   (load-file "~/.emacs.d/setup/axiomander.el")
   ```

This automatically:
- Loads the main configuration with built-in hover improvements
- Enables global mode for all Python files  
- Provides status, reload, and management commands
- Maintains connection to source control for updates

### Manual Setup

If you prefer manual control:

```elisp
(add-to-list 'load-path "~/dev/Scidonia/axiomander/editors/emacs")
(require 'axiomander)
(axiomander-global-mode 1)
```



## Dependencies

### Required
- **`lsp-mode`** (version 9.0+) - Core LSP functionality

### Recommended  
- **`lsp-ui`** - Enhanced hover display and diagnostics
- **`python-mode`** - Better Python support

### Optional
- **`pos-tip`** - Alternative hover display method

Install via package manager:
```elisp
(package-install 'lsp-mode)
(package-install 'lsp-ui)
```

## Features

### Modern LSP Integration (`axiomander.el`)

- **Multi-server support** - Runs alongside Pyright for complete Python + verification
- **Smart hover display** - Properly positioned and sized verification results
- **Contract-specific commands** - Verification, testing, SMT generation
- **Automatic configuration** - Sets up when Python files are opened
- **Comprehensive diagnostics** - Built-in troubleshooting tools
- **Status monitoring** - Server health and connection status

### Key Bindings

#### Contract Operations
| Key | Command | Description |
|-----|---------|-------------|
| `C-c a v` | `axiomander-verify-contracts` | Verify contracts in current file |
| `C-c a t` | `axiomander-generate-tests` | Generate tests for contracts |
| `C-c a s` | `axiomander-show-smt` | Show SMT-LIB representation |
| `C-c a e` | `axiomander-explain-assertion` | Explain assertion at point |
| `C-c a c` | `axiomander-generate-counterexample` | Generate counterexample |

#### Navigation & Info
| Key | Command | Description |
|-----|---------|-------------|
| `C-c a h` | `lsp-describe-thing-at-point` | Show hover information |
| `C-c a i` | `lsp-ui-doc-show` | Show documentation popup |
| `C-c a r` | `lsp-find-references` | Find references |
| `C-c a j` | `lsp-find-definition` | Jump to definition |

#### Utilities
| Key | Command | Description |
|-----|---------|-------------|
| `C-c a S` | `axiomander-server-status` | Show server status |
| `C-c a R` | `axiomander-restart-server` | Restart LSP server |
| `C-c a D` | `axiomander-doctor` | Run diagnostics |
| `C-c a H` | `axiomander-configure-hover` | Configure hover display |
| `C-c a ?` | `axiomander-help` | Show help |

#### Setup Commands (from `~/.emacs.d/setup/axiomander.el`)
| Key | Command | Description |
|-----|---------|-------------|
| `C-c a L` | `reload-axiomander-config` | Reload configuration |
| `C-c a O` | `open-axiomander-config` | Open config file |
| `C-c a P` | `open-axiomander-project` | Open project directory |
| `C-c a ?` | `axiomander-setup-status` | Show setup status |

## Hover Display Improvements

The hover configuration fixes common issues with verification result display:

### Problems Solved
- **Positioning**: Hover now appears above the function, not far to the right
- **Width**: Expanded to 100+ characters for full verification results  
- **Height**: Increased to 30+ lines for multiple assertions
- **Speed**: Quick 0.1s display delay

### Configuration
```elisp
;; Customize hover display (before loading)
(setq axiomander-hover-max-width 120)     ; Characters wide
(setq axiomander-hover-max-height 40)     ; Lines tall  
(setq axiomander-hover-position 'top)     ; Position: top/bottom/at-point
(setq axiomander-hover-at-point t)        ; Follow cursor
```

### Manual Alternatives
If hover still has issues:
- **Manual popup**: `C-c a p`
- **Help buffer**: `C-c l h` 
- **Status check**: `C-c a ?`

## Configuration

### Main Settings

```elisp
;; Core configuration
(setq axiomander-server-command "axiomander-lsp")
(setq axiomander-python-executable "python3")
(setq axiomander-enable-contracts t)
(setq axiomander-strict-mode nil)

;; UI settings
(setq axiomander-keybinding-prefix "C-c a")
(setq axiomander-show-server-messages t)

;; Hover configuration
(setq axiomander-hover-max-width 120)
(setq axiomander-hover-position 'top)
```

### Complete Example

```elisp
;; Load from setup directory (recommended)
(load-file "~/.emacs.d/setup/axiomander.el")

;; Or manual configuration
(add-to-list 'load-path "~/dev/Scidonia/axiomander/editors/emacs")
(require 'axiomander)

;; Customize if needed
(setq axiomander-strict-mode t
      axiomander-hover-max-width 100
      axiomander-keybinding-prefix "C-c x")

;; Enable globally
(axiomander-global-mode 1)
```

## Troubleshooting

### Quick Diagnostics

```
M-x axiomander-setup-status    # Check setup
M-x axiomander-doctor          # Comprehensive diagnostics
```

### Common Issues

#### LSP Server Not Starting

1. **Check Axiomander installation:**
   ```bash
   python3 -m axiomander.lsp --help
   ```

2. **Verify setup status:**
   ```
   C-c a ?  (axiomander-setup-status)
   ```

3. **Try reloading:**
   ```  
   C-c a L  (reload-axiomander-config)
   ```

#### Hover Display Issues

1. **Configure hover manually:**
   ```
   C-c a H  (axiomander-configure-hover)
   ```

2. **Try manual popup:**
   ```
   C-c a p  (axiomander-show-verification-popup)
   ```

3. **Check LSP UI:**
   ```elisp
   M-x package-install RET lsp-ui RET
   ```

#### Server Connection Problems

1. **Check server status:**
   ```
   C-c a S  (axiomander-server-status)
   ```

2. **Restart server:**
   ```
   C-c a R  (axiomander-restart-server)
   ```

3. **Check Python environment:**
   ```bash
   python3 -c "import axiomander; print('OK')"
   ```

### Debug Information

Enable debug output:
```elisp
(setq lsp-log-io t)
(setq axiomander-log-level "debug")
```

Check logs:
```
M-x lsp-workspace-show-log
```

## Project Structure

Expected file organization:
```
~/dev/Scidonia/axiomander/
├── editors/emacs/              # This directory
│   ├── axiomander.el          # Main configuration  
│   ├── axiomander-hover-fix.el # Hover improvements
│   ├── axiomander-mode.el     # Basic mode (legacy)
│   └── README.md              # This file
├── src/axiomander/
│   └── lsp/                   # LSP server implementation
└── ~/.emacs.d/setup/
    └── axiomander.el          # Setup loader
```

## Alternative Configurations

- **Modern LSP**: `axiomander.el` (recommended)
- **Hover fix only**: `axiomander-hover-fix.el` 
- **Basic mode**: `axiomander-mode.el` (legacy)
- **Package metadata**: `axiomander-pkg.el`

## Contributing

1. Edit configuration files in this directory
2. Test changes:
   ```elisp
   C-c a L  ; Reload config
   ```
3. Submit pull requests to the main project

## License

Part of the Axiomander project. See main project license.