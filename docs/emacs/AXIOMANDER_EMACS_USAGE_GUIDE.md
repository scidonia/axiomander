# Axiomander Emacs LSP Integration - Usage Guide

## Overview

This guide covers the **modernized** Axiomander LSP integration for Emacs, featuring comprehensive support for contract-oriented programming with Python. The integration uses modern lsp-mode APIs and provides advanced features including semantic tokens, custom capabilities, and multi-server coordination with Pyright.

## ✨ Key Features

### 🔧 **Modern LSP Integration**
- **lsp-mode 9.0+ compatibility** with current API standards
- **Multi-server support** - runs alongside Pyright seamlessly  
- **Advanced error handling** with server availability testing
- **Automatic server restart** on crashes
- **Custom LSP capabilities** for Axiomander-specific features

### 📝 **Contract Development Tools**
- **Contract verification** - verify assertions and invariants
- **Test generation** - automatic test case creation from contracts
- **SMT visualization** - view Z3 SMT-LIB representations
- **Counterexample generation** - debug failed assertions
- **Assertion explanation** - understand contract failures

### 🎨 **Enhanced UI**
- **Semantic token highlighting** for contract constructs
- **Custom keybindings** (`C-c a` prefix by default)
- **Visual indicators** when Axiomander LSP is active
- **Comprehensive diagnostics** and troubleshooting tools

### ⚙️ **Advanced Configuration**
- **Comprehensive settings** via Emacs customize system
- **Project-aware configuration** with `.dir-locals.el`
- **Runtime server management** (start, stop, restart)
- **Extensive customization options**

---

## 🚀 Quick Start

### 1. Prerequisites

**Required Packages:**
```elisp
;; Install via package manager (MELPA)
(package-install 'lsp-mode)      ; version 9.0.0+
(package-install 'lsp-pyright)   ; version 1.1.0+
(package-install 'lsp-ui)        ; optional but recommended
```

**System Requirements:**
- **Emacs 28.1+**
- **Python 3.8+** 
- **Axiomander LSP Server** (`axiomander-lsp` command available)
- **Pyright** (`npm install -g pyright` or `pip install basedpyright`)

### 2. Basic Setup

**Simple Configuration** (add to your `~/.emacs.d/init.el`):
```elisp
;; Add Axiomander to your load path (adjust path as needed)
(add-to-list 'load-path "/home/gavin/dev/Personal/code/elisp/setup/")

;; Load and enable Axiomander global mode
(require 'axiomander)
(axiomander-global-mode 1)
```

**Advanced Configuration** (using `use-package`):
```elisp
(use-package axiomander
  :load-path "/path/to/axiomander/setup/"
  :config
  ;; Customize server settings
  (setq axiomander-server-command "axiomander-lsp"
        axiomander-enable-contracts t
        axiomander-strict-mode nil
        axiomander-log-level "info"
        axiomander-keybinding-prefix "C-c a")
  
  ;; Enable global mode
  (axiomander-global-mode 1)
  
  ;; Optional: customize semantic token faces
  (setq axiomander-semantic-token-faces
        '(("contract" . font-lock-keyword-face)
          ("assertion" . font-lock-builtin-face))))
```

### 3. Verification

**Test your setup:**
1. Open a Python file
2. Look for " Axio" in the mode line (indicates Axiomander LSP is active)  
3. Run `M-x axiomander-doctor` for comprehensive diagnostics
4. Try `C-c a ?` for help and available commands

---

## 📋 Command Reference

### Contract Operations

| Key | Command | Description |
|-----|---------|-------------|
| `C-c a v` | `axiomander-verify-contracts` | Verify contracts in current file |
| `C-c a t` | `axiomander-generate-tests` | Generate tests for contracts |
| `C-c a s` | `axiomander-show-smt` | Show SMT-LIB representation |
| `C-c a e` | `axiomander-explain-assertion` | Explain assertion at point |
| `C-c a c` | `axiomander-generate-counterexample` | Generate counterexample for failed assertion |
| `C-c a a` | `lsp-execute-code-action` | Apply contract suggestions |

### Navigation & Information

| Key | Command | Description |
|-----|---------|-------------|
| `C-c a h` | `lsp-describe-thing-at-point` | Show hover information |
| `C-c a i` | `lsp-ui-doc-show` | Show documentation popup |
| `C-c a r` | `lsp-find-references` | Find references to symbol |
| `C-c a j` | `lsp-find-definition` | Jump to definition |
| `C-c a d` | `lsp-ui-flycheck-list` | Show diagnostics list |

### Utilities

| Key | Command | Description |
|-----|---------|-------------|
| `C-c a S` | `axiomander-server-status` | Show server status |
| `C-c a R` | `axiomander-restart-server` | Restart Axiomander LSP server |
| `C-c a D` | `axiomander-doctor` | Run comprehensive diagnostics |
| `C-c a ?` | `axiomander-help` | Show help and command list |

---

## ⚙️ Configuration Options

### Server Configuration

```elisp
;; Server command (string, list, or function)
(setq axiomander-server-command "axiomander-lsp")
;; Alternative: (setq axiomander-server-command '("python" "-m" "axiomander.lsp"))
;; Function: (setq axiomander-server-command #'my-axiomander-command-function)

;; Additional server arguments
(setq axiomander-server-args '("--verbose" "--config" "/path/to/config.json"))

;; Python executable for fallback
(setq axiomander-python-executable "python3.11")
```

### Feature Configuration

```elisp
;; Contract verification settings
(setq axiomander-enable-contracts t           ; Enable contract analysis
      axiomander-strict-mode nil             ; Strict contract enforcement
      axiomander-verification-timeout 30     ; Timeout in seconds
      axiomander-log-level "info")           ; Server log level

;; UI and behavior settings
(setq axiomander-keybinding-prefix "C-c a"   ; Key prefix (customizable)
      axiomander-mode-lighter " Axio"        ; Mode line indicator
      axiomander-show-server-messages t      ; Show startup messages
      axiomander-auto-restart-server t)      ; Auto-restart on crash
```

### Advanced Configuration

```elisp
;; Semantic token support
(setq axiomander-enable-semantic-tokens t
      axiomander-completion-in-comments nil)

;; Library directories for contract resolution
(setq axiomander-library-directories
      '("/usr/local/lib/axiomander" 
        "~/.local/lib/axiomander"))

;; Custom semantic token faces
(setq axiomander-semantic-token-faces
      '(("contract" . font-lock-keyword-face)
        ("assertion" . font-lock-builtin-face)
        ("invariant" . font-lock-constant-face)
        ("precondition" . font-lock-preprocessor-face)
        ("postcondition" . font-lock-preprocessor-face)))
```

---

## 🎯 Project Setup

### Global Configuration (Recommended)

The modernized integration enables Axiomander LSP globally for all Python files automatically. No per-project configuration needed!

### Project-Specific Configuration (Optional)

**For project-specific settings**, create `.dir-locals.el` in your project root:

```elisp
((python-mode
  ;; Ensure both servers are active
  (lsp-enabled-clients . (pyright axiomander-lsp))
  
  ;; Project-specific Axiomander settings
  (axiomander-strict-mode . t)
  (axiomander-verification-timeout . 60)
  (axiomander-library-directories . ("./lib" "./contracts"))
  
  ;; Auto-enable contracts mode
  (eval . (axiomander-contracts-mode 1))))
```

### Workspace Configuration

**For use-package users**, project-specific setup:

```elisp
(use-package axiomander
  :load-path "/path/to/axiomander/"
  :hook ((python-mode . (lambda ()
                          (when (locate-dominating-file default-directory ".axiomander")
                            (setq-local axiomander-strict-mode t)))))
  :config
  (axiomander-global-mode 1))
```

---

## 🛠️ Troubleshooting

### Common Issues

#### 1. **"Symbol's function definition is void: axiomander-global-mode"**

**Problem**: File not loaded properly or dependency issues.

**Solutions**:
```elisp
;; Method 1: Explicit require (recommended)
(require 'axiomander)
(axiomander-global-mode 1)

;; Method 2: Direct load (if require fails)
(load-file "/path/to/axiomander-example.el")
(axiomander-global-mode 1)

;; Method 3: Check load path
(add-to-list 'load-path "/path/to/axiomander/directory/")
(require 'axiomander)
```

#### 2. **"lsp-mode is required for Axiomander global mode"**

**Problem**: lsp-mode not installed or loaded.

**Solutions**:
```elisp
;; Install lsp-mode
(package-install 'lsp-mode)
(package-install 'lsp-pyright)

;; Ensure it's loaded before axiomander
(require 'lsp-mode)
(require 'axiomander)
(axiomander-global-mode 1)
```

#### 3. **Axiomander LSP Server Not Starting**

**Problem**: Server executable not found or not working.

**Diagnostic Steps**:
1. Run `M-x axiomander-doctor` for comprehensive diagnosis
2. Check server command: `M-x axiomander-server-status`
3. Verify installation: `axiomander-lsp --help` in terminal

**Solutions**:
```elisp
;; Try different server commands
(setq axiomander-server-command "axiomander-lsp")  ; Direct command
;; OR
(setq axiomander-server-command '("python" "-m" "axiomander.lsp"))  ; Python module

;; Check if server is in PATH
(executable-find "axiomander-lsp")  ; Should return path if available
```

#### 4. **Both Servers Not Running Together**

**Problem**: Only Pyright or only Axiomander LSP running.

**Solutions**:
```elisp
;; Ensure global configuration is set
(setq lsp-enabled-clients '(pyright axiomander-lsp))

;; Or use project-local configuration
;; In .dir-locals.el:
((python-mode
  (lsp-enabled-clients . (pyright axiomander-lsp))))
```

### Advanced Diagnostics

#### **Comprehensive System Check**
```elisp
M-x axiomander-doctor
```
This command provides detailed system diagnostics including:
- LSP mode version and status
- Server command availability
- Active workspaces and servers
- Configuration validation
- Error logs and recommendations

#### **Server Status Monitoring**
```elisp
M-x axiomander-server-status  ; Quick status check
M-x lsp-describe-session      ; Detailed LSP session info  
M-x lsp-log                   ; View LSP communication logs
```

#### **Manual Server Management**
```elisp
M-x axiomander-restart-server ; Restart just Axiomander LSP
M-x lsp-restart-workspace     ; Restart all LSP servers
M-x lsp                       ; Start LSP if not running
```

---

## 📊 Performance & Optimization

### Performance Tips

1. **Resource Monitoring**:
   - Use `axiomander-doctor` to check resource usage
   - Monitor server process with `M-x axiomander-server-status`
   - Check LSP logs for performance issues

2. **Configuration Optimization**:
   ```elisp
   ;; Reduce verification timeout for faster feedback
   (setq axiomander-verification-timeout 15)
   
   ;; Limit library directories to essentials
   (setq axiomander-library-directories '("./src" "./lib"))
   
   ;; Disable features you don't use
   (setq axiomander-completion-in-comments nil
         axiomander-enable-semantic-tokens nil)
   ```

3. **Multi-Server Coordination**:
   - The integration is optimized for multi-server usage
   - Pyright handles type checking, Axiomander handles contracts
   - No conflicts or resource competition

### Memory Usage

- **Baseline**: ~50MB for Axiomander LSP server
- **With Pyright**: ~150MB total for both servers
- **Large projects**: May use more memory for analysis

---

## 🔧 Customization Examples

### Example 1: Minimal Setup
```elisp
(require 'axiomander)
(axiomander-global-mode 1)
```

### Example 2: Development Setup
```elisp
(use-package axiomander
  :config
  (setq axiomander-enable-contracts t
        axiomander-strict-mode nil
        axiomander-show-server-messages t
        axiomander-keybinding-prefix "C-c c")  ; Different prefix
  (axiomander-global-mode 1))
```

### Example 3: Production Setup
```elisp
(use-package axiomander
  :config
  (setq axiomander-enable-contracts t
        axiomander-strict-mode t
        axiomander-verification-timeout 60
        axiomander-auto-restart-server t
        axiomander-show-server-messages nil)
  (axiomander-global-mode 1)
  
  ;; Add project-specific hook
  (add-hook 'python-mode-hook
            (lambda ()
              (when (locate-dominating-file default-directory "pyproject.toml")
                (setq-local axiomander-library-directories 
                           (list (expand-file-name "lib" (projectile-project-root))))))))
```

### Example 4: Research/Academic Setup
```elisp
(use-package axiomander
  :config
  (setq axiomander-enable-contracts t
        axiomander-strict-mode t
        axiomander-verification-timeout 120    ; Longer timeout for complex proofs
        axiomander-log-level "debug"          ; Detailed logging
        axiomander-enable-semantic-tokens t   ; Full syntax highlighting
        axiomander-completion-in-comments t)  ; Completion in contract comments
  (axiomander-global-mode 1)
  
  ;; Custom faces for academic presentation
  (setq axiomander-semantic-token-faces
        '(("contract" . (:foreground "blue" :weight bold))
          ("assertion" . (:foreground "red" :weight bold))
          ("invariant" . (:foreground "green" :weight bold)))))
```

---

## 🆘 Support & Resources

### Getting Help

1. **Built-in Help**: `C-c a ?` or `M-x axiomander-help`
2. **Diagnostics**: `M-x axiomander-doctor`
3. **LSP Logs**: `M-x lsp-log` for detailed LSP communication

### Customization

- **Customize Group**: `M-x customize-group RET axiomander RET`
- **All Settings**: Browse and modify all Axiomander settings through Emacs customize interface

### Version Information

- **Package Version**: 2.0.0 (Modern LSP Integration)
- **Minimum Requirements**: 
  - Emacs 28.1+
  - lsp-mode 9.0.0+
  - lsp-pyright 1.1.0+
- **Recommended**: Latest versions of all dependencies

---

## 📝 Summary

The modernized Axiomander Emacs integration provides:

✅ **Fixed API Compatibility** - Works with current lsp-mode versions  
✅ **Global Python Support** - Automatically active on all Python files  
✅ **Multi-Server Architecture** - Seamless Pyright coordination  
✅ **Advanced Error Handling** - Graceful fallbacks and recovery  
✅ **Comprehensive Features** - Contract verification, testing, debugging  
✅ **Extensive Customization** - Fully configurable via Emacs customize  
✅ **Production Ready** - Robust, tested, and performant  

**Quick Start**: Just `(require 'axiomander)` and `(axiomander-global-mode 1)` - everything else works automatically!