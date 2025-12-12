# Axiomander Emacs Setup Instructions

The Axiomander Emacs configuration has been reorganized and is now ready for use!

## File Organization

✅ **Main configuration moved to:** `editors/emacs/axiomander.el`  
✅ **Hover improvements built into main config**  
✅ **Setup loader in source control:** `editors/emacs/axiomander-setup.el`  
✅ **Symlinked to:** `~/.emacs.d/setup/axiomander.el`  
✅ **Documentation updated:** `editors/emacs/README.md`

## Quick Start

### 1. Create Symlink (if not already done)

```bash
ln -sf ~/dev/Scidonia/axiomander/editors/emacs/axiomander-setup.el ~/.emacs.d/lisp/axiomander-setup.el
```

### 2. Add to Your Init File

Add this to your `~/.emacs.d/init.el`:

```elisp
;; Add lisp directory to load-path  
(add-to-list 'load-path "~/.emacs.d/lisp")

;; axiomander
(require 'axiomander-setup)
(axiomander-global-mode 1)
```

### 3. Install Dependencies

Make sure you have the required packages:

```elisp
M-x package-install RET lsp-mode RET
M-x package-install RET lsp-ui RET
```

Or use the built-in installer: `C-c a I`

### 4. Open a Python File

Open any Python file (e.g., `examples/wrong_contracts.py`) and the Axiomander LSP should automatically start.

### 5. Test the Setup

Use these commands to verify everything is working:

- **Check setup status:** `C-c a ?`
- **Configure hover:** `C-c a H`  
- **Run diagnostics:** `C-c a D` (once LSP is loaded)

## Key Features Now Available

### ✅ Fixed Hover Display
- Hover now appears **above** functions (not to the right)
- **Wider display** (100+ characters) for full verification results
- **Taller display** (30+ lines) for multiple assertions
- **Faster response** (0.1s delay)

### ✅ Complete Key Bindings
- `C-c a v` - Verify contracts
- `C-c a h` - Show hover info
- `C-c a S` - Server status
- `C-c a ?` - Setup status
- `C-c a L` - Reload config
- `C-c a O` - Open config file

### ✅ Automatic Setup
- Runs alongside Pyright LSP
- Auto-configures for Python files
- Handles server startup/restart
- Provides comprehensive diagnostics

## Testing the Hover Fix

1. **Open wrong_contracts.py:**
   ```
   C-c a P  (open project)
   ```
   Navigate to `examples/wrong_contracts.py`

2. **Start LSP if needed:**
   ```
   M-x lsp
   ```

3. **Test hover on function:**
   - Place cursor on any function name (e.g., `wrong_precondition_too_restrictive`)
   - Press `C-c a h` or hover with mouse
   - Verify hover appears above the function with proper width

4. **Manual popup as backup:**
   ```
   C-c a p  (manual verification popup)
   ```

## Troubleshooting

### If LSP doesn't start:

1. **Check dependencies:**
   ```
   M-x package-list-packages
   ```
   Install `lsp-mode` and `lsp-ui`

2. **Check setup status:**
   ```
   C-c a ?
   ```

3. **Reload configuration:**
   ```
   C-c a L
   ```

### If hover still has issues:

1. **Manual configuration:**
   ```
   C-c a H
   ```

2. **Try different display methods:**
   ```
   C-c a p  (manual popup)
   C-c l h  (LSP describe)
   ```

3. **Check LSP UI settings:**
   ```elisp
   M-x customize-group RET lsp-ui-doc RET
   ```

## File Locations Summary

| File | Location | Purpose |
|------|----------|---------|
| Main config | `editors/emacs/axiomander.el` | Complete LSP integration with built-in hover fixes |
| Setup loader | `editors/emacs/axiomander-setup.el` | Setup file (in source control) |
| Symlink | `~/.emacs.d/lisp/axiomander-setup.el` → `axiomander-setup.el` | Easy loading from init.el |
| Documentation | `editors/emacs/README.md` | Comprehensive usage guide |

## Why Symlinks?

✅ **Source control** - Setup file is versioned with the project  
✅ **Distribution** - Users get updates when they pull the repo  
✅ **Consistency** - Same setup file works for all users  
✅ **Maintenance** - Single file to update, automatically propagated

## Next Steps

1. **Add to your init.el** the load-file line above
2. **Restart Emacs** or reload your init file
3. **Open a Python file** with contracts
4. **Test verification** with `C-c a v`
5. **Test hover display** on function names

The hover should now display verification results properly positioned and sized for easy reading!

## Quick Reference Card

```
Setup Commands:
C-c a ? - Setup status        C-c a L - Reload config
C-c a O - Open config         C-c a P - Open project

Contract Commands:  
C-c a v - Verify              C-c a t - Generate tests
C-c a s - Show SMT            C-c a h - Hover info

Server Commands:
C-c a S - Server status       C-c a R - Restart server  
C-c a D - Diagnostics         C-c a H - Configure hover
```

🎉 **Ready to use!** The configuration is now properly organized and the hover display issues are fixed.