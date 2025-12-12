# Axiomander Emacs Setup

Quick setup instructions for Axiomander LSP integration with improved hover display.

## One-Time Setup

### 1. Create Symlink

```bash
# Create symlink to your emacs lisp directory
ln -sf ~/dev/Scidonia/axiomander/editors/emacs/axiomander-setup.el ~/.emacs.d/lisp/axiomander-setup.el
```

### 2. Add to Init File

Add to your `~/.emacs.d/init.el`:

```elisp
;; Add lisp directory to load-path
(add-to-list 'load-path "~/.emacs.d/lisp")

;; axiomander
(require 'axiomander-setup)
(axiomander-global-mode 1)
```

### 2. Add to Init File

**Option A: Using require (recommended):**
```elisp
;; Add setup directory to load-path and require
(add-to-list 'load-path "~/.emacs.d/setup")
(require 'axiomander)
```

**Option B: Using load-file:**
```elisp
;; Direct load
(load-file "~/.emacs.d/setup/axiomander.el")
```

### 3. Install Dependencies

Either manually:
```elisp
M-x package-install RET lsp-mode RET
M-x package-install RET lsp-ui RET
```

Or use the built-in installer after loading:
```
C-c a I
```

## What You Get

✅ **Complete LSP integration** - Full Axiomander server support  
✅ **Fixed hover display** - Positioned above function, proper sizing  
✅ **Contract commands** - Verify, test, show SMT, etc.  
✅ **Multi-server support** - Works alongside Pyright  
✅ **Auto-updates** - Pulls changes from source control  

## Key Commands

- `C-c a ?` - Show setup status
- `C-c a v` - Verify contracts  
- `C-c a h` - Show hover info
- `C-c a H` - Configure hover display
- `C-c a D` - Run diagnostics
- `C-c a L` - Reload configuration

## Troubleshooting

1. **Check status:** `C-c a ?`
2. **Install packages:** `C-c a I`  
3. **Reload config:** `C-c a L`
4. **Run diagnostics:** `C-c a D`

## For Developers

The setup file is in source control at `editors/emacs/axiomander-setup.el`. Updates to this file automatically affect all users who have symlinked it.

To update the main configuration, edit `editors/emacs/axiomander.el`. The hover improvements are built into this file, not separate.

---

🎉 **That's it!** Open a Python file with contracts and enjoy improved hover display with full LSP features.