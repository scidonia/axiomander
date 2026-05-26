# Axiomander Emacs LSP Integration Guide

This document describes how to use **Axiomander LSP** together with **Pyright** in Emacs for Python development.

The goal is:

- Pyright provides type-checking, diagnostics, and completions.
- Axiomander LSP provides contract‑oriented features (spec browsing, contract diagnostics, code actions, etc.).
- Both servers run over the same Python buffer via `lsp-mode` (Axiomander registered as an *add‑on* server).

> **Note:** Anywhere you see `axiomander-lsp` below, replace it with the actual command that starts your Axiomander language server (for example `python -m axiomander.lsp` or a venv-local script path).

---

## 1. Dependencies

### System

- Emacs 28+ (earlier may work but is not tested here).
- Python 3.11+ (whatever Axiomander is targeting).
- A working installation of:
  - `pyright` (or `basedpyright`) in your PATH:  
    ```bash
    npm install -g pyright
    # or
    pip install basedpyright
    ```
  - `axiomander-lsp` entrypoint somewhere on PATH (or an absolute path you will use in the Emacs config).

### Emacs packages

Install from MELPA (recommended):

- `lsp-mode`
- `lsp-ui` (optional but nice)
- `lsp-pyright`
- (Optionally) `which-key`, `project`, `flycheck` or `flymake`, etc.

Using `use-package`, your base dependencies might look like:

```elisp
(use-package lsp-mode
  :ensure t
  :init
  (setq lsp-keymap-prefix "C-c l")
  :hook ((python-mode . lsp-deferred))
  :commands (lsp lsp-deferred))

(use-package lsp-ui
  :ensure t
  :commands lsp-ui-mode)

(use-package lsp-pyright
  :ensure t
  :after lsp-mode
  :hook (python-mode . (lambda ()
                         (require 'lsp-pyright)))
  :custom
  ;; Use "pyright" or "basedpyright" depending on what you installed:
  (lsp-pyright-langserver-command "pyright"))
```

At this point, opening a Python file and running `M-x lsp` should start Pyright.

---

## 2. Registering Axiomander as an add‑on LSP server

`lsp-mode` lets you run multiple servers on the same buffer if one of them is marked as `:add-on? t`. We’ll keep Pyright as the primary Python server and register **Axiomander** as an add‑on.

Add the following to your Emacs config **after** `lsp-mode` is loaded:

```elisp
(with-eval-after-load 'lsp-mode
  ;; Ensure python-mode is associated with the "python" language id
  ;; (lsp-mode usually sets this automatically, but it doesn’t hurt to be explicit).
  (add-to-list 'lsp-language-id-configuration '(python-mode . "python"))

  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection
                     (lambda ()
                       ;; Replace this with the actual command to start Axiomander LSP
                       ;; Example: '("python" "-m" "axiomander.lsp")
                       '("axiomander-lsp")))
    :activation-fn (lsp-activate-on "python")
    :priority -1              ;; Lower priority than Pyright; Pyright is the "main" server
    :add-on? t                ;; <--- IMPORTANT: run alongside other Python servers
    :server-id 'axiomander-lsp)))
```

### Per-project enabling of both servers

By default, `lsp-mode` may choose a single client. To make sure **both** Pyright and Axiomander run in your project, you can configure `.dir-locals.el` at the repo root:

```elisp
((python-mode
  (lsp-enabled-clients . (pyright axiomander-lsp))))
```

Alternatively, you can set `lsp-enabled-clients` in your init for all Python buffers, but using `.dir-locals.el` per project is usually safer.

You can inspect what is running with:

- `M-x lsp-describe-session` – shows active workspaces and servers.
- `M-x lsp-log` – inspect server startup / errors.

---

## 3. Axiomander Emacs minor mode (for the agent to implement)

The Emacs integration should be a thin, opinionated layer over `lsp-mode`. The responsibilities:

1. Ensure both Pyright and Axiomander LSP are running for Python buffers.
2. Provide keybindings that map to Axiomander-specific functionality (via LSP requests).
3. Offer small UX features for contracts (jumping, viewing, applying code actions).

### 3.1. Skeleton minor mode

The agent should implement a minor mode roughly like this:

```elisp
(define-minor-mode axiomander-mode
  "Minor mode for interacting with the Axiomander contract system.

When enabled in a Python buffer, this mode ensures that Axiomander LSP
is active alongside Pyright and provides keybindings for contract
navigation, inspection, and code actions."
  :init-value nil
  :lighter " Axio"
  :keymap (let ((map (make-sparse-keymap)))
            ;; Fill bindings below
            map)
  (if axiomander-mode
      (axiomander--enable)
    (axiomander--disable)))
```

The agent should implement at least:

```elisp
(defun axiomander--enable ()
  "Enable Axiomander behavior in the current buffer."
  ;; Make sure lsp is running and both clients are allowed.
  (setq-local lsp-enabled-clients '(pyright axiomander-lsp))
  (unless (bound-and-true-p lsp-mode)
    (lsp-deferred)))

(defun axiomander--disable ()
  "Disable Axiomander-specific behavior in the current buffer."
  ;; You can either restore previous `lsp-enabled-clients` if you saved it,
  ;; or simply leave the session running and only remove keybindings/UI.
  )
```

### 3.2. Recommended keybindings

The agent should fill in `axiomander-mode-map` with commands that talk to the Axiomander server via `lsp-mode` primitives.

Suggested bindings (all prefixed under `C-c a`):

- `C-c a v` – View a summary of contracts relevant to the current symbol.
- `C-c a d` – Show contract diagnostics for the current buffer.
- `C-c a a` – Apply a suggested contract/code action at point.
- `C-c a j` – Jump between implementation and contract/spec file (if Axiomander exposes this).

Skeleton definitions:

```elisp
(define-key axiomander-mode-map (kbd "C-c a v") #'axiomander-view-contracts)
(define-key axiomander-mode-map (kbd "C-c a d") #'axiomander-show-diagnostics)
(define-key axiomander-mode-map (kbd "C-c a a") #'axiomander-apply-action)
(define-key axiomander-mode-map (kbd "C-c a j") #'axiomander-jump-related)
```

The agent should implement these in terms of LSP:

- Use `lsp-execute-code-action` to trigger Axiomander-provided code actions.
- Use `lsp-send-execute-command` for Axiomander-specific commands.
- Use `lsp-treemacs-*` or simple buffers to display structured output.

For example, `axiomander-apply-action` might:

1. Ask the server for available `codeAction`s at point.
2. Filter actions whose title starts with `"Axiomander:"`.
3. Present them via `completing-read` and execute the chosen one.

### 3.3. Displaying contract information

The UX can be simple but should be script-friendly:

- A plain `*axiomander-contracts*` buffer that is recreated each time.
- Using standard Emacs navigation (`n`, `p`, `RET` to jump).
- Each item should record its originating file/position using text properties so that `RET` can `xref-push-marker-stack` and jump back to the appropriate location in the source.

The agent does **not** need to care about JSON or protocol details directly; it should always go through `lsp-mode` helpers to talk to the server.

---

## 4. Startup and project workflow

### 4.1. Enabling in a project

Recommended flow for a Python project using Axiomander:

1. At project root, create `.dir-locals.el`:
   ```elisp
   ((python-mode
     (lsp-enabled-clients . (pyright axiomander-lsp))
     (eval . (axiomander-mode 1))))
   ```

2. Open a Python file inside the project.
3. `axiomander-mode` should auto-enable (via the `eval` in `.dir-locals.el`).
4. `lsp-mode` starts; both Pyright and Axiomander connect.
5. You can now use `C-c a` keybindings to interact with contracts.

### 4.2. Debugging

The agent should ensure that common debugging hooks are available:

- `M-x lsp-describe-session` – verify both servers are listed.
- `M-x lsp-log` – check server startup logs, errors, and messages.
- If Axiomander fails to start, display a helpful message suggesting:
  - Check that `axiomander-lsp` is on PATH.
  - Check that the virtualenv is activated or the absolute path is correct.

Optional: expose a helper command:

```elisp
(defun axiomander-lsp-doctor ()
  "Show status information for Axiomander + Pyright."
  (interactive)
  (message "lsp-mode: %s, clients: %S"
           (if (bound-and-true-p lsp-mode) "on" "off")
           (lsp-workspaces)))
```

---

## 5. Summary for the agent

When implementing the Emacs integration:

1. **Use `lsp-mode`** as the transport layer.
2. **Use `lsp-pyright`** for standard Python intelligence.
3. **Register Axiomander as `:add-on? t`** with its own `:server-id 'axiomander-lsp`.
4. **Provide `axiomander-mode`** as a minor mode that:
   - Ensures `lsp-mode` is running.
   - Ensures both `pyright` and `axiomander-lsp` are enabled.
   - Binds a small, stable set of `C-c a` commands to Axiomander functionality.
5. **Use LSP primitives** (`lsp-execute-code-action`, `lsp-send-execute-command`, `lsp-request`) instead of manually dealing with JSON.
6. **Keep everything project‑local** via `.dir-locals.el` where possible, so users can opt in per project.

This is the contract the Axiomander Emacs mode should satisfy.
