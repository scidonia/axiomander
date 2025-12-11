;;; axiomander-mode.el --- Major mode for editing Axiomander Python code -*- lexical-binding: t; -*-

;; Copyright (C) 2024

;; Author: Axiomander Team
;; Version: 1.0.0
;; Package-Requires: ((emacs "26.1") (lsp-mode "8.0.0") (python-mode "0.1"))
;; Keywords: languages, python, axiomander, formal-verification
;; URL: https://github.com/your-org/axiomander

;;; Commentary:

;; This package provides a major mode for editing Axiomander Python code
;; with enhanced LSP support, syntax highlighting for formal verification
;; constructs, and specialized tooling integration.

;;; Code:

(require 'python)
(require 'lsp-mode nil t)
(require 'flycheck nil t)

(defgroup axiomander nil
  "Major mode for Axiomander Python development."
  :group 'languages
  :prefix "axiomander-")

(defcustom axiomander-python-executable "python3"
  "Python executable to use for Axiomander projects."
  :type 'string
  :group 'axiomander)

(defcustom axiomander-lsp-server-command nil
  "Command to start the Axiomander LSP server.
If nil, will try to auto-detect based on project structure."
  :type '(choice (const nil) (list string))
  :group 'axiomander)

(defcustom axiomander-enable-contract-highlighting t
  "Enable syntax highlighting for contract constructs."
  :type 'boolean
  :group 'axiomander)

;; Font-lock keywords for Axiomander-specific constructs
(defconst axiomander-font-lock-keywords
  '(;; Contract keywords
    ("\\<\\(requires\\|ensures\\|invariant\\|assert\\|assume\\|havoc\\)\\>" . font-lock-keyword-face)
    ;; Z3 related constructs
    ("\\<\\(forall\\|exists\\|implies\\|iff\\)\\>" . font-lock-builtin-face)
    ;; Axiomander decorators
    ("@\\(contract\\|pure\\|axiom\\|lemma\\|theorem\\)\\>" . font-lock-preprocessor-face)
    ;; Mathematical operators
    ("\\(==\\|!=\\|<=\\|>=\\|&&\\|||\\|!\\)" . font-lock-operator-face)))

(defvar axiomander-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-v") 'axiomander-verify-file)
    (define-key map (kbd "C-c C-t") 'axiomander-run-tests)
    (define-key map (kbd "C-c C-z") 'axiomander-z3-check)
    (define-key map (kbd "C-c C-s") 'axiomander-show-smt)
    map)
  "Keymap for Axiomander mode.")

;; LSP configuration
(defun axiomander-lsp-server-command ()
  "Get the LSP server command for Axiomander."
  (or axiomander-lsp-server-command
      ;; Try to auto-detect based on project structure
      (when (locate-dominating-file default-directory "pyproject.toml")
        (list axiomander-python-executable "-m" "pylsp"))
      ;; Fallback to pylsp
      (list "pylsp")))

(defun axiomander-setup-lsp ()
  "Setup LSP for Axiomander mode."
  (when (featurep 'lsp-mode)
    (lsp-register-client
     (make-lsp-client
      :new-connection (lsp-stdio-connection (axiomander-lsp-server-command))
      :major-modes '(axiomander-mode)
      :server-id 'axiomander-lsp
      :priority 1))
    (lsp)))

;; Interactive commands
(defun axiomander-verify-file ()
  "Verify the current Axiomander file."
  (interactive)
  (let ((file (buffer-file-name)))
    (if file
        (compile (format "%s -m axiomander.verify %s" axiomander-python-executable file))
      (message "Buffer is not visiting a file"))))

(defun axiomander-run-tests ()
  "Run tests for the current Axiomander project."
  (interactive)
  (let ((root (locate-dominating-file default-directory "pyproject.toml")))
    (if root
        (let ((default-directory root))
          (compile (format "%s -m pytest tests/" axiomander-python-executable)))
      (message "Not in an Axiomander project"))))

(defun axiomander-z3-check ()
  "Check the current file with Z3."
  (interactive)
  (let ((file (buffer-file-name)))
    (if file
        (compile (format "%s -m axiomander.z3_check %s" axiomander-python-executable file))
      (message "Buffer is not visiting a file"))))

(defun axiomander-show-smt ()
  "Show SMT-LIB output for the current file."
  (interactive)
  (let ((file (buffer-file-name)))
    (if file
        (let ((smt-buffer (get-buffer-create "*Axiomander SMT*"))
              (command (format "%s -m axiomander.show_smt %s" axiomander-python-executable file)))
          (with-current-buffer smt-buffer
            (erase-buffer)
            (insert (shell-command-to-string command))
            (smt-lib-mode))
          (display-buffer smt-buffer))
      (message "Buffer is not visiting a file"))))

;; Project detection
(defun axiomander-project-p ()
  "Check if current directory is an Axiomander project."
  (or (locate-dominating-file default-directory "pyproject.toml")
      (locate-dominating-file default-directory ".axiomander")))

;; Imenu support for contracts
(defun axiomander-imenu-create-index ()
  "Create imenu index for Axiomander constructs."
  (let ((index-alist '())
        (case-fold-search nil))
    (save-excursion
      (goto-char (point-min))
      ;; Find contract functions
      (while (re-search-forward "^\\s-*@contract\\s-*\n\\s-*def\\s-+\\([a-zA-Z_][a-zA-Z0-9_]*\\)" nil t)
        (push (cons (match-string 1) (match-beginning 1)) index-alist))
      ;; Find pure functions  
      (goto-char (point-min))
      (while (re-search-forward "^\\s-*@pure\\s-*\n\\s-*def\\s-+\\([a-zA-Z_][a-zA-Z0-9_]*\\)" nil t)
        (push (cons (format "%s (pure)" (match-string 1)) (match-beginning 1)) index-alist)))
    (nreverse index-alist)))

;;;###autoload
(define-derived-mode axiomander-mode python-mode "Axiomander"
  "Major mode for editing Axiomander Python code.

This mode extends python-mode with:
- Enhanced syntax highlighting for formal verification constructs
- LSP integration for Axiomander-specific tooling  
- Keybindings for verification and testing
- Specialized imenu support

\\{axiomander-mode-map}"
  ;; Font lock
  (when axiomander-enable-contract-highlighting
    (font-lock-add-keywords nil axiomander-font-lock-keywords))
  
  ;; Imenu
  (setq imenu-create-index-function 'axiomander-imenu-create-index)
  
  ;; LSP setup
  (axiomander-setup-lsp)
  
  ;; Flycheck integration
  (when (featurep 'flycheck)
    (flycheck-mode 1)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ax\\.py\\'" . axiomander-mode))
;;;###autoload
(add-to-list 'auto-mode-alist '("/axiomander/.*\\.py\\'" . axiomander-mode))

(provide 'axiomander-mode)

;;; axiomander-mode.el ends here