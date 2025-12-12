;;; axiomander.el --- Modern Axiomander LSP integration for Python -*- lexical-binding: t; -*-

;; Copyright (C) 2024

;; Author: Axiomander Team
;; Version: 2.0.0
;; Package-Requires: ((emacs "28.1") (lsp-mode "9.0.0") (lsp-pyright "1.1.0") (python "0.1"))
;; Keywords: languages, python, axiomander, formal-verification, lsp, contracts
;; URL: https://github.com/your-org/axiomander

;;; Commentary:

;; This package provides modern Axiomander LSP integration for Python development.
;; It automatically registers the Axiomander LSP server to run alongside Pyright
;; on all Python files, providing contract-oriented programming features with
;; modern lsp-mode API support.
;;
;; Key Features:
;; - Modern LSP-mode API integration (v9.0+)
;; - Global LSP registration for all Python files
;; - Advanced error handling with server availability testing
;; - Contract-specific keybindings and commands
;; - Comprehensive configuration management
;; - Multi-server coordination with Pyright
;; - Semantic token support for contract highlighting
;; - Custom LSP capabilities for Axiomander features
;; - Enhanced debugging and diagnostic tools
;;
;; Quick Setup:
;;   (require 'axiomander)
;;   (axiomander-global-mode 1)
;;
;; Advanced Setup:
;;   (use-package axiomander
;;     :config
;;     (setq axiomander-server-command "axiomander-lsp"
;;           axiomander-enable-contracts t
;;           axiomander-strict-mode t)
;;     (axiomander-global-mode 1))

;;; Code:

(require 'python)
(require 'cl-lib)

;; LSP Mode is required for functionality but not for loading
(defvar axiomander--lsp-available nil
  "Whether lsp-mode is available for use.")

(defvar axiomander--lsp-ui-available nil
  "Whether lsp-ui is available for enhanced hover display.")

(condition-case nil
    (progn
      (require 'lsp-mode)
      (setq axiomander--lsp-available t))
  (error
   (message "Warning: lsp-mode not available. Axiomander LSP integration will be limited.")
   (setq axiomander--lsp-available nil)))

;; Try to load lsp-ui for better hover display
(condition-case nil
    (progn
      (require 'lsp-ui)
      (setq axiomander--lsp-ui-available t))
  (error
   (setq axiomander--lsp-ui-available nil)))

;; Customization Group
(defgroup axiomander nil
  "Modern Axiomander LSP integration for Python."
  :group 'languages
  :group 'lsp-mode
  :prefix "axiomander-"
  :link '(url-link :tag "GitHub" "https://github.com/your-org/axiomander"))

;; Server Configuration
(defcustom axiomander-server-command "axiomander-lsp"
  "Command to start the Axiomander LSP server.
Can be a string for a simple command or a list for command with arguments.
The command will be automatically validated for availability."
  :type '(choice 
          (string :tag "Command string")
          (repeat :tag "Command with arguments" string)
          (function :tag "Function returning command"))
  :group 'axiomander)

(defcustom axiomander-server-args nil
  "Additional arguments to pass to the Axiomander LSP server."
  :type '(repeat string)
  :group 'axiomander)

(defcustom axiomander-python-executable "python3"
  "Python executable to use for Axiomander projects.
Used as fallback when axiomander-lsp is not directly available."
  :type 'string
  :group 'axiomander)

;; Feature Configuration  
(defcustom axiomander-enable-contracts t
  "Enable contract verification and analysis."
  :type 'boolean
  :group 'axiomander)

(defcustom axiomander-strict-mode nil
  "Enable strict contract verification mode.
When enabled, all contract violations are treated as errors."
  :type 'boolean
  :group 'axiomander)

(defcustom axiomander-verification-timeout 30
  "Timeout in seconds for contract verification operations."
  :type 'integer
  :group 'axiomander)

(defcustom axiomander-log-level "info"
  "Log level for the Axiomander LSP server.
Valid values: trace, debug, info, warn, error."
  :type '(choice (const "trace") (const "debug") (const "info") 
                 (const "warn") (const "error"))
  :group 'axiomander)

;; UI Configuration
(defcustom axiomander-keybinding-prefix "C-c a"
  "Key prefix for Axiomander contract commands."
  :type 'string
  :group 'axiomander)

(defcustom axiomander-mode-lighter " Axio"
  "Mode line indicator when Axiomander contracts mode is active."
  :type 'string
  :group 'axiomander)

(defcustom axiomander-show-server-messages t
  "Show server startup and status messages in echo area."
  :type 'boolean
  :group 'axiomander)

(defcustom axiomander-library-directories nil
  "List of additional library directories for contract resolution.
These directories will be added to the LSP server's library path."
  :type '(repeat directory)
  :group 'axiomander)

;; Advanced Configuration
(defcustom axiomander-enable-semantic-tokens t
  "Enable semantic token support for contract highlighting."
  :type 'boolean
  :group 'axiomander)

(defcustom axiomander-completion-in-comments nil
  "Enable code completion inside comments."
  :type 'boolean
  :group 'axiomander)

(defcustom axiomander-auto-restart-server t
  "Automatically restart server if it crashes."
  :type 'boolean
  :group 'axiomander)

;; Hover Configuration
(defcustom axiomander-hover-at-point t
  "Show hover information at point rather than at cursor position."
  :type 'boolean
  :group 'axiomander)

(defcustom axiomander-hover-max-width 120
  "Maximum width of hover popup in characters."
  :type 'integer
  :group 'axiomander)

(defcustom axiomander-hover-max-height 30
  "Maximum height of hover popup in lines."
  :type 'integer
  :group 'axiomander)

(defcustom axiomander-hover-position 'top
  "Position of hover popup relative to point.
Valid values: top, bottom, at-point."
  :type '(choice (const top) (const bottom) (const at-point))
  :group 'axiomander)

;; Internal Variables
(defvar axiomander--server-id 'axiomander-lsp
  "LSP server identifier for Axiomander.")

(defvar axiomander--client-registered nil
  "Whether the Axiomander LSP client has been registered.")

(defvar axiomander--server-status 'unknown
  "Current status of the Axiomander LSP server.
Values: unknown, starting, running, failed, stopped.")

(defvar axiomander--startup-errors nil
  "List of recent server startup errors.")

;; Server Command Resolution
(defun axiomander--resolve-server-command ()
  "Resolve the server command to a list of strings."
  (let ((cmd (cond
              ((functionp axiomander-server-command)
               (funcall axiomander-server-command))
              ((listp axiomander-server-command)
               axiomander-server-command)
              (t (list axiomander-server-command)))))
    (append cmd axiomander-server-args)))

(defun axiomander--find-server-executable ()
  "Find the Axiomander LSP server executable.
Returns the full path if found, nil otherwise."
  (let ((cmd-list (axiomander--resolve-server-command)))
    (when cmd-list
      (let ((executable (car cmd-list)))
        (or (executable-find executable)
            ;; Try Python module as fallback
            (when (string= executable "axiomander-lsp")
              (when (executable-find axiomander-python-executable)
                (list axiomander-python-executable "-m" "axiomander.lsp.server"))))))))

(defun axiomander--server-test ()
  "Test if Axiomander LSP server is available and working."
  (let ((server-path (axiomander--find-server-executable)))
    (when (and server-path
               (if (listp server-path)
                   (executable-find (car server-path))
                 (file-executable-p server-path)))
      ;; Additional test: try to start server briefly to check if it works
      (condition-case err
          (let ((process (start-process "axiomander-test" nil 
                                        (if (listp server-path)
                                            (car server-path)
                                          server-path))))
            (when process
              (delete-process process)
              t))  ; Server can be started
        (error 
         (message "Axiomander LSP server test failed: %s" err)
         nil)))))

(defun axiomander--get-server-command ()
  "Get the complete server command for lsp-stdio-connection."
  (let ((resolved-cmd (axiomander--find-server-executable)))
    (cond
     ((listp resolved-cmd) resolved-cmd)
     ((stringp resolved-cmd) (list resolved-cmd))
     (t (axiomander--resolve-server-command)))))

;; LSP Configuration Management
(defun axiomander--register-settings ()
  "Register Axiomander LSP settings with lsp-mode."
  (lsp-register-custom-settings
   '(("axiomander.enable" axiomander-enable-contracts t)
     ("axiomander.server.logLevel" axiomander-log-level)
     ("axiomander.contracts.strict" axiomander-strict-mode t)
     ("axiomander.verification.timeout" axiomander-verification-timeout)
     ("axiomander.python.executable" axiomander-python-executable)
     ("axiomander.completion.inComments" axiomander-completion-in-comments t)
     ("axiomander.semanticTokens.enable" axiomander-enable-semantic-tokens t))))

(defun axiomander--initialization-options ()
  "Generate initialization options for the LSP server."
  `(:enableContracts ,(if axiomander-enable-contracts t :json-false)
    :strictMode ,(if axiomander-strict-mode t :json-false)
    :logLevel ,axiomander-log-level
    :verificationTimeout ,axiomander-verification-timeout
    :pythonExecutable ,axiomander-python-executable
    :libraryDirectories ,(apply 'vector axiomander-library-directories)
    :semanticTokens ,(if axiomander-enable-semantic-tokens t :json-false)))

(defun axiomander--library-directories (_workspace)
  "Return library directories for the workspace."
  axiomander-library-directories)

;; Server Lifecycle Management
(defun axiomander--on-server-initialized (workspace)
  "Called when Axiomander LSP server is initialized."
  (setq axiomander--server-status 'running)
  (when axiomander-show-server-messages
    (message "Axiomander LSP server initialized successfully"))
  ;; Configure server settings if functions are available
  (when (fboundp 'lsp--set-configuration)
    (with-lsp-workspace workspace
      (lsp--set-configuration (lsp-configuration-section "axiomander")))))

(defun axiomander--on-server-shutdown (_workspace)
  "Called when Axiomander LSP server shuts down."
  (setq axiomander--server-status 'stopped)
  (when axiomander-show-server-messages
    (message "Axiomander LSP server shut down")))

(defun axiomander--on-server-error (workspace error)
  "Handle Axiomander LSP server errors."
  (setq axiomander--server-status 'failed)
  (push (format "Server error: %s" error) axiomander--startup-errors)
  (when axiomander-show-server-messages
    (message "Axiomander LSP server error: %s" error))
  
  ;; Auto-restart if enabled
  (when axiomander-auto-restart-server
    (run-with-timer 2 nil 
                    (lambda () 
                      (when workspace
                        (lsp-restart-workspace workspace))))))

;; Hover Configuration
(defun axiomander--configure-hover ()
  "Configure hover display for better readability of verification results."
  (when axiomander--lsp-ui-available
    ;; Configure lsp-ui-doc for better hover display
    (setq-local lsp-ui-doc-enable t)
    (setq-local lsp-ui-doc-position axiomander-hover-position)
    (setq-local lsp-ui-doc-alignment 'window)  ; Better window alignment
    (setq-local lsp-ui-doc-border "darkgray")
    (setq-local lsp-ui-doc-max-width axiomander-hover-max-width)
    (setq-local lsp-ui-doc-max-height axiomander-hover-max-height)
    (setq-local lsp-ui-doc-use-childframe t)
    (setq-local lsp-ui-doc-use-webkit nil)
    (setq-local lsp-ui-doc-delay 0.1)  ; Faster display
    (setq-local lsp-ui-doc-include-signature t)
    (setq-local lsp-ui-doc-show-with-cursor axiomander-hover-at-point)
    (setq-local lsp-ui-doc-show-with-mouse t)
    
    ;; Force refresh of childframe settings
    (when (bound-and-true-p lsp-ui-doc-mode)
      (lsp-ui-doc-mode -1)
      (lsp-ui-doc-mode 1))
    
    (when axiomander-show-server-messages
      (message "✓ LSP-UI hover configured for Axiomander display")))
  
  ;; Configure basic lsp-mode hover as fallback
  (setq-local lsp-eldoc-enable-hover t)
  (setq-local lsp-signature-auto-activate t)
  (setq-local lsp-signature-render-documentation t))

;; Custom Capabilities
(defun axiomander--custom-capabilities ()
  "Return custom LSP capabilities for Axiomander."
  '((experimental . 
     ((axiomander . 
       ((commands . 
         ["axiomander.verifyContract"
          "axiomander.generateTest"  
          "axiomander.showSMT"
          "axiomander.explainAssertion"
          "axiomander.generateCounterexample"])
        (diagnostics . 
         ((contractViolation . t)
          (verificationResult . t)
          (assertionFailure . t)))
        (codeActions . 
         ((quickFix . t)
          (refactor . t)
          (contract . t)))
        (semanticTokens . 
         ((types . ["contract" "assertion" "invariant" "precondition" "postcondition"])
          (modifiers . ["pure" "verified" "failed"])))))))))

;; Semantic Token Configuration
(defvar axiomander-semantic-token-faces
  '(("contract" . font-lock-keyword-face)
    ("assertion" . font-lock-builtin-face)
    ("invariant" . font-lock-constant-face)
    ("precondition" . font-lock-preprocessor-face)
    ("postcondition" . font-lock-preprocessor-face))
  "Face mappings for Axiomander semantic tokens.")

;; LSP Client Registration
(defun axiomander--register-lsp-client ()
  "Register the modern Axiomander LSP client."
  (unless axiomander--client-registered
    (unless axiomander--lsp-available
      (error "lsp-mode is required for Axiomander LSP integration"))
    
    ;; Register settings first
    (axiomander--register-settings)
    
    ;; Register the LSP client
    (lsp-register-client
     (make-lsp-client 
      :new-connection (lsp-stdio-connection 
                       #'axiomander--get-server-command)
      :activation-fn (lsp-activate-on "python")
      :server-id axiomander--server-id
      :priority -1                    ; Run after primary Python servers
      :add-on? t                     ; Allow multiple servers
      :language-id "python"
      :completion-in-comments? axiomander-completion-in-comments
      :library-folders-fn #'axiomander--library-directories
       :initialized-fn #'axiomander--on-server-initialized
       :custom-capabilities (axiomander--custom-capabilities)
      :initialization-options #'axiomander--initialization-options
      :semantic-tokens-faces-overrides axiomander-semantic-token-faces
      :notification-handlers (ht ("axiomander/status" 
                                  (lambda (_workspace params)
                                    (axiomander--handle-status-notification params))))
      :action-handlers (ht ("axiomander.applyContract"
                            (lambda (action)
                              (axiomander--handle-apply-contract action))))))
    
    (setq axiomander--client-registered t)
    (when axiomander-show-server-messages
      (message "Axiomander LSP client registered"))))

;; Notification Handlers
(defun axiomander--handle-status-notification (params)
  "Handle status notification from Axiomander LSP server."
  (let ((status (gethash "status" params))
        (message (gethash "message" params)))
    (setq axiomander--server-status (intern status))
    (when (and message axiomander-show-server-messages)
      (message "Axiomander LSP: %s" message))))

;; Action Handlers
(defun axiomander--handle-apply-contract (action)
  "Handle contract application action."
  (let ((contract-code (gethash "contractCode" action))
        (position (gethash "position" action)))
    (when (and contract-code position)
      (save-excursion
        (if (fboundp 'lsp--position-to-point)
            (goto-char (lsp--position-to-point position))
          (goto-char (point))) ; fallback
        (insert contract-code))
      (message "Applied contract: %s" contract-code))))

;; Helper Functions for LSP Compatibility
(defun axiomander--buffer-uri ()
  "Get buffer URI in a compatible way."
  (if (fboundp 'lsp--buffer-uri)
      (lsp--buffer-uri)
    (concat "file://" (buffer-file-name))))

(defun axiomander--current-position ()
  "Get current position in a compatible way."
  (if (fboundp 'lsp--cur-position)
      (lsp--cur-position)
    (point)))

;; Server Status Functions
(defun axiomander--server-running-p ()
  "Check if Axiomander LSP server is currently running."
  (and (bound-and-true-p lsp-mode)
       (lsp-workspaces)
       (cl-some (lambda (ws) 
                  (and (fboundp 'lsp--workspace-server-id)
                       (eq (lsp--workspace-server-id ws) axiomander--server-id)))
                (lsp-workspaces))))

(defun axiomander--get-server-workspace ()
  "Get the Axiomander LSP workspace if active."
  (when (axiomander--server-running-p)
    (cl-find-if (lambda (ws)
                  (and (fboundp 'lsp--workspace-server-id)
                       (eq (lsp--workspace-server-id ws) axiomander--server-id)))
                (lsp-workspaces))))

;; Contract Mode Definition
(defvar axiomander-contracts-mode-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for `axiomander-contracts-mode'.")

(define-minor-mode axiomander-contracts-mode
  "Minor mode for Axiomander contract operations.

This mode provides keybindings for interacting with Axiomander
contract features when the LSP server is running.

Key bindings:
\\{axiomander-contracts-mode-map}"
  :init-value nil
  :lighter axiomander-mode-lighter
  :keymap axiomander-contracts-mode-map
  :group 'axiomander)

;; Dynamic Keymap Setup
(defun axiomander--setup-keybindings ()
  "Setup keybindings for contracts mode."
  (let ((map axiomander-contracts-mode-map))
    ;; Clear existing bindings
    (setcdr map nil)
    
    ;; Contract-specific commands
    (define-key map (kbd (concat axiomander-keybinding-prefix " a")) #'lsp-execute-code-action)
    (define-key map (kbd (concat axiomander-keybinding-prefix " d")) #'lsp-ui-flycheck-list)
    (define-key map (kbd (concat axiomander-keybinding-prefix " h")) #'lsp-describe-thing-at-point)
    (define-key map (kbd (concat axiomander-keybinding-prefix " i")) #'lsp-ui-doc-show)
    (define-key map (kbd (concat axiomander-keybinding-prefix " r")) #'lsp-find-references)
    (define-key map (kbd (concat axiomander-keybinding-prefix " j")) #'lsp-find-definition)
    
    ;; Axiomander-specific commands
    (define-key map (kbd (concat axiomander-keybinding-prefix " v")) #'axiomander-verify-contracts)
    (define-key map (kbd (concat axiomander-keybinding-prefix " t")) #'axiomander-generate-tests)
    (define-key map (kbd (concat axiomander-keybinding-prefix " s")) #'axiomander-show-smt)
    (define-key map (kbd (concat axiomander-keybinding-prefix " e")) #'axiomander-explain-assertion)
    (define-key map (kbd (concat axiomander-keybinding-prefix " c")) #'axiomander-generate-counterexample)
    
    ;; Utility commands
    (define-key map (kbd (concat axiomander-keybinding-prefix " S")) #'axiomander-server-status)
    (define-key map (kbd (concat axiomander-keybinding-prefix " R")) #'axiomander-restart-server)
    (define-key map (kbd (concat axiomander-keybinding-prefix " D")) #'axiomander-doctor)
    (define-key map (kbd (concat axiomander-keybinding-prefix " H")) #'axiomander-configure-hover)
    (define-key map (kbd (concat axiomander-keybinding-prefix " ?")) #'axiomander-help)))

;; Interactive Commands
(defun axiomander-verify-contracts ()
  "Verify contracts in the current file or selection."
  (interactive)
  (if (axiomander--server-running-p)
      (lsp-send-execute-command "axiomander.verifyContract" 
                                (vector (axiomander--buffer-uri)))
    (message "Axiomander LSP server not running")))

(defun axiomander-generate-tests ()
  "Generate tests for contracts in the current file."
  (interactive)
  (if (axiomander--server-running-p)
      (lsp-send-execute-command "axiomander.generateTest"
                                (vector (axiomander--buffer-uri)))
    (message "Axiomander LSP server not running")))

(defun axiomander-show-smt ()
  "Show SMT-LIB representation for the current contracts."
  (interactive)
  (if (axiomander--server-running-p)
      (lsp-send-execute-command "axiomander.showSMT"
                                (vector (axiomander--buffer-uri)))
    (message "Axiomander LSP server not running")))

(defun axiomander-explain-assertion ()
  "Explain the assertion at point."
  (interactive)
  (if (axiomander--server-running-p)
      (lsp-send-execute-command "axiomander.explainAssertion"
                                (vector (axiomander--buffer-uri) (axiomander--current-position)))
    (message "Axiomander LSP server not running")))

(defun axiomander-generate-counterexample ()
  "Generate counterexample for failed assertion at point."
  (interactive)
  (if (axiomander--server-running-p)
      (lsp-send-execute-command "axiomander.generateCounterexample"
                                (vector (axiomander--buffer-uri) (axiomander--current-position)))
    (message "Axiomander LSP server not running")))

(defun axiomander-server-status ()
  "Show detailed status of Axiomander LSP server."
  (interactive)
  (let ((workspace (axiomander--get-server-workspace)))
    (if workspace
        (message "Axiomander LSP: Running (Status: %s, PID: %s)" 
                 axiomander--server-status
                 (if (fboundp 'lsp--workspace-proc)
                     (lsp--workspace-proc workspace)
                   "unknown"))
      (message "Axiomander LSP: Not running (Last status: %s%s)"
               axiomander--server-status
               (if axiomander--startup-errors
                   (format ", Errors: %s" (length axiomander--startup-errors))
                 "")))))

(defun axiomander-restart-server ()
  "Restart the Axiomander LSP server."
  (interactive)
  (let ((workspace (axiomander--get-server-workspace)))
    (if workspace
        (progn
          (setq axiomander--startup-errors nil)
          (setq axiomander--server-status 'starting)
          (lsp-restart-workspace workspace)
          (message "Restarting Axiomander LSP server..."))
      (when (bound-and-true-p lsp-mode)
        (lsp)
        (message "Starting Axiomander LSP server...")))))

(defun axiomander-doctor ()
  "Run comprehensive diagnostics on Axiomander LSP setup."
  (interactive)
  (with-help-window "*Axiomander Doctor*"
    (princ "Axiomander LSP Diagnostics\n")
    (princ "==========================\n\n")
    
    ;; LSP Mode Check
    (princ "LSP Mode: ")
    (if (featurep 'lsp-mode)
        (princ (format "✓ Available (version: %s)\n" (lsp-version)))
      (princ "✗ Not loaded\n"))
    
    ;; Python Mode Check
    (princ "Python Mode: ")
    (if (eq major-mode 'python-mode)
        (princ "✓ Active\n")
      (princ (format "✗ Current mode: %s\n" major-mode)))
    
    ;; Server Command Check
    (princ "Server Command: ")
    (let ((cmd (axiomander--resolve-server-command)))
      (princ (format "%s\n" (mapconcat 'identity cmd " "))))
    
    ;; Server Availability Check
    (princ "Server Executable: ")
    (if (axiomander--server-test)
        (let ((exec-path (axiomander--find-server-executable)))
          (princ (format "✓ Found at %s\n" 
                        (if (listp exec-path)
                            (mapconcat 'identity exec-path " ")
                          exec-path))))
      (princ "✗ Not found or not executable\n"))
    
    ;; LSP Workspace Check
    (princ "LSP Workspace: ")
    (if (and (bound-and-true-p lsp-mode) (lsp-workspaces))
        (progn
          (princ "✓ Active\n")
          (princ "Active servers:\n")
          (dolist (ws (lsp-workspaces))
            (princ (format "  - %s (Status: %s)\n" 
                          (if (fboundp 'lsp--workspace-server-id)
                              (lsp--workspace-server-id ws)
                            "unknown")
                          (if (and (fboundp 'lsp--workspace-proc)
                                   (lsp--workspace-proc ws))
                              "running" "stopped")))))
      (princ "✗ No active workspace\n"))
    
    ;; Axiomander LSP Specific Check
    (princ "Axiomander LSP: ")
    (let ((workspace (axiomander--get-server-workspace)))
      (if workspace
          (princ (format "✓ Running (Status: %s)\n" axiomander--server-status))
        (princ (format "✗ Not running (Status: %s)\n" axiomander--server-status))))
    
    ;; Pyright Coordination Check
    (princ "Pyright Integration: ")
    (let ((pyright-active (cl-some (lambda (ws)
                                     (and (fboundp 'lsp--workspace-server-id)
                                          (eq (lsp--workspace-server-id ws) 'pyright)))
                                   (or (lsp-workspaces) '()))))
      (if pyright-active
          (princ "✓ Pyright server also active\n")
        (princ "- Pyright not active\n")))
    
    ;; Configuration Check
    (princ "\nConfiguration:\n")
    (princ (format "  Command: %s\n" axiomander-server-command))
    (princ (format "  Python: %s\n" axiomander-python-executable))
    (princ (format "  Enable contracts: %s\n" axiomander-enable-contracts))
    (princ (format "  Strict mode: %s\n" axiomander-strict-mode))
    (princ (format "  Log level: %s\n" axiomander-log-level))
    (princ (format "  Key prefix: %s\n" axiomander-keybinding-prefix))
    
    ;; Startup Errors
    (when axiomander--startup-errors
      (princ "\nRecent Errors:\n")
      (dolist (error axiomander--startup-errors)
        (princ (format "  - %s\n" error))))
    
    ;; Recommendations
    (princ "\nRecommendations:\n")
    (unless (axiomander--server-test)
      (princ "  - Install Axiomander with LSP support\n")
      (princ "  - Ensure axiomander-lsp is in PATH\n"))
    (unless (featurep 'lsp-mode)
      (princ "  - Install lsp-mode package\n"))
    (unless (eq major-mode 'python-mode)
      (princ "  - Open a Python file to test LSP integration\n"))))

(defun axiomander-configure-hover ()
  "Configure hover display settings for better verification results."
  (interactive)
  (axiomander--configure-hover)
  (message "Hover display configured for Axiomander verification results"))

(defun axiomander-help ()
  "Show comprehensive help for Axiomander commands."
  (interactive)
  (with-help-window "*Axiomander Help*"
    (princ "Axiomander Contract Commands\n")
    (princ "============================\n\n")
    (princ (format "Key prefix: %s\n\n" axiomander-keybinding-prefix))
    
    (princ "Contract Operations:\n")
    (princ (format "  %s a  - Execute code action (apply contract suggestions)\n" axiomander-keybinding-prefix))
    (princ (format "  %s v  - Verify contracts in current file\n" axiomander-keybinding-prefix))
    (princ (format "  %s t  - Generate tests for contracts\n" axiomander-keybinding-prefix))
    (princ (format "  %s s  - Show SMT-LIB representation\n" axiomander-keybinding-prefix))
    (princ (format "  %s e  - Explain assertion at point\n" axiomander-keybinding-prefix))
    (princ (format "  %s c  - Generate counterexample\n" axiomander-keybinding-prefix))
    
    (princ "\nNavigation:\n")
    (princ (format "  %s h  - Describe thing at point (hover info)\n" axiomander-keybinding-prefix))
    (princ (format "  %s i  - Show documentation popup\n" axiomander-keybinding-prefix))
    (princ (format "  %s r  - Find references\n" axiomander-keybinding-prefix))
    (princ (format "  %s j  - Jump to definition\n" axiomander-keybinding-prefix))
    (princ (format "  %s d  - Show diagnostics list\n" axiomander-keybinding-prefix))
    
    (princ "\nUtilities:\n")
    (princ (format "  %s S  - Show server status\n" axiomander-keybinding-prefix))
    (princ (format "  %s R  - Restart Axiomander LSP server\n" axiomander-keybinding-prefix))
    (princ (format "  %s D  - Run diagnostics (doctor)\n" axiomander-keybinding-prefix))
    (princ (format "  %s H  - Configure hover display settings\n" axiomander-keybinding-prefix))
    (princ (format "  %s ?  - Show this help\n" axiomander-keybinding-prefix))
    
    (princ "\nCustomization:\n")
    (princ "  M-x customize-group RET axiomander RET\n")
    
    (princ "\nFor more information:\n")
    (princ "  - https://github.com/your-org/axiomander\n")
    (princ "  - M-x axiomander-doctor (for troubleshooting)\n")))

;; Auto-activation Logic
(defun axiomander--maybe-enable-contracts-mode ()
  "Enable contracts mode if Axiomander LSP is running."
  (when (and (eq major-mode 'python-mode)
             (axiomander--server-running-p))
    (axiomander-contracts-mode 1)
    (axiomander--configure-hover)))

(defun axiomander--setup-python-mode ()
  "Setup Axiomander integration for Python mode."
  (when axiomander-global-mode
    ;; Ensure both servers are enabled
    (setq-local lsp-enabled-clients '(pyright axiomander-lsp))
    ;; Configure hover for better verification result display
    (axiomander--configure-hover)))

;; Global Mode Definition
(define-minor-mode axiomander-global-mode
  "Global mode for modern Axiomander LSP integration.

When enabled, this mode:
- Registers Axiomander LSP to run alongside Pyright on all Python files
- Provides comprehensive contract-specific keybindings when LSP is active  
- Shows visual indicators for contract availability
- Enables modern LSP features including semantic tokens and custom capabilities

This mode should be enabled in your Emacs configuration:
  (axiomander-global-mode 1)

For customization, see:
  M-x customize-group RET axiomander RET"
  :global t
  :group 'axiomander
  (if axiomander-global-mode
      (progn
        ;; Check LSP availability
        (unless axiomander--lsp-available
          (error "lsp-mode is required for Axiomander global mode. Please install lsp-mode package"))
        
        ;; Register LSP client
        (axiomander--register-lsp-client)
        
        ;; Setup keybindings
        (axiomander--setup-keybindings)
        
        ;; Enable global LSP configuration
        (setq lsp-enabled-clients '(pyright axiomander-lsp))
        
        ;; Add hooks
        (add-hook 'python-mode-hook #'axiomander--setup-python-mode)
        (add-hook 'lsp-mode-hook #'axiomander--maybe-enable-contracts-mode)
        
        ;; Initialize server status
        (setq axiomander--server-status 'unknown)
        
        (when axiomander-show-server-messages
          (message "Axiomander global mode enabled")))
    
    ;; Disable mode
    (remove-hook 'python-mode-hook #'axiomander--setup-python-mode)
    (remove-hook 'lsp-mode-hook #'axiomander--maybe-enable-contracts-mode)
    (when axiomander-show-server-messages
      (message "Axiomander global mode disabled"))))

;; Initialization
(when axiomander--lsp-available
  (with-eval-after-load 'lsp-mode
    (axiomander--register-lsp-client)))

;; Re-setup keybindings when prefix changes
(add-variable-watcher 'axiomander-keybinding-prefix
                      (lambda (_ _ _ _) (axiomander--setup-keybindings)))

(provide 'axiomander)

;;; axiomander.el ends here