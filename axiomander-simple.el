;;; axiomander-simple.el --- Simple Axiomander LSP integration -*- lexical-binding: t; -*-

;; A minimal version of the Axiomander LSP client for testing and debugging

(require 'lsp-mode)

(defcustom axiomander-simple-server-command "axiomander-lsp"
  "Command to start the Axiomander LSP server."
  :type 'string
  :group 'axiomander)

(defvar axiomander-simple-server-id 'axiomander-lsp-simple
  "LSP server identifier for simple Axiomander client.")

(defun axiomander-simple-register ()
  "Register a simple Axiomander LSP client."
  (interactive)
  (message "Registering simple Axiomander LSP client...")
  (lsp-register-client
   (make-lsp-client 
    :new-connection (lsp-stdio-connection axiomander-simple-server-command)
    :activation-fn (lsp-activate-on "python")
    :server-id axiomander-simple-server-id
    :priority -1                    ; Run after primary Python servers
    :add-on? t                     ; Allow multiple servers  
    :language-id "python"))
  (message "Simple Axiomander LSP client registered"))

(defun axiomander-simple-start ()
  "Start the simple Axiomander LSP client."
  (interactive)
  (axiomander-simple-register)
  (when (eq major-mode 'python-mode)
    (lsp)))

(defun axiomander-simple-restart ()
  "Restart the Axiomander LSP server."
  (interactive)
  (lsp-restart-workspace)
  (message "Restarted Axiomander LSP server"))

;; Register the client when this file is loaded
(axiomander-simple-register)

(provide 'axiomander-simple)

;;; axiomander-simple.el ends here