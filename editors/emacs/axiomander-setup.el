;;; axiomander-setup.el --- Axiomander LSP integration setup -*- lexical-binding: t; -*-

;; Copyright (C) 2024

;; Author: Axiomander Team
;; Version: 2.0.0
;; Keywords: languages, python, axiomander, formal-verification, lsp, contracts
;; URL: https://github.com/your-org/axiomander

;;; Commentary:

;; This file loads the main Axiomander configuration from the project directory.
;; 
;; To use, symlink this file to your Emacs lisp directory:
;;   ln -sf ~/dev/Scidonia/axiomander/editors/emacs/axiomander-setup.el ~/.emacs.d/lisp/axiomander-setup.el
;;
;; Then in your init.el:
;;   (add-to-list 'load-path "~/.emacs.d/lisp")
;;   (require 'axiomander-setup)
;;   (axiomander-global-mode 1)

;;; Code:

(defvar axiomander-project-root
  (expand-file-name "~/dev/Scidonia/axiomander")
  "Root directory of the Axiomander project.")

(defvar axiomander-emacs-config-dir
  (expand-file-name "editors/emacs" axiomander-project-root)
  "Directory containing Axiomander Emacs configurations.")

;; Add the Axiomander emacs config directory to load path
(add-to-list 'load-path axiomander-emacs-config-dir)

;; Load the main Axiomander configuration (includes hover fixes)
(condition-case err
    (progn
      (load-file (expand-file-name "axiomander.el" axiomander-emacs-config-dir))
      
      ;; Enable Axiomander global mode for all Python files
      (when (fboundp 'axiomander-global-mode)
        (axiomander-global-mode 1))
      
      (message "✓ Axiomander LSP integration loaded successfully (with hover improvements)"))
  (error
   (message "⚠ Failed to load Axiomander LSP integration: %s" err)
   (message "   Make sure the Axiomander project is at: %s" axiomander-project-root)
   (message "   Install required packages: lsp-mode, lsp-ui")))

;; Keybinding to quickly reload Axiomander config
(defun reload-axiomander-config ()
  "Reload Axiomander LSP configuration."
  (interactive)
  (load-file (expand-file-name "~/.emacs.d/setup/axiomander.el"))
  (message "Axiomander configuration reloaded"))

(global-set-key (kbd "C-c a L") 'reload-axiomander-config)

;; Quick access to Axiomander files
(defun open-axiomander-config ()
  "Open the main Axiomander configuration file."
  (interactive)
  (find-file (expand-file-name "axiomander.el" axiomander-emacs-config-dir)))

(defun open-axiomander-project ()
  "Open the Axiomander project directory."
  (interactive)
  (dired axiomander-project-root))

(defun open-axiomander-examples ()
  "Open Axiomander examples directory."
  (interactive)
  (dired (expand-file-name "examples" axiomander-project-root)))

(global-set-key (kbd "C-c a O") 'open-axiomander-config)
(global-set-key (kbd "C-c a P") 'open-axiomander-project)
(global-set-key (kbd "C-c a E") 'open-axiomander-examples)

;; Status check function
(defun axiomander-setup-status ()
  "Show Axiomander setup status."
  (interactive)
  (with-output-to-temp-buffer "*Axiomander Setup Status*"
    (princ "Axiomander Setup Status\n")
    (princ "======================\n\n")
    
    (princ (format "Project Root: %s\n" axiomander-project-root))
    (princ (format "  Exists: %s\n" (if (file-exists-p axiomander-project-root) "✓" "✗")))
    
    (princ (format "Config Directory: %s\n" axiomander-emacs-config-dir))
    (princ (format "  Exists: %s\n" (if (file-exists-p axiomander-emacs-config-dir) "✓" "✗")))
    
    (let ((main-config (expand-file-name "axiomander.el" axiomander-emacs-config-dir)))
      (princ (format "Main Config: %s\n" main-config))
      (princ (format "  Exists: %s\n" (if (file-exists-p main-config) "✓" "✗"))))
    
    (princ (format "Global Mode: %s\n" 
                   (if (and (boundp 'axiomander-global-mode) axiomander-global-mode) "✓ Active" "✗ Inactive")))
    
    (princ (format "LSP Mode: %s\n" 
                   (if (featurep 'lsp-mode) "✓ Available" "✗ Not loaded")))
    
    (when (featurep 'lsp-ui)
      (princ (format "LSP UI: ✓ Available\n"))
      (princ "\nHover Configuration (Built-in):\n")
      (princ "  ✓ Improved positioning (above function, not right)\n")
      (princ "  ✓ Better sizing (customizable width/height)\n") 
      (princ "  ✓ Faster display (0.1s delay)\n")
      (princ "  ✓ Window alignment for better positioning\n")
      (princ "  ✓ Force refresh for immediate changes\n"))
    
    (unless (featurep 'lsp-ui)
      (princ (format "LSP UI: ✗ Not available - install for best hover experience\n")))
    
    (princ "\nSetup Commands:\n")
    (princ "  C-c a L - Reload Axiomander config\n")
    (princ "  C-c a O - Open Axiomander config file\n")
    (princ "  C-c a P - Open Axiomander project\n")
    (princ "  C-c a E - Open examples directory\n")
    (princ "  C-c a ? - Show this status\n")
    
    (princ "\nContract Commands (when LSP loaded):\n")
    (princ "  C-c a v - Verify contracts\n")
    (princ "  C-c a h - Show hover info\n")
    (princ "  C-c a H - Configure hover display\n")
    (princ "  C-c a D - Run Axiomander doctor\n")
    
    (when (fboundp 'axiomander-doctor)
      (princ "\nFor detailed diagnostics, run: M-x axiomander-doctor\n"))
    
    (unless (featurep 'lsp-mode)
      (princ "\n⚠ Install lsp-mode and lsp-ui packages for full functionality:\n")
      (princ "  M-x package-install RET lsp-mode RET\n")
      (princ "  M-x package-install RET lsp-ui RET\n"))))

(global-set-key (kbd "C-c a ?") 'axiomander-setup-status)

;; Installation helper
(defun axiomander-install-dependencies ()
  "Install required packages for Axiomander."
  (interactive)
  (package-refresh-contents)
  (package-install 'lsp-mode)
  (package-install 'lsp-ui)
  (message "✓ Axiomander dependencies installed. Restart Emacs or reload configuration."))

(global-set-key (kbd "C-c a I") 'axiomander-install-dependencies)

(message "Axiomander setup configuration loaded. Use C-c a ? for status, C-c a I to install dependencies.")

(provide 'axiomander-setup)
;;; axiomander-setup.el ends here