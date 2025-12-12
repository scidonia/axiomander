;;; axiomander.el --- Axiomander LSP integration setup -*- lexical-binding: t; -*-

;; Axiomander formal verification for Python
;; This file loads the main Axiomander configuration from the project directory

(defvar axiomander-project-root
  (expand-file-name "~/dev/Scidonia/axiomander")
  "Root directory of the Axiomander project.")

(defvar axiomander-emacs-config-dir
  (expand-file-name "editors/emacs" axiomander-project-root)
  "Directory containing Axiomander Emacs configurations.")

;; Add the Axiomander emacs config directory to load path
(add-to-list 'load-path axiomander-emacs-config-dir)

;; Load the main Axiomander configuration
(condition-case err
    (progn
      (require 'axiomander)
      
      ;; Enable Axiomander global mode for all Python files
      (when (fboundp 'axiomander-global-mode)
        (axiomander-global-mode 1))
      
      (message "✓ Axiomander LSP integration loaded successfully"))
  (error
   (message "⚠ Failed to load Axiomander LSP integration: %s" err)
   (message "   Make sure the Axiomander project is at: %s" axiomander-project-root)))

;; Alternative: Load hover fix independently if main config fails
(unless (fboundp 'axiomander-global-mode)
  (condition-case err
      (progn
        (load-file (expand-file-name "axiomander-hover-fix.el" axiomander-emacs-config-dir))
        (message "✓ Axiomander hover fix loaded as fallback"))
    (error
     (message "⚠ Could not load Axiomander hover fix: %s" err))))

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

(global-set-key (kbd "C-c a O") 'open-axiomander-config)
(global-set-key (kbd "C-c a P") 'open-axiomander-project)

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
    
    (let ((hover-fix (expand-file-name "axiomander-hover-fix.el" axiomander-emacs-config-dir)))
      (princ (format "Hover Fix: %s\n" hover-fix))
      (princ (format "  Exists: %s\n" (if (file-exists-p hover-fix) "✓" "✗"))))
    
    (princ (format "Global Mode: %s\n" 
                   (if (and (boundp 'axiomander-global-mode) axiomander-global-mode) "✓ Active" "✗ Inactive")))
    
    (princ (format "LSP Mode: %s\n" 
                   (if (featurep 'lsp-mode) "✓ Available" "✗ Not loaded")))
    
    (princ "\nQuick Actions:\n")
    (princ "  C-c a L - Reload Axiomander config\n")
    (princ "  C-c a O - Open Axiomander config file\n")
    (princ "  C-c a P - Open Axiomander project\n")
    (princ "  C-c a D - Run Axiomander doctor (if loaded)\n")
    
    (when (fboundp 'axiomander-doctor)
      (princ "\nFor detailed diagnostics, run: M-x axiomander-doctor\n"))))

(global-set-key (kbd "C-c a ?") 'axiomander-setup-status)

(message "Axiomander setup configuration loaded. Use C-c a ? for status.")

(provide 'axiomander)
;;; axiomander.el ends here