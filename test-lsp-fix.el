;;; test-lsp-fix.el --- Test script to verify LSP fix -*- lexical-binding: t; -*-

;; Quick test to verify the lambda function fix

(defun test-axiomander-lsp-fix ()
  "Test that Axiomander LSP configuration loads without errors."
  (interactive)
  (let ((errors nil))
    
    ;; Test 1: Load simple version
    (condition-case err
        (progn
          (load-file "axiomander-simple.el")
          (message "✅ Simple configuration loaded successfully"))
      (error
       (setq errors (cons (format "Simple config error: %s" err) errors))))
    
    ;; Test 2: Load complex version
    (condition-case err
        (progn
          (load-file "axiomander-example.el")
          (message "✅ Complex configuration loaded successfully"))
      (error
       (setq errors (cons (format "Complex config error: %s" err) errors))))
    
    ;; Report results
    (if errors
        (progn
          (message "❌ Errors found:")
          (dolist (error errors)
            (message "  - %s" error)))
      (message "✅ All configurations loaded successfully!"))))

;; Function to restart LSP cleanly
(defun restart-axiomander-lsp ()
  "Cleanly restart Axiomander LSP."
  (interactive)
  (when (fboundp 'lsp-workspace-shutdown)
    (lsp-workspace-shutdown))
  (when (fboundp 'lsp-restart-workspace)
    (lsp-restart-workspace))
  (message "Restarted Axiomander LSP"))

(provide 'test-lsp-fix)

;;; test-lsp-fix.el ends here