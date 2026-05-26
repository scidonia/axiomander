;;; test-axiomander-lsp.el --- Test script for Axiomander LSP integration -*- lexical-binding: t; -*-

;; Test script to validate the modernized Axiomander LSP integration

(defun test-axiomander-integration ()
  "Test Axiomander LSP integration functionality."
  (interactive)
  (let ((test-results '())
        (test-count 0)
        (pass-count 0))
    
    ;; Helper function to run tests
    (cl-flet ((test (name condition)
                (setq test-count (1+ test-count))
                (if condition
                    (progn
                      (setq pass-count (1+ pass-count))
                      (push (format "✓ %s" name) test-results))
                  (push (format "✗ %s" name) test-results))))
      
      ;; Test 1: Package loads successfully
      (test "Package loads without errors"
            (condition-case nil
                (progn (require 'axiomander) t)
              (error nil)))
      
      ;; Test 2: Global mode function exists
      (test "axiomander-global-mode function defined"
            (fboundp 'axiomander-global-mode))
      
      ;; Test 3: Customization group exists
      (test "Axiomander customization group exists"
            (get 'axiomander 'group-documentation))
      
      ;; Test 4: Essential functions exist
      (test "Server command resolution function exists"
            (fboundp 'axiomander--resolve-server-command))
      
      (test "Server test function exists"
            (fboundp 'axiomander--server-test))
      
      (test "LSP client registration function exists"
            (fboundp 'axiomander--register-lsp-client))
      
      ;; Test 5: Interactive commands exist
      (test "Contract verification command exists"
            (fboundp 'axiomander-verify-contracts))
      
      (test "Server status command exists"
            (fboundp 'axiomander-server-status))
      
      (test "Doctor command exists"
            (fboundp 'axiomander-doctor))
      
      (test "Help command exists"
            (fboundp 'axiomander-help))
      
      ;; Test 6: Configuration variables exist
      (test "Server command variable exists"
            (boundp 'axiomander-server-command))
      
      (test "Enable contracts variable exists"
            (boundp 'axiomander-enable-contracts))
      
      ;; Test 7: Minor mode functionality
      (test "Contracts minor mode defined"
            (fboundp 'axiomander-contracts-mode))
      
      ;; Test 8: Command resolution works
      (test "Server command resolution returns list"
            (listp (axiomander--resolve-server-command)))
      
      ;; Test 9: LSP availability detection
      (test "LSP availability variable exists"
            (boundp 'axiomander--lsp-available))
      
      ;; Test 10: Global mode can be enabled (if LSP available)
      (when axiomander--lsp-available
        (test "Global mode can be enabled with LSP"
              (condition-case nil
                  (progn (axiomander-global-mode 1) 
                         (axiomander-global-mode -1) 
                         t)
                (error nil))))
      
      ;; Display results
      (with-output-to-temp-buffer "*Axiomander Test Results*"
        (princ (format "Axiomander LSP Integration Test Results\n"))
        (princ (format "======================================\n\n"))
        (princ (format "Passed: %d/%d tests\n\n" pass-count test-count))
        
        (princ "Test Details:\n")
        (dolist (result (reverse test-results))
          (princ (format "%s\n" result)))
        
        (princ "\nEnvironment Info:\n")
        (princ (format "Emacs version: %s\n" emacs-version))
        (princ (format "LSP mode available: %s\n" 
                       (if axiomander--lsp-available "Yes" "No")))
        (when axiomander--lsp-available
          (princ (format "LSP mode version: %s\n" (lsp-version))))
        (princ (format "Current major mode: %s\n" major-mode))
        
        (princ "\nRecommendations:\n")
        (unless axiomander--lsp-available
          (princ "- Install lsp-mode package for full functionality\n"))
        (when (< pass-count test-count)
          (princ "- Some tests failed - check implementation\n"))
        (princ "- Run M-x axiomander-doctor for detailed diagnostics\n"))
      
      ;; Return summary
      (message "Axiomander tests completed: %d/%d passed" pass-count test-count)
      (list :passed pass-count :total test-count :success (= pass-count test-count)))))

;; Quick test function
(defun test-axiomander-quick ()
  "Quick test of essential Axiomander functionality."
  (interactive)
  (message "Testing Axiomander integration...")
  (let ((result (test-axiomander-integration)))
    (if (plist-get result :success)
        (message "✓ All tests passed!")
      (message "⚠ %d/%d tests passed - see *Axiomander Test Results* buffer" 
               (plist-get result :passed) 
               (plist-get result :total)))))

(provide 'test-axiomander-lsp)

;;; test-axiomander-lsp.el ends here