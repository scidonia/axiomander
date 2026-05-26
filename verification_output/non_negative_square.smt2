(set-option :produce-models true)
(set-logic ALL)

; ==================================================
; Axiomander Verification Condition for: non_negative_square
; Generated at: 2025-12-12 08:50:17.374707
; ==================================================
;
; This file contains the verification condition for proving that
; the postcondition holds given the preconditions.
; 
; Structure: P ∧ ¬Q where:
; - P: Preconditions (assumed to be true)
; - ¬Q: Negated postcondition (trying to prove impossible)
;
; If result is UNSAT: Postcondition is valid ✓
; If result is SAT: Counterexample exists ✗
; ==================================================

; Variable declarations:
(declare-const x_0 Int)
(declare-const result_1 Int)

; Function body constraints:
(assert (= result_1 (* x_0 x_0)))

; Preconditions (P) - assumed true:
(assert true)

; Negated postconditions (¬Q) - trying to prove impossible:
; (If UNSAT, then postconditions are valid given preconditions)
(assert (not (<= 0 result_1)))

; Check satisfiability:
; UNSAT = Verification successful (postcondition always holds)
; SAT   = Verification failed (counterexample exists)
(check-sat)
(get-model)