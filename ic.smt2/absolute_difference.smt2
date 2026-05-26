(set-option :produce-models true)
(set-logic ALL)

; ==================================================
; Axiomander Verification Condition for: absolute_difference
; Generated at: 2025-12-12 08:51:03.090744
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
(declare-const y_1 Int)
(declare-const result_2 Int)

; Function body constraints:
(assert (= result_2 (- x_0 y_1)))
(assert (= result_2 (- y_1 x_0)))

; Preconditions (P) - assumed true:
(assert (and (>= x_0 (- 100)) (>= 100 x_0)))
(assert (and (>= y_1 (- 100)) (>= 100 y_1)))

; Check satisfiability:
; UNSAT = Verification successful (postcondition always holds)
; SAT   = Verification failed (counterexample exists)
(check-sat)
(get-model)