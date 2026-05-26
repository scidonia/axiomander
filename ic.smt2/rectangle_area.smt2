(set-option :produce-models true)
(set-logic ALL)

; ==================================================
; Axiomander Verification Condition for: rectangle_area
; Generated at: 2025-12-12 08:51:03.090892
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
(declare-const width_0 Int)
(declare-const height_1 Int)
(declare-const area_2 Int)

; Function body constraints:
(assert (= area_2 (* width_0 height_1)))

; Preconditions (P) - assumed true:
(assert (< 0 width_0))
(assert (< 0 height_1))
(assert (>= 20 width_0))
(assert (>= 20 height_1))

; Check satisfiability:
; UNSAT = Verification successful (postcondition always holds)
; SAT   = Verification failed (counterexample exists)
(check-sat)
(get-model)