(set-option :produce-models true)
(set-logic ALL)

; ==================================================
; Axiomander Verification Condition for: distance_manhattan
; Generated at: 2025-12-12 08:51:03.090918
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
(declare-const x1_0 Int)
(declare-const y1_1 Int)
(declare-const x2_2 Int)
(declare-const y2_3 Int)
(declare-const distance_4 Int)
(declare-const dx_5 Int)
(declare-const dy_6 Int)

; Function body constraints:
(assert (= distance_4 (+ dx_5 dy_6)))
(assert (= dx_5 (- x2_2 x1_0)))
(assert (= dx_5 (- x1_0 x2_2)))
(assert (= dy_6 (- y2_3 y1_1)))
(assert (= dy_6 (- y1_1 y2_3)))

; Preconditions (P) - assumed true:
(assert (and (>= x1_0 (- 10)) (>= 10 x1_0)))
(assert (and (>= y1_1 (- 10)) (>= 10 y1_1)))
(assert (and (>= x2_2 (- 10)) (>= 10 x2_2)))
(assert (and (>= y2_3 (- 10)) (>= 10 y2_3)))

; Check satisfiability:
; UNSAT = Verification successful (postcondition always holds)
; SAT   = Verification failed (counterexample exists)
(check-sat)
(get-model)