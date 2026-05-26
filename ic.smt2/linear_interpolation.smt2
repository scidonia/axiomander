(set-option :produce-models true)
(set-logic ALL)

; ==================================================
; Axiomander Verification Condition for: linear_interpolation
; Generated at: 2025-12-12 08:51:03.090831
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
(declare-const x_4 Int)
(declare-const result_5 Int)

; Function body constraints:
(assert (= result_5 y1_1))
(assert (= result_5 y2_3))

; Preconditions (P) - assumed true:
(assert (distinct x1_0 x2_2))
(assert (and (<= 0 x1_0) (>= 10 x1_0)))
(assert (and (<= 0 x2_2) (>= 10 x2_2)))
(assert (and (<= 0 y1_1) (>= 10 y1_1)))
(assert (and (<= 0 y2_3) (>= 10 y2_3)))
(assert (and (<= 0 x_4) (>= 10 x_4)))
(assert (and (>= x_4 x1_0) (<= x_4 x2_2)))

; Check satisfiability:
; UNSAT = Verification successful (postcondition always holds)
; SAT   = Verification failed (counterexample exists)
(check-sat)
(get-model)