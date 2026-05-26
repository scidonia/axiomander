(set-option :produce-models true)
(set-logic ALL)

; ==================================================
; Axiomander Verification Condition for: min_of_two
; Generated at: 2025-12-12 08:51:03.090795
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
(declare-const a_0 Int)
(declare-const b_1 Int)
(declare-const result_2 Int)

; Function body constraints:
(assert (= result_2 a_0))
(assert (= result_2 b_1))

; Preconditions (P) - assumed true:
(assert (and (>= a_0 (- 50)) (>= 50 a_0)))
(assert (and (>= b_1 (- 50)) (>= 50 b_1)))

; Negated postconditions (¬Q) - trying to prove impossible:
; (If UNSAT, then postconditions are valid given preconditions)
(assert (not (<= result_2 a_0)))
(assert (not (<= result_2 b_1)))
(assert (not (or (= result_2 a_0) (= result_2 b_1))))

; Check satisfiability:
; UNSAT = Verification successful (postcondition always holds)
; SAT   = Verification failed (counterexample exists)
(check-sat)
(get-model)