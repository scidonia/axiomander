(set-option :produce-models true)
(set-logic ALL)

; ==================================================
; Axiomander Verification Condition for: quadratic_discriminant
; Generated at: 2025-12-12 08:51:03.090605
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
(declare-const c_2 Int)
(declare-const discriminant_3 Int)

; Function body constraints:
(assert (= discriminant_3 (- (* b_1 b_1) (* 4 a_0 c_2))))

; Preconditions (P) - assumed true:
(assert (distinct 0 a_0))
(assert (and (>= a_0 (- 10)) (>= 10 a_0)))
(assert (and (>= b_1 (- 10)) (>= 10 b_1)))
(assert (and (>= c_2 (- 10)) (>= 10 c_2)))

; Negated postconditions (¬Q) - trying to prove impossible:
; (If UNSAT, then postconditions are valid given preconditions)
(assert (not (= discriminant_3 (- (* b_1 b_1) (* 4 a_0 c_2)))))

; Check satisfiability:
; UNSAT = Verification successful (postcondition always holds)
; SAT   = Verification failed (counterexample exists)
(check-sat)
(get-model)