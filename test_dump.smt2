; Z3 Constraints Dump
; Generated at: 2025-12-10 15:59:22.075983

; Variables:
; a: int (a_0)
; b: int (b_1)
; result: int (result_2)

; Constraints:
(assert result_2 == a_0 + b_1) ; Constraint 1
(assert 0 <= a_0) ; Constraint 2
(assert 0 <= b_1) ; Constraint 3
(assert 100 >= a_0) ; Constraint 4
(assert 100 >= b_1) ; Constraint 5

; Check satisfiability
(check-sat)
(get-model)