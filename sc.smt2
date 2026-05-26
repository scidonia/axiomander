; Z3 Constraints Dump
; Generated at: 2025-12-12 08:33:03.459655

; Variable declarations:
(declare-const always_positive_x Int)
(declare-const always_positive_result Int)
(declare-const increment_function_n Int)
(declare-const increment_function_result Int)
(declare-const non_negative_square_x Int)
(declare-const non_negative_square_result Int)
(declare-const bounded_add_a Int)
(declare-const bounded_add_b Int)
(declare-const bounded_add_result Int)

; Constraints from all functions:
; Function: always_positive
(assert result_1 == x_0)
; Function: always_positive
(assert 0 < x_0)
; Function: increment_function
(assert result_1 == n_0 + 1)
; Function: increment_function
(assert True)
; Function: non_negative_square
(assert result_1 == x_0*x_0)
; Function: non_negative_square
(assert True)
; Function: bounded_add
(assert result_2 == a_0 + b_1)
; Function: bounded_add
(assert 0 <= a_0)
; Function: bounded_add
(assert 0 <= b_1)
; Function: bounded_add
(assert 100 >= a_0)
; Function: bounded_add
(assert 100 >= b_1)

; Check satisfiability
(check-sat)
(get-model)