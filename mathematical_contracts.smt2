; Z3 Constraints Dump
; Generated at: 2025-12-10 22:16:48.476680

; Variable declarations:
(declare-const absolute_value_x Int)
(declare-const absolute_value_result Int)
(declare-const max_of_two_a Int)
(declare-const max_of_two_b Int)
(declare-const max_of_two_result Int)
(declare-const simple_factorial_n Int)
(declare-const simple_factorial_result Int)
(declare-const sum_positive_numbers_numbers Int)
(declare-const sum_positive_numbers_total Int)
(declare-const main_computation_abs_result Int)
(declare-const main_computation_max_result Int)
(declare-const main_computation_fact_result Int)

; Constraints from all functions:
; Function: absolute_value
(assert result_1 == x_0)
; Function: absolute_value
(assert result_1 == -x_0)
; Function: absolute_value
(assert True)
; Function: max_of_two
(assert result_2 == a_0)
; Function: max_of_two
(assert result_2 == b_1)
; Function: max_of_two
(assert True)
; Function: max_of_two
(assert True)

; Check satisfiability
(check-sat)
(get-model)