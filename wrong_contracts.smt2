; Z3 Constraints Dump
; Generated at: 2025-12-10 22:15:42.489857

; Variable declarations:
(declare-const wrong_precondition_too_restrictive_x Int)
(declare-const wrong_precondition_too_restrictive_result Int)
(declare-const wrong_precondition_too_permissive_x Int)
(declare-const wrong_precondition_too_permissive_result Int)
(declare-const wrong_postcondition_too_weak_a Int)
(declare-const wrong_postcondition_too_weak_b Int)
(declare-const wrong_postcondition_too_weak_result Int)
(declare-const wrong_postcondition_too_strong_x Int)
(declare-const wrong_postcondition_too_strong_result Int)
(declare-const wrong_postcondition_contradictory_x Int)
(declare-const wrong_postcondition_contradictory_result Int)
(declare-const wrong_implementation_off_by_one_n Int)
(declare-const wrong_implementation_off_by_one_result Int)
(declare-const wrong_implementation_wrong_logic_a Int)
(declare-const wrong_implementation_wrong_logic_b Int)
(declare-const wrong_implementation_wrong_logic_c Int)
(declare-const wrong_implementation_wrong_logic_result Int)
(declare-const wrong_implementation_infinite_loop_risk_n Int)
(declare-const wrong_implementation_infinite_loop_risk_result Int)
(declare-const wrong_implementation_infinite_loop_risk_counter Int)
(declare-const wrong_implementation_division_by_zero_x Int)
(declare-const wrong_implementation_division_by_zero_y Int)
(declare-const wrong_implementation_division_by_zero_result Real)
(declare-const wrong_implementation_type_error_items Int)
(declare-const wrong_implementation_type_error_total Int)
(declare-const wrong_implementation_type_error_items_len Int)
(declare-const test_wrong_examples_items Int)
(declare-const test_wrong_examples_total Int)
(declare-const test_wrong_examples_items_len Int)

; Constraints from all functions:
; Function: wrong_precondition_too_restrictive
(assert result_1 == x_0*2)
; Function: wrong_precondition_too_restrictive
(assert 0 == result_1)
; Function: wrong_precondition_too_restrictive
(assert 100 < x_0)
; Function: wrong_precondition_too_permissive
(assert result_1 == x_0*x_0)
; Function: wrong_precondition_too_permissive
(assert True)
; Function: wrong_postcondition_too_weak
(assert result_2 == a_0)
; Function: wrong_postcondition_too_weak
(assert result_2 == b_1)
; Function: wrong_postcondition_too_weak
(assert And(0 <= a_0, 0 <= b_1))
; Function: wrong_postcondition_too_strong
(assert result_1 == x_0 + 1)
; Function: wrong_postcondition_too_strong
(assert 0 <= x_0)
; Function: wrong_postcondition_contradictory
(assert result_1 == x_0*2)
; Function: wrong_postcondition_contradictory
(assert 0 < x_0)
; Function: wrong_implementation_wrong_logic
(assert result_3 == a_0)
; Function: wrong_implementation_wrong_logic
(assert result_3 == b_1)
; Function: wrong_implementation_wrong_logic
(assert result_3 == c_2)
; Function: wrong_implementation_wrong_logic
(assert And(0 <= a_0, 0 <= b_1, 0 <= c_2))
; Function: wrong_implementation_wrong_logic
(assert And(100 >= a_0, 100 >= b_1, 100 >= c_2))
; Function: wrong_implementation_infinite_loop_risk
(assert result_1 == n_0)
; Function: wrong_implementation_infinite_loop_risk
(assert 0 == counter_2)
; Function: wrong_implementation_infinite_loop_risk
(assert result_1 == result_1 - 1)
; Function: wrong_implementation_infinite_loop_risk
(assert 0 < n_0)
; Function: wrong_implementation_infinite_loop_risk
(assert 10 >= n_0)
; Function: wrong_implementation_division_by_zero
(assert result_2 == ToReal(x_0/y_1))
; Function: wrong_implementation_division_by_zero
(assert 0 <= x_0)
; Function: wrong_implementation_division_by_zero
(assert 0 <= y_1)
; Function: wrong_implementation_type_error
(assert 0 == total_1)
; Function: wrong_implementation_type_error
(assert False)
; Function: wrong_implementation_type_error
(assert items_len_2 >= 0)
; Function: wrong_implementation_type_error
(assert 0 < items_len_2)
; Function: test_wrong_examples
(assert 0 == total_1)
; Function: test_wrong_examples
(assert False)
; Function: test_wrong_examples
(assert items_len_2 >= 0)
; Function: test_wrong_examples
(assert 0 < items_len_2)

; Check satisfiability
(check-sat)
(get-model)