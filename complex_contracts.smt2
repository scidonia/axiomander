; Z3 Constraints Dump
; Generated at: 2025-12-10 22:15:25.298410

; Variable declarations:
(declare-const conditional_max_a Int)
(declare-const conditional_max_b Int)
(declare-const conditional_max_c Int)
(declare-const conditional_max_result Int)
(declare-const fibonacci_iterative_n Int)
(declare-const fibonacci_iterative_result Int)
(declare-const safe_division_numerator Int)
(declare-const safe_division_denominator Int)
(declare-const safe_division_result Real)
(declare-const factorial_with_contracts_n Int)
(declare-const factorial_with_contracts_result Int)
(declare-const clamp_value_value Int)
(declare-const clamp_value_min_val Int)
(declare-const clamp_value_max_val Int)
(declare-const clamp_value_result Int)
(declare-const euclidean_gcd_a Int)
(declare-const euclidean_gcd_b Int)
(declare-const euclidean_gcd_result Int)
(declare-const triangle_type_a Int)
(declare-const triangle_type_b Int)
(declare-const triangle_type_c Int)

; Constraints from all functions:
; Function: conditional_max
(assert result_3 == a_0)
; Function: conditional_max
(assert result_3 == b_1)
; Function: conditional_max
(assert result_3 == c_2)
; Function: euclidean_gcd
(assert 0 < a_0)
; Function: euclidean_gcd
(assert 0 < b_1)
; Function: euclidean_gcd
(assert And(100 >= a_0, 100 >= b_1))

; Check satisfiability
(check-sat)
(get-model)