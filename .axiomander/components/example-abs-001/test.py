"""Tests for absolute_value function."""

import pytest
from hypothesis import given, strategies as st
from .implementation import absolute_value
from .logical import absolute_value_precondition, absolute_value_postcondition
from axiomander.contracts import is_real_number


class TestAbsoluteValue:
    """Test cases for the absolute_value function."""

    def test_positive_numbers(self):
        """Test absolute value of positive numbers."""
        assert absolute_value(5) == 5
        assert absolute_value(3.14) == 3.14
        assert absolute_value(1) == 1

    def test_negative_numbers(self):
        """Test absolute value of negative numbers."""
        assert absolute_value(-5) == 5
        assert absolute_value(-3.14) == 3.14
        assert absolute_value(-1) == 1

    def test_zero(self):
        """Test absolute value of zero."""
        assert absolute_value(0) == 0
        assert absolute_value(0.0) == 0.0

    def test_contract_precondition(self):
        """Test that precondition logic works correctly."""
        # Valid inputs should pass precondition
        assert absolute_value_precondition(5)
        assert absolute_value_precondition(-3.14)
        assert absolute_value_precondition(0)

        # Invalid inputs should fail precondition
        assert not absolute_value_precondition("5")
        assert not absolute_value_precondition(None)
        assert not absolute_value_precondition(
            True
        )  # bool is not considered a real number
        assert not absolute_value_precondition([1, 2, 3])

    def test_contract_postcondition(self):
        """Test that postcondition logic works correctly."""
        # Test postcondition with valid results
        assert absolute_value_postcondition(5, 5)  # result, input
        assert absolute_value_postcondition(5, -5)  # result, input
        assert absolute_value_postcondition(0, 0)  # result, input

        # Test postcondition with invalid results
        assert not absolute_value_postcondition(-5, 5)  # negative result should fail
        assert not absolute_value_postcondition(3, 5)  # wrong magnitude should fail

    def test_invalid_input_types(self):
        """Test that invalid input types raise PreconditionViolationError."""
        from axiomander.exceptions import PreconditionViolationError

        invalid_inputs = ["5", None, [1, 2, 3], {"x": 5}]

        for invalid_input in invalid_inputs:
            with pytest.raises(PreconditionViolationError):
                absolute_value(invalid_input)

    def test_mathematical_properties(self):
        """Test mathematical properties of absolute value."""
        # |x| >= 0 for all x
        test_values = [5, -3, 0, 2.5, -1.7]
        for x in test_values:
            result = absolute_value(x)
            assert result >= 0, f"Absolute value should be non-negative, got {result}"

        # |x| = |-x| for all x
        for x in [5, 3.14, 1, 2.5]:
            assert absolute_value(x) == absolute_value(-x)

        # |x| = x if x >= 0
        for x in [5, 3.14, 0, 2.5]:
            assert absolute_value(x) == x

    @given(st.floats(allow_nan=False, allow_infinity=False))
    def test_property_non_negative(self, x: float) -> None:
        """Property: |x| >= 0 for all real numbers x."""
        result = absolute_value(x)
        assert (
            result >= 0
        ), f"Absolute value should be non-negative, got {result} for input {x}"

    @given(st.floats(allow_nan=False, allow_infinity=False))
    def test_property_symmetry(self, x: float) -> None:
        """Property: |x| = |-x| for all real numbers x."""
        pos_result = absolute_value(x)
        neg_result = absolute_value(-x)
        assert (
            pos_result == neg_result
        ), f"|{x}| = {pos_result} but |{-x}| = {neg_result}"

    @given(st.floats(min_value=0, allow_nan=False, allow_infinity=False))
    def test_property_identity_for_non_negative(self, x: float) -> None:
        """Property: |x| = x for all x >= 0."""
        result = absolute_value(x)
        assert result == x, f"For non-negative {x}, expected |x| = x, but got {result}"

    @given(st.floats(max_value=0, allow_nan=False, allow_infinity=False))
    def test_property_negation_for_non_positive(self, x: float) -> None:
        """Property: |x| = -x for all x <= 0."""
        result = absolute_value(x)
        expected = -x
        assert (
            result == expected
        ), f"For non-positive {x}, expected |x| = {expected}, but got {result}"

    @given(st.integers())
    def test_property_integer_inputs(self, x: int) -> None:
        """Property: absolute value works correctly for integer inputs."""
        result = absolute_value(x)
        assert isinstance(
            result, int
        ), f"Expected integer result for integer input, got {type(result)}"
        assert result >= 0, f"Result should be non-negative, got {result}"
        assert result == abs(
            x
        ), f"Should match Python's built-in abs(), got {result} vs {abs(x)}"

    @given(
        st.floats(allow_nan=False, allow_infinity=False),
        st.floats(allow_nan=False, allow_infinity=False),
    )
    def test_property_triangle_inequality(self, x: float, y: float) -> None:
        """Property: |x + y| <= |x| + |y| (triangle inequality)."""
        try:
            sum_abs = absolute_value(x + y)
            abs_sum = absolute_value(x) + absolute_value(y)
            assert (
                sum_abs <= abs_sum + 1e-10
            ), f"|{x} + {y}| = {sum_abs} > |{x}| + |{y}| = {abs_sum}"
        except OverflowError:
            # Skip cases where x + y overflows
            pass

    @given(st.one_of(st.text(), st.none(), st.lists(st.integers()), st.booleans()))
    def test_property_invalid_types_raise_precondition_error(
        self, invalid_input
    ) -> None:
        """Property: invalid input types should raise PreconditionViolationError."""
        from axiomander.exceptions import PreconditionViolationError

        with pytest.raises(PreconditionViolationError):
            absolute_value(invalid_input)
