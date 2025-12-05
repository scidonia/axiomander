"""Tests for absolute_value function."""

import pytest
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
        assert not absolute_value_precondition(True)  # bool is not considered a real number
        assert not absolute_value_precondition([1, 2, 3])
    
    def test_contract_postcondition(self):
        """Test that postcondition logic works correctly."""
        # Test postcondition with valid results
        assert absolute_value_postcondition(5, 5)  # result, input
        assert absolute_value_postcondition(5, -5)  # result, input
        assert absolute_value_postcondition(0, 0)   # result, input
        
        # Test postcondition with invalid results
        assert not absolute_value_postcondition(-5, 5)  # negative result should fail
        assert not absolute_value_postcondition(3, 5)   # wrong magnitude should fail
    
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
