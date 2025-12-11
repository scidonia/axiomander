# axiomander:component:example-abs-001

"""Tests for component: absolute_value"""

# axiomander:component:example-abs-001
# axiomander:module:example
# axiomander:uniquified_name:absolute_value
# axiomander:original_name:absolute_value
# axiomander:path:

# AXIOMANDER_PREAMBLE_START
# Generated imports for compiled module
import sys
from pathlib import Path

# Add src directory to Python path for testing
src_path = Path(__file__).parent.parent / 'src'
if str(src_path) not in sys.path:
    sys.path.insert(0, str(src_path))

from example.absolute_value import *
from example.absolute_value_logical import *

import pytest
import unittest
try:
    from hypothesis import given, strategies as st
    HAS_HYPOTHESIS = True
except ImportError:
    HAS_HYPOTHESIS = False
# AXIOMANDER_PREAMBLE_END

"""Tests for absolute_value function."""

import pytest

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
        """Test that precondition is enforced."""
        # Valid inputs should pass precondition
        assert is_real_number(5)
        assert is_real_number(-3.14)
        assert is_real_number(0)
        
        # Invalid inputs should fail precondition
        assert not is_real_number("5")
        assert not is_real_number(None)
        assert not is_real_number(True)  # bool is not considered a real number
        assert not is_real_number([1, 2, 3])
    
    
    def test_invalid_input_types(self):
        """Test that invalid input types raise PreconditionViolationError."""
        from axiomander.exceptions import PreconditionViolationError
        
        invalid_inputs = ["5", None, True, [1, 2, 3], {"x": 5}]
        
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
