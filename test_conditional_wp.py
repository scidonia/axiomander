#!/usr/bin/env python3
"""
Test script to check weakest precondition calculation for conditional statements.
"""

import ast
from src.axiomander.logic.weakest_precondition import WeakestPreconditionCalculator, WPResult

def test_conditional_max_wp():
    """Test weakest precondition calculation on conditional_max function."""
    
    # Source code with conditional logic
    source_code = '''
def conditional_max(a: int, b: int, c: int) -> int:
    """Returns the maximum of three integers using conditional logic."""
    assert a is not None
    assert b is not None  
    assert c is not None
    
    if a >= b and a >= c:
        result = a
    elif b >= c:
        result = b
    else:
        result = c
        
    # This is our target assertion to calculate WP for
    assert result >= a
    assert result >= b
    assert result >= c
    
    return result
'''

    # Parse the code
    tree = ast.parse(source_code)
    
    # Create a mock ParsedCode object
    from src.axiomander.logic.weakest_precondition import ParsedCode
    parsed_code = ParsedCode(tree, source_code, "test.py", {})
    
    # Create the calculator
    calculator = WeakestPreconditionCalculator(parsed_code)
    
    # Find the function and its assertions
    func_node = tree.body[0]  # First function definition
    assertions = [node for node in ast.walk(func_node) if isinstance(node, ast.Assert)]
    
    print(f"Found {len(assertions)} assertions in conditional_max")
    
    for i, assertion in enumerate(assertions):
        print(f"\nTesting assertion {i+1}: {ast.unparse(assertion.test)}")
        
        result = calculator.calculate_weakest_precondition(assertion)
        
        print(f"Result: {result.result}")
        print(f"Reason: {result.reason}")
        
        if result.condition:
            print(f"Weakest Precondition: {calculator.condition_to_string(result.condition)}")
        
        if result.intermediate_steps:
            print("Calculation steps:")
            for step in calculator.get_calculation_trace():
                print(f"  {step}")

if __name__ == "__main__":
    test_conditional_max_wp()