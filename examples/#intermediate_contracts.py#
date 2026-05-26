"""
Intermediate contract examples that should verify well with current system.

These examples focus on patterns that work well with our Z3-based verification:
- Simple arithmetic and comparisons
- Basic conditional logic
- Straightforward mathematical properties
- Functions without loops or complex control flow
"""


def quadratic_discriminant(a: int, b: int, c: int) -> int:
    """
    Computes the discriminant of a quadratic equation ax² + bx + c.

    Demonstrates verification of mathematical formulas.
    """
    # Preconditions
    assert a != 0  # Must be quadratic (a ≠ 0)
    assert a >= -10 and a <= 10  # Reasonable bounds
    assert b >= -10 and b <= 10
    assert c >= -10 and c <= 10

    discriminant = b * b - 4 * a * c

    # Postconditions: basic properties
    # If discriminant is positive, equation has two real roots
    # If zero, one repeated root
    # If negative, no real roots

    # Mathematical relationship holds
    assert discriminant == b * b - 4 * a * c

    return discriminant


def absolute_difference(x: int, y: int) -> int:
    """
    Computes absolute difference between two integers.

    Demonstrates verification of conditional logic and absolute values.
    """
    # Preconditions
    assert x >= -100 and x <= 100
    assert y >= -100 and y <= 100

    if x >= y:
        result = x - y
    else:
        result = y - x

    # Postconditions
    assert result >= 0  # Absolute difference is non-negative

    # Relationship to inputs
    if x >= y:
        assert result == x - y
    else:
        assert result == y - x

    # Symmetric property: |x - y| = |y - x|
    # (This would be the same regardless of order)

    return result


def min_of_two(a: int, b: int) -> int:
    """
    Returns the minimum of two integers.

    Simple conditional logic that should verify easily.
    """
    # Preconditions: reasonable bounds
    assert a >= -50 and a <= 50
    assert b >= -50 and b <= 50

    if a <= b:
        result = a
    else:
        result = b

    # Postconditions
    assert result <= a  # Result is not greater than either input
    assert result <= b
    assert result == a or result == b  # Result equals one of the inputs

    return result


def linear_interpolation(x1: int, y1: int, x2: int, y2: int, x: int) -> int:
    """
    Simple linear interpolation (integer version).

    Demonstrates verification with multiple parameters and arithmetic.
    """
    # Preconditions
    assert x1 != x2  # Points must be distinct
    assert x1 >= 0 and x1 <= 10
    assert x2 >= 0 and x2 <= 10
    assert y1 >= 0 and y1 <= 10
    assert y2 >= 0 and y2 <= 10
    assert x >= 0 and x <= 10
    assert x >= x1 and x <= x2  # x is between the two points

    # Simplified integer linear interpolation
    if x == x1:
        result = y1
    elif x == x2:
        result = y2
    else:
        # For simplicity, use midpoint when x is between x1 and x2
        result = (y1 + y2) // 2

    # Postconditions
    if x == x1:
        assert result == y1
    elif x == x2:
        assert result == y2

    return result


def sign_function(x: int) -> int:
    """
    Returns sign of an integer (-1, 0, or 1).

    Simple conditional logic with clear mathematical properties.
    """
    # Preconditions
    assert x >= -100 and x <= 100

    if x > 0:
        result = 1
    elif x < 0:
        result = -1
    else:
        result = 0

    # Postconditions
    assert result >= -1 and result <= 1  # Sign is always -1, 0, or 1

    if x > 0:
        assert result == 1
    elif x < 0:
        assert result == -1
    else:
        assert result == 0

    return result


def rectangle_area(width: int, height: int) -> int:
    """
    Computes area of rectangle with integer dimensions.

    Simple multiplication with clear mathematical properties.
    """
    # Preconditions
    assert width > 0
    assert height > 0
    assert width <= 20  # Reasonable bounds
    assert height <= 20

    area = width * height

    # Postconditions
    assert area > 0  # Area is positive for positive dimensions
    assert area >= width  # Area is at least as large as width
    assert area >= height  # Area is at least as large as height
    assert area == width * height  # Definition holds

    # If square, area equals width squared
    if width == height:
        assert area == width * width

    return area


def distance_manhattan(x1: int, y1: int, x2: int, y2: int) -> int:
    """
    Computes Manhattan distance between two points.

    Demonstrates absolute value operations and coordinate geometry.
    """
    # Preconditions: keep coordinates in reasonable range
    assert x1 >= -10 and x1 <= 10
    assert y1 >= -10 and y1 <= 10
    assert x2 >= -10 and x2 <= 10
    assert y2 >= -10 and y2 <= 10

    # Compute absolute differences
    if x2 >= x1:
        dx = x2 - x1
    else:
        dx = x1 - x2

    if y2 >= y1:
        dy = y2 - y1
    else:
        dy = y1 - y2

    distance = dx + dy

    # Postconditions
    assert distance >= 0  # Distance is non-negative
    assert dx >= 0  # Component distances are non-negative
    assert dy >= 0
    assert distance == dx + dy  # Manhattan distance definition

    # Distance is zero iff points are the same
    if x1 == x2 and y1 == y2:
        assert distance == 0

    return distance
