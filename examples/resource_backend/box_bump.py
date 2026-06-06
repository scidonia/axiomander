"""Bump: an intentionally trivial resource-aware function.

Used to test the Iris backend prototype pipeline.
"""

class Box:
    value: int


def bump(box: Box) -> int:
    """
    axiomander:
        requires:
            owns(box)
            box.value >= 0
        modifies:
            box.value
        ensures:
            box.value >= 1
    """
    box.value = box.value + 1
    return box.value
