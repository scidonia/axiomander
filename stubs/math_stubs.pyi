# Stub contracts for the Python math module.
# These provide pre/post conditions for external functions,
# enabling cross-module verification without black holes.

# Frame conventions:
#   reads:   variables/fields the function inspects (comma-separated, or "(none)")
#   writes:  variables/fields the function may mutate (comma-separated, or "(none)")
#
# Default (omitted): reads=(none), writes=(none) — pure, no side effects

def sqrt(x: float | int | bool) -> float:
    """requires: x >= 0
    ensures: result >= 0
    reads: x
    writes: (none)"""
    ...

def fabs(x: float | int | bool) -> float:
    """requires: True
    ensures: result >= 0
    reads: x
    writes: (none)"""
    ...
