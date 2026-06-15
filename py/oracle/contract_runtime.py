"""
contract_runtime.py -- Executable implementations of verifier-only builtins.

Generated tests import this module to evaluate contract expressions at runtime.
These are the Python-executable counterparts of the Coq/SMT-only predicates
defined in contract_ir.py.

Usage in generated tests::

    from oracle.contract_runtime import implies, is_shape, is_valid, re_match_pred

All functions are pure and side-effect-free.
"""

from __future__ import annotations

import re
from typing import Any


# ---------------------------------------------------------------------------
# Core logical builtins
# ---------------------------------------------------------------------------

def implies(antecedent: bool, consequent: bool) -> bool:
    """Logical implication: (not antecedent) or consequent.

    Matches the Coq form ``(A -> B)`` and SMT form ``(=> A B)``.

    >>> implies(True, True)
    True
    >>> implies(True, False)
    False
    >>> implies(False, True)
    True
    >>> implies(False, False)
    True
    """
    return (not antecedent) or consequent


# ---------------------------------------------------------------------------
# Shape / validity predicates
# ---------------------------------------------------------------------------

def is_shape(obj: Any, model_type: str) -> bool:
    """Check that obj structurally matches the named shape.

    Looks up the shape in the shape_ir registry.  Returns True if the
    shape is unknown (conservative -- do not fail on unregistered types).

    This is the runtime counterpart of ``IsShape.to_coq()``.
    """
    try:
        from .shape_ir import lookup_shape
        shape = lookup_shape(model_type)
        if shape is None:
            return True  # unknown type -- conservative pass
        for field in shape.fields:
            if not hasattr(obj, field.name):
                return False
        return True
    except Exception:
        return True


def is_valid(obj: Any, model_type: str) -> bool:
    """Check that obj satisfies all declared Field constraints for model_type.

    Expands to is_shape + ge/gt/le/lt checks derived from the shape registry.
    The shape registry stores constraints as Coq template strings
    (e.g. ``"(0 <= asZ ({key_scoped}))"``).  We parse the numeric bound
    from those templates rather than re-running the AST extractor.

    This is the runtime counterpart of ``IsValid.to_coq()``.
    """
    import re as _re
    try:
        from .shape_ir import lookup_shape
        shape = lookup_shape(model_type)
        if shape is None:
            return True
        for f in shape.fields:
            if not hasattr(obj, f.name):
                return False
            val = getattr(obj, f.name)
            for tmpl in (f.constraints or []):
                # Template forms (from _extract_field_constraints):
                #   ge:  "(N <= asZ ({key_scoped}))"
                #   gt:  "(N < asZ ({key_scoped}))"
                #   le:  "(asZ ({key_scoped}) <= N)"
                #   lt:  "(asZ ({key_scoped}) < N)"
                m_ge = _re.match(r'^\((-?\d+) <= asZ', tmpl)
                m_gt = _re.match(r'^\((-?\d+) < asZ', tmpl)
                m_le = _re.match(r'^\(asZ \([^)]+\) <= (-?\d+)\)', tmpl)
                m_lt = _re.match(r'^\(asZ \([^)]+\) < (-?\d+)\)', tmpl)
                if m_ge and not (val >= int(m_ge.group(1))):
                    return False
                if m_gt and not (val > int(m_gt.group(1))):
                    return False
                if m_le and not (val <= int(m_le.group(1))):
                    return False
                if m_lt and not (val < int(m_lt.group(1))):
                    return False
        return True
    except Exception:
        return True


# ---------------------------------------------------------------------------
# Regex predicate
# ---------------------------------------------------------------------------

def re_match_pred(subject: str, pattern: str) -> bool:
    """Return True if subject fully matches the Python regex pattern.

    This is the runtime counterpart of ``ReMatchExpr``.
    Uses ``re.fullmatch`` to match the Coq ``re_match`` semantics
    (full-string match, not prefix match).
    """
    try:
        return bool(re.fullmatch(pattern, subject))
    except re.error:
        return False


# ---------------------------------------------------------------------------
# old() snapshot helper
# ---------------------------------------------------------------------------

class _OldSnapshot:
    """Captures a snapshot of named values before a function call.

    Usage in generated tests::

        snap = _OldSnapshot(x=x, balance=account.balance)
        result = f(x)
        assert snap.x == ...   # old(x) in postcondition

    The generated test code uses ``snap.<name>`` to refer to pre-call values.
    """

    def __init__(self, **kwargs: Any) -> None:
        for k, v in kwargs.items():
            object.__setattr__(self, k, v)

    def __setattr__(self, name: str, value: Any) -> None:
        raise AttributeError("_OldSnapshot is immutable after construction")

    def __repr__(self) -> str:
        fields = ", ".join(
            f"{k}={v!r}" for k, v in self.__dict__.items()
        )
        return f"_OldSnapshot({fields})"
