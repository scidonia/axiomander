# Stub contracts for Python built-in types and standard library.
# These provide contracts for methods that axiomander can't
# verify from source alone (C-implemented methods).
#
# Type annotations follow Python spec where possible.
# Element-dependent types (list[int] vs list[str]) are noted
# since our model doesn't track type parameters.

# ── file I/O (Path methods) — black holes, external effects ───

def read_text(path: str) -> str:
    """requires: True
    ensures: True
    reads: (none)
    writes: path"""
    ...

def write_text(path: str, data: str):
    """requires: True
    ensures: True
    reads: (none)
    writes: path"""
    ...

# ── JSON methods ───────────────────────────────────────────────

def loads(data: str) -> dict | list | str | int | float | bool | None:
    """requires: True
    ensures: True
    reads: data
    writes: (none)
    note: returns dict | list | str | int | float | bool | None. int used as placeholder.
    """
    ...

def dumps(data: dict | list | str | int | float | bool | None) -> str:
    """requires: True
    ensures: len(result) > 0
    reads: data
    writes: (none)
    note: data: Any → str. List used as default. Result always non-empty string."""
    ...

# ── time methods ───────────────────────────────────────────────

def strftime(fmt: str) -> str:
    """requires: True
    ensures: True
    reads: fmt
    writes: (none)"""
    ...

# ── string methods ────────────────────────────────────────────

def str_contains(s: str, needle: str) -> bool:
    """requires: True
    ensures: result == 0 or result == 1
    reads: s, needle
    writes: (none)"""
    ...

# ── dict methods ──────────────────────────────────────────────

def get(d: dict, key: any, default: any) -> any:
    """requires: True
    ensures: True
    reads: d
    writes: (none)"""
    ...

# ── list methods ──────────────────────────────────────────────

def pop(lst: list[any]) -> any:
    """requires: len(lst) >= 1
    ensures: True
    reads: lst
    writes: lst
    note: returns list element type, not necessarily int"""
    ...

# ── set methods ───────────────────────────────────────────────

def add(s: set, x: any) -> None:
    """requires: True
    ensures: True
    reads: s, x
    writes: s
    note: x type depends on set element type"""
    ...

def remove(lst: list, x: any) -> None:
    """requires: True
    ensures: True
    reads: lst, x
    writes: lst
    note: x type depends on list element type"""
    ...

# ── string replace ─────────────────────────────────────────────

def str_replace(s: str, old: str, new: str) -> str:
    """requires: len(old) >= 1
    ensures: implies(old not in s, result == s)
             implies(old in s, new in result)
             old not in result or old in new
    reads: s, old, new
    writes: result"""
    ...
