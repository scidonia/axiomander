# Stub contracts for Python built-in types and standard library.
# These provide contracts for methods that axiomander can't
# verify from source alone (C-implemented methods).

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

def loads(data: str) -> int:
    """requires: True
    ensures: len(result) > 0
    reads: data
    writes: (none)"""
    ...

def dumps(data: int) -> str:
    """requires: True
    ensures: len(result) > 0
    reads: data
    writes: (none)"""
    ...


# ── time methods ───────────────────────────────────────────────

def strftime(fmt: str) -> str:
    """requires: True
    ensures: True
    reads: fmt
    writes: (none)"""
    ...


# ── string methods ────────────────────────────────────────────

def str_contains(s: str, needle: str) -> int:
    """requires: True
    ensures: result == 0 or result == 1
    reads: s, needle
    writes: (none)"""
    ...


# ── dict methods ──────────────────────────────────────────────

def get(d: dict, key: int) -> int:
    """requires: True
    ensures: True
    reads: d
    writes: (none)"""
    ...


# ── list methods ──────────────────────────────────────────────

def pop(lst: list) -> int:
    """requires: True
    ensures: True
    reads: lst
    writes: lst"""
    ...


# ── set methods ───────────────────────────────────────────────

def add(s: set, x: int) -> None:
    """requires: True
    ensures: True
    reads: s, x
    writes: s"""
    ...

def remove(lst: list, x: int) -> None:
    """requires: True
    ensures: True
    reads: lst, x
    writes: lst"""
    ...
