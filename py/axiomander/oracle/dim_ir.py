"""
Dimensional Analysis IR for Axiomander contracts.

Tracks units through arithmetic operations using a named dimension system.
Base dimensions are arbitrary strings -- fully user-defined, no hardcoded list.

Design principles:
  - DimVec is a sparse integer vector over named base dimensions.
  - Multiplication/division compose DimVecs algebraically.
  - Addition/subtraction require identical DimVecs (dimension error otherwise).
  - No implicit compatibility between different named dimensions.
    [USD] and [GBP] are genuinely distinct -- conversions must be explicit.
  - Integer exponents only (sufficient for financial and physical domains).
  - Dimensionless quantities have an empty DimVec: {}.

Examples:
  [USD]          = {"USD": 1}
  [USD/person]   = {"USD": 1, "person": -1}
  [GBP/USD]      = {"GBP": 1, "USD": -1}      -- exchange rate
  [share/account]= {"share": 1, "account": -1}
  [m/s^2]        = {"m": 1, "s": -2}
  1 (dimensionless) = {}

Grammar for dimension expressions (dim_expr):
  dim_expr ::= base_dim
             | dim_expr * dim_expr
             | dim_expr / dim_expr
             | dim_expr ^ integer
             | 1
             | ( dim_expr )
  base_dim ::= identifier   (letters, digits, underscores -- no leading digit)

Parsing is done by dim_parse() -- a hand-written recursive descent parser
over the token stream, not over strings.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Optional


# ── DimVec ────────────────────────────────────────────────────────

class DimVec:
    """Sparse integer vector over named base dimensions.

    Immutable and hashable -- suitable as dict keys and set members.
    Zero exponents are never stored (canonical form).
    """

    __slots__ = ("_components",)

    def __init__(self, components: dict[str, int] | None = None):
        # Canonicalise: remove zero exponents, sort for stable repr
        if components:
            self._components = {
                k: v for k, v in components.items() if v != 0
            }
        else:
            self._components = {}

    # ── Factory methods ──────────────────────────────────────────

    @classmethod
    def dimensionless(cls) -> "DimVec":
        """The multiplicative identity: empty exponent vector."""
        return cls()

    @classmethod
    def base(cls, name: str) -> "DimVec":
        """A single base dimension with exponent 1."""
        return cls({name: 1})

    # ── Algebraic operations ─────────────────────────────────────

    def __mul__(self, other: "DimVec") -> "DimVec":
        """Multiplication: add exponent vectors."""
        result = dict(self._components)
        for name, exp in other._components.items():
            result[name] = result.get(name, 0) + exp
        return DimVec(result)

    def __truediv__(self, other: "DimVec") -> "DimVec":
        """Division: subtract exponent vectors."""
        result = dict(self._components)
        for name, exp in other._components.items():
            result[name] = result.get(name, 0) - exp
        return DimVec(result)

    def __pow__(self, n: int) -> "DimVec":
        """Integer power: scale exponent vector."""
        if n == 0:
            return DimVec.dimensionless()
        return DimVec({name: exp * n for name, exp in self._components.items()})

    def compatible_with(self, other: "DimVec") -> bool:
        """Two DimVecs are compatible for addition iff they are identical."""
        return self._components == other._components

    def is_dimensionless(self) -> bool:
        return len(self._components) == 0

    # ── Display ──────────────────────────────────────────────────

    def __repr__(self) -> str:
        if not self._components:
            return "[1]"
        pos = [(n, e) for n, e in sorted(self._components.items()) if e > 0]
        neg = [(n, e) for n, e in sorted(self._components.items()) if e < 0]

        def fmt_pos(n: str, e: int) -> str:
            return n if e == 1 else f"{n}^{e}"

        def fmt_neg(n: str, e: int) -> str:
            return n if e == -1 else f"{n}^{-e}"

        num = "*".join(fmt_pos(n, e) for n, e in pos) or "1"
        if neg:
            den = "*".join(fmt_neg(n, e) for n, e in neg)
            return f"[{num}/{den}]"
        return f"[{num}]"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, DimVec):
            return NotImplemented
        return self._components == other._components

    def __hash__(self) -> int:
        return hash(frozenset(self._components.items()))

    @property
    def components(self) -> dict[str, int]:
        return dict(self._components)


# ── Dimension expression parser ───────────────────────────────────
#
# Tokenises then parses: dim_expr -> DimVec
# No regex on nested structure -- proper recursive descent.

_TOKEN_RE = re.compile(
    r"""
      (?P<int>   -?\d+         )   # integer (for exponents)
    | (?P<id>    [A-Za-z_]\w*  )   # identifier (base dimension or "1")
    | (?P<star>  \*             )   # multiplication
    | (?P<slash> /              )   # division
    | (?P<caret> \^             )   # power
    | (?P<lparen>\(             )   # left paren
    | (?P<rparen>\)             )   # right paren
    | (?P<ws>    \s+            )   # whitespace (skip)
    """,
    re.VERBOSE,
)


def _tokenise(text: str) -> list[tuple[str, str]]:
    """Tokenise a dimension expression string.

    Returns list of (kind, value) pairs, whitespace dropped.
    Raises ValueError on unrecognised characters.
    """
    tokens: list[tuple[str, str]] = []
    pos = 0
    while pos < len(text):
        m = _TOKEN_RE.match(text, pos)
        if not m:
            raise ValueError(
                f"Unrecognised character {text[pos]!r} at position {pos} "
                f"in dimension expression {text!r}"
            )
        kind = m.lastgroup
        assert kind is not None
        if kind != "ws":
            tokens.append((kind, m.group()))
        pos = m.end()
    return tokens


class _DimParser:
    """Recursive descent parser for dimension expressions.

    Grammar (left-recursive eliminated, precedence via nesting):
      expr   ::= factor (('*' | '/') factor)*
      factor ::= atom ('^' int)?
      atom   ::= '1' | identifier | '(' expr ')'
    """

    def __init__(self, tokens: list[tuple[str, str]]):
        self._tokens = tokens
        self._pos = 0

    def _peek(self) -> Optional[tuple[str, str]]:
        if self._pos < len(self._tokens):
            return self._tokens[self._pos]
        return None

    def _consume(self, kind: str) -> str:
        tok = self._peek()
        if tok is None or tok[0] != kind:
            expected = kind
            got = repr(tok) if tok else "end of input"
            raise ValueError(f"Expected {expected}, got {got}")
        self._pos += 1
        return tok[1]

    def parse_expr(self) -> DimVec:
        left = self._parse_factor()
        while True:
            tok = self._peek()
            if tok is None:
                break
            if tok[0] == "star":
                self._pos += 1
                right = self._parse_factor()
                left = left * right
            elif tok[0] == "slash":
                self._pos += 1
                right = self._parse_factor()
                left = left / right
            else:
                break
        return left

    def _parse_factor(self) -> DimVec:
        base = self._parse_atom()
        tok = self._peek()
        if tok and tok[0] == "caret":
            self._pos += 1
            exp_str = self._consume("int")
            exp = int(exp_str)
            return base ** exp
        return base

    def _parse_atom(self) -> DimVec:
        tok = self._peek()
        if tok is None:
            raise ValueError("Unexpected end of dimension expression")
        if tok[0] == "lparen":
            self._pos += 1
            inner = self.parse_expr()
            self._consume("rparen")
            return inner
        if tok[0] == "id":
            self._pos += 1
            name = tok[1]
            if name == "1":
                return DimVec.dimensionless()
            return DimVec.base(name)
        if tok[0] == "int":
            self._pos += 1
            val = int(tok[1])
            if val == 1:
                return DimVec.dimensionless()
            raise ValueError(
                f"Integer {val} is not a valid dimension atom "
                f"(only '1' is allowed as a dimensionless literal)"
            )
        raise ValueError(
            f"Unexpected token {tok!r} in dimension expression"
        )


def dim_parse(text: str) -> DimVec:
    """Parse a dimension expression string into a DimVec.

    Accepts:
      "USD"              -> [USD]
      "USD/person"       -> [USD/person]
      "GBP/USD"          -> [GBP/USD]       exchange rate
      "USD/person/year"  -> [USD/person/year]
      "m/s^2"            -> [m/s^2]
      "kg*m^2/s^2"       -> [kg*m^2/s^2]   Joules
      "1"                -> []              dimensionless
      "share/account"    -> [share/account]

    Raises ValueError on syntax errors.
    """
    text = text.strip()
    if not text:
        raise ValueError("Empty dimension expression")
    tokens = _tokenise(text)
    parser = _DimParser(tokens)
    result = parser.parse_expr()
    if parser._pos < len(tokens):
        remaining = tokens[parser._pos:]
        raise ValueError(
            f"Unexpected tokens at end of dimension expression: {remaining}"
        )
    return result


# ── Unit declarations ─────────────────────────────────────────────

@dataclass
class UnitDecl:
    """A declared dimension annotation for one variable."""
    var_name: str      # "revenue", "rate", "result", "result.field"
    dim: DimVec
    source_text: str   # original text e.g. "USD/person" for error messages


@dataclass
class ConversionDecl:
    """An explicit currency/unit conversion declared in the units: section.

    Example: "convert GBP to USD: rate" means the parameter named 'rate'
    has dimension [USD/GBP] and is used for explicit conversion.
    """
    from_dim: DimVec
    to_dim: DimVec
    via_param: str     # name of the rate parameter


@dataclass
class UnitsSection:
    """Parsed content of a units: section in a docstring contract."""
    declarations: list[UnitDecl] = field(default_factory=list)
    conversions: list[ConversionDecl] = field(default_factory=list)

    def dim_of(self, var_name: str) -> Optional[DimVec]:
        """Look up the declared dimension of a variable."""
        for d in self.declarations:
            if d.var_name == var_name:
                return d.dim
        return None

    def all_base_dims(self) -> set[str]:
        """All named base dimensions referenced in this section."""
        bases: set[str] = set()
        for d in self.declarations:
            bases.update(d.dim.components.keys())
        return bases


def parse_units_section(lines: list[str]) -> UnitsSection:
    """Parse the body of a units: section (one declaration per line).

    Accepted formats:
      variable_name: [dim_expr]   -- standard declaration
      result: [dim_expr]          -- return value
      result.field: [dim_expr]    -- field of structured return
      convert X to Y: param       -- explicit conversion via parameter

    Lines starting with # are comments and are ignored.
    """
    section = UnitsSection()

    convert_re = re.compile(
        r"convert\s+(\w+)\s+to\s+(\w+)\s*:\s*(\w+)", re.IGNORECASE
    )
    decl_re = re.compile(
        r"([\w.]+)\s*:\s*\[([^\]]+)\]"
    )

    for raw in lines:
        line = raw.strip()
        if not line or line.startswith("#"):
            continue

        # Conversion declaration
        m = convert_re.fullmatch(line)
        if m:
            from_dim = DimVec.base(m.group(1))
            to_dim   = DimVec.base(m.group(2))
            param    = m.group(3)
            section.conversions.append(
                ConversionDecl(from_dim=from_dim, to_dim=to_dim, via_param=param)
            )
            continue

        # Variable declaration
        m = decl_re.fullmatch(line)
        if m:
            var_name   = m.group(1)
            dim_text   = m.group(2).strip()
            try:
                dim = dim_parse(dim_text)
            except ValueError as e:
                raise ValueError(
                    f"Invalid dimension expression {dim_text!r} "
                    f"for {var_name!r}: {e}"
                ) from e
            section.declarations.append(
                UnitDecl(var_name=var_name, dim=dim, source_text=dim_text)
            )
            continue

        raise ValueError(
            f"Unrecognised units: line: {line!r}"
        )

    return section


# ── Dimension constraints ─────────────────────────────────────────

@dataclass
class DimConstraint:
    """A constraint that two expression dimensions must be equal.

    Generated at addition/subtraction nodes in the expression tree.
    All such constraints must hold for the function to be
    dimensionally consistent.
    """
    lhs_dim: DimVec
    rhs_dim: DimVec
    operation: str     # "+", "-", "==" (assignment compatibility check)
    line: int
    context: str       # human-readable description of the constraint origin


@dataclass
class DimViolation:
    """A confirmed dimension error."""
    line: int
    message: str
    lhs_dim: DimVec
    rhs_dim: DimVec
    context: str


@dataclass
class DimInference:
    """Result of dimensional inference on a function."""
    var_dims: dict[str, DimVec]          # variable -> inferred dimension
    constraints: list[DimConstraint]      # all generated constraints
    violations: list[DimViolation]        # confirmed errors (lhs != rhs)
    unknown_vars: set[str]               # variables with no dimension info

    @property
    def is_consistent(self) -> bool:
        return len(self.violations) == 0

    def format_report(self, func_name: str) -> str:
        """Format dimension violations as a human-readable report."""
        if self.is_consistent:
            return f"`{func_name}`: dimensionally consistent."
        lines = [f"## Dimension errors in `{func_name}`", ""]
        for v in self.violations:
            lines.append(f"- **Line {v.line}**: {v.message}")
            lines.append(f"  - Left:  `{v.lhs_dim}`")
            lines.append(f"  - Right: `{v.rhs_dim}`")
            if v.context:
                lines.append(f"  - In: `{v.context}`")
        return "\n".join(lines)


def check_constraints(constraints: list[DimConstraint]) -> list[DimViolation]:
    """Check all dimension constraints.

    DimVec equality is exact (frozenset comparison) -- no SMT needed.
    Returns a list of violations (empty if all constraints satisfied).
    """
    violations: list[DimViolation] = []
    for c in constraints:
        if not c.lhs_dim.compatible_with(c.rhs_dim):
            violations.append(DimViolation(
                line=c.line,
                message=(
                    f"Dimension mismatch in '{c.operation}': "
                    f"{c.lhs_dim} != {c.rhs_dim}"
                ),
                lhs_dim=c.lhs_dim,
                rhs_dim=c.rhs_dim,
                context=c.context,
            ))
    return violations
