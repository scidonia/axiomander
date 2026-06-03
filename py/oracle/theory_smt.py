"""
Theory-dispatched SMT oracle for Axiomander.

Outsources proof obligations that belong to specific decidable theories
to external SMT solvers (CVC4, Z3, CVC5), then either:
  - emits a Coq Axiom tagged with the query hash (UNSAT -> proved)
  - returns a typed TheoryCounterexample (SAT -> contract violation)
  - falls through to Level 3 (unknown)

Supported theories:
  STRING  -- QF_SLIA (strings + linear int arithmetic)
             str.++, str.len, str.contains, str.prefixof,
             str.suffixof, str.indexof, str.in_re, re.*
  FLOAT   -- QF_LRA (linear real arithmetic, models VFloat as Z/100)
  INT     -- QF_NIA (fallback, already handled by smt_export.py)
  MIXED   -- QF_SLIA (cross-theory: string length as integer etc.)

Design principles:
  - Each Theory defines its own Encoder (Coq term -> SMTLIB2 fragment).
  - Encoders are pluggable; adding a new theory = adding a new Encoder.
  - The SmtOracle runs any query and returns a structured result.
  - Counterexamples carry typed TheoryValues, not raw integers.
  - AxiomRecords carry the query hash for auditability and re-verification.
  - All Axioms are tagged with a comment block so the trust base is explicit.
"""

import hashlib
import re
import subprocess
import tempfile
import os
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Optional


# ── Theory definitions ────────────────────────────────────────────

class TheoryKind(Enum):
    STRING = "string"
    FLOAT  = "float"
    INT    = "int"
    MIXED  = "mixed"    # string + integer arithmetic


@dataclass(frozen=True)
class Theory:
    kind: TheoryKind
    smt_logic: str               # SMTLIB2 (set-logic ...) value
    solver_prefs: tuple[str, ...] # preferred solvers in order


STRING_THEORY = Theory(
    kind=TheoryKind.STRING,
    smt_logic="QF_SLIA",
    solver_prefs=("z3", "cvc5", "cvc4"),
)

FLOAT_THEORY = Theory(
    kind=TheoryKind.FLOAT,
    smt_logic="QF_LRA",
    solver_prefs=("z3", "cvc5", "cvc4"),
)

INT_THEORY = Theory(
    kind=TheoryKind.INT,
    smt_logic="QF_NIA",
    solver_prefs=("z3", "cvc5", "cvc4"),
)

MIXED_THEORY = Theory(
    kind=TheoryKind.MIXED,
    smt_logic="QF_SLIA",
    solver_prefs=("z3", "cvc5", "cvc4"),
)


# ── Typed SMT values ──────────────────────────────────────────────

@dataclass
class TheoryValue:
    """A typed value from an SMT model."""
    sort: str       # "String", "Int", "Real", "Bool"
    raw: str        # raw SMT model term: '"hello"', '42', '(/ 1 3)'
    python: str     # human-readable Python: '"hello"', '42', '0.33'

    @classmethod
    def from_smt_string(cls, raw: str) -> "TheoryValue":
        """Parse a String-sort value from SMT model output."""
        # SMT-LIB2: string values are double-quoted, "" escapes "
        inner = raw.strip()
        if inner.startswith('"') and inner.endswith('"'):
            inner = inner[1:-1].replace('""', '"')
        return cls(sort="String", raw=raw, python=repr(inner))

    @classmethod
    def from_smt_int(cls, raw: str) -> "TheoryValue":
        """Parse an Int-sort value from SMT model output."""
        # May be negative: (- 42) in some solvers
        raw = raw.strip()
        neg = re.match(r'^\(- (\d+)\)$', raw)
        if neg:
            v = -int(neg.group(1))
        else:
            try:
                v = int(raw)
            except ValueError:
                v = 0
        return cls(sort="Int", raw=raw, python=str(v))

    @classmethod
    def from_smt_real(cls, raw: str, float_scale: int = 100) -> "TheoryValue":
        """Parse a Real-sort value and unscale from VFloat encoding."""
        raw = raw.strip()
        # Rational: (/ p q)
        rat = re.match(r'^\(/ (-?\d+) (-?\d+)\)$', raw)
        if rat:
            p, q = int(rat.group(1)), int(rat.group(2))
            scaled = p / q
        else:
            try:
                scaled = float(raw)
            except ValueError:
                scaled = 0.0
        # Our VFloat stores float * float_scale as Z, so unscale
        python_val = scaled / float_scale
        return cls(sort="Real", raw=raw, python=f"{python_val:.4g}")


# ── SMT query fragment ────────────────────────────────────────────

@dataclass
class SmtDeclaration:
    name: str   # SMT variable name
    sort: str   # "String", "Int", "Real", "Bool"
    coq_var: str  # original Coq variable name (may differ after normalization)


@dataclass
class SmtFragment:
    """A self-contained SMTLIB2 query for one proof subgoal.

    Built by a TheoryEncoder from a Coq goal + hypothesis context.
    The SmtOracle runs it; the TheoryDispatcher decides what to do
    with the result.
    """
    theory: Theory
    declarations: list[SmtDeclaration]
    hypotheses: list[str]      # SMTLIB2 assertion strings (without assert wrapper)
    goal_negation: str         # negation of the goal, as SMTLIB2 string
    coq_prop: str              # the original Coq Prop (for the Axiom statement)
    coq_vars: list[str]        # Coq variable names in forall order (for Axiom)
    coq_sorts: dict[str, str]  # coq_var -> Coq sort ("string", "Z", etc.)

    def to_smt2(self) -> str:
        """Render as a complete SMTLIB2 file."""
        lines = [
            f"(set-logic {self.theory.smt_logic})",
            "(set-option :produce-models true)",
        ]
        for d in self.declarations:
            lines.append(f"(declare-const {d.name} {d.sort})")
        for h in self.hypotheses:
            lines.append(f"(assert {h})")
        lines.append(f"(assert (not {self.goal_negation}))")
        lines.append("(check-sat)")
        lines.append("(get-model)")
        return "\n".join(lines)

    def query_hash(self) -> str:
        """SHA256 of the SMTLIB2 query (first 16 hex chars)."""
        return hashlib.sha256(self.to_smt2().encode()).hexdigest()[:16]


# ── SMT result types ──────────────────────────────────────────────

@dataclass
class AxiomRecord:
    """A Coq Axiom backed by SMT evidence (UNSAT result).

    The axiom name encodes both the theory and query hash, making it
    globally unique and traceable.
    """
    axiom_name: str         # e.g. "smt_string_a3f9b2c1deadbeef"
    coq_statement: str      # the full Axiom declaration (with forall)
    query_hash: str         # hex digest for re-verification
    theory: TheoryKind
    solver: str             # which solver produced this
    solver_version: str     # solver --version output
    fragment: SmtFragment   # the original query (for re-verification)

    def to_coq(self) -> str:
        """Emit as a Coq Axiom with attribution comment."""
        return (
            f"(* SMT-verified: {self.theory.value} theory, "
            f"{self.solver} {self.solver_version}, "
            f"query {self.query_hash} *)\n"
            f"Axiom {self.axiom_name} : {self.coq_statement}."
        )


@dataclass
class TheoryCounterexample:
    """A concrete counterexample from an SMT SAT result.

    Carries typed values (not just integers), the violated proposition,
    and enough context to generate a useful error message.
    """
    theory: TheoryKind
    assignments: dict[str, TheoryValue]   # var_name -> typed value
    violated_prop: str                     # Coq Prop that was falsified
    query_hash: str
    solver: str
    raw_model: str  # raw SMT model output for debugging

    def format_report(self) -> str:
        """Format as a human-readable counterexample block."""
        lines = [
            f"Contract violation ({self.theory.value} theory):",
            "",
        ]
        for var, val in self.assignments.items():
            lines.append(f"  {var} = {val.python}  ({val.sort})")
        lines.append("")
        lines.append(f"  Violated: {self.violated_prop}")
        lines.append("")

        # Theory-specific guidance
        if self.theory == TheoryKind.STRING:
            lines.append(
                "  Hint: The postcondition references a string property that\n"
                "  does not hold for these inputs. Check whether the contract\n"
                "  is correct or whether the function body establishes it."
            )
        elif self.theory == TheoryKind.FLOAT:
            lines.append(
                "  Hint: The postcondition references a float property.\n"
                "  VFloat values are stored as Z * 100 (2 decimal places).\n"
                "  Check rounding assumptions in the contract."
            )
        return "\n".join(lines)


@dataclass
class TheoryOracleResult:
    """Outcome of running the theory SMT oracle on a set of goal fragments."""
    proved: list[AxiomRecord] = field(default_factory=list)
    counterexamples: list[TheoryCounterexample] = field(default_factory=list)
    unknown: list[SmtFragment] = field(default_factory=list)  # fall through

    @property
    def all_proved(self) -> bool:
        return bool(self.proved) and not self.counterexamples and not self.unknown

    @property
    def has_counterexample(self) -> bool:
        return bool(self.counterexamples)

    def coq_axiom_block(self) -> str:
        """All proved axioms as a Coq block for injection into the proof."""
        if not self.proved:
            return ""
        lines = ["(* Theory-SMT axioms — verified by external oracle *)"]
        for ax in self.proved:
            lines.append(ax.to_coq())
        return "\n".join(lines)

    def proof_apply_block(self) -> str:
        """Tactic script applying all axioms, one per proved goal."""
        if not self.proved:
            return ""
        applies = "\n".join(
            f"  try (exact {ax.axiom_name})." for ax in self.proved
        )
        return f"  intros; wp_reduce; repeat split;\n{applies}\n  try lia."


# ── Theory classifier ─────────────────────────────────────────────

# Coq terms that signal string theory involvement
_STRING_SIGNALS = frozenset([
    "String.eqb", "String.append", "String.length", "String.index",
    "String.prefix", "String.substring", "String.concat",
    "asString", "VString", "isVString",
    "smem_f",       # our string-keyed set field
])

# Coq terms that signal float theory involvement
_FLOAT_SIGNALS = frozenset([
    "asFloat", "VFloat", "isVFloat", "float_scale",
])


def classify_goal(goal_text: str) -> Optional[Theory]:
    """Classify a Coq goal text into a Theory, or None if not applicable.

    Returns None for pure integer arithmetic (already handled by
    smt_export.py / _smt_prove_goal).
    """
    has_string = any(sig in goal_text for sig in _STRING_SIGNALS)
    has_float  = any(sig in goal_text for sig in _FLOAT_SIGNALS)

    if has_string and has_float:
        return MIXED_THEORY   # treat as string+LIA; float as Int/100
    if has_string:
        return STRING_THEORY
    if has_float:
        return FLOAT_THEORY
    return None               # pure integer — handled upstream


# ── SMT variable normalization ────────────────────────────────────

def _normalize_var(name: str) -> str:
    """Normalize a Coq variable name to a safe SMTLIB2 identifier."""
    # Replace characters that SMTLIB2 identifiers cannot contain
    return re.sub(r'[^a-zA-Z0-9_]', '_', name)


def _smt_string_var(coq_name: str) -> str:
    return _normalize_var(coq_name)


# ── String theory encoder ─────────────────────────────────────────

class StringTheoryEncoder:
    """Encode a Coq string/mixed goal as a QF_SLIA SMTLIB2 fragment.

    Recognizes the following Coq patterns:
      String.append s1 s2 = s3         -> (= (str.++ s1 s2) s3)
      String.length s = n              -> (= (str.len s) n)
      String.eqb s1 s2 = true/false    -> (= s1 s2) / (not (= s1 s2))
      String.index 0 s1 s2 <> None     -> (str.contains s2 s1)
      String.index 0 s1 s2 = None      -> (not (str.contains s2 s1))
      String.prefix s1 s2 = true       -> (str.prefixof s1 s2)
      asString (s "x") = "lit"         -> direct string equality
      VString s1 = VString s2          -> (= s1 s2)
    """

    def encode(
        self,
        goal_text: str,
        hyp_texts: list[str],
        param_types: dict[str, str],
    ) -> Optional[SmtFragment]:
        """Encode goal + hypotheses as a QF_SLIA fragment.

        Returns None if the goal cannot be encoded (falls through to LLM).
        """
        # Extract all string and integer variables from goal + hyps
        all_text = " ".join([goal_text] + hyp_texts)
        decls, coq_sorts = self._extract_declarations(all_text, param_types)

        if not decls:
            return None

        # Encode each hypothesis
        encoded_hyps = []
        for h in hyp_texts:
            enc = self._encode_expr(h, coq_sorts)
            if enc:
                encoded_hyps.append(enc)

        # Encode the goal negation
        goal_enc = self._encode_expr(goal_text, coq_sorts)
        if not goal_enc:
            return None

        # Build Coq Prop for the Axiom (universally quantified)
        coq_vars = [d.coq_var for d in decls]
        coq_sorts_for_prop = {
            d.coq_var: ("string" if d.sort == "String" else "Z")
            for d in decls
        }
        prop = self._build_coq_prop(goal_text, coq_vars, coq_sorts_for_prop)

        return SmtFragment(
            theory=STRING_THEORY,
            declarations=decls,
            hypotheses=encoded_hyps,
            goal_negation=goal_enc,
            coq_prop=prop,
            coq_vars=coq_vars,
            coq_sorts=coq_sorts_for_prop,
        )

    def _extract_declarations(
        self,
        text: str,
        param_types: dict[str, str],
    ) -> tuple[list[SmtDeclaration], dict[str, str]]:
        """Identify variables and assign SMT sorts."""
        decls: list[SmtDeclaration] = []
        coq_sorts: dict[str, str] = {}

        # Find all identifiers that look like state variable reads:
        # asString (s "x"), asZ (s "x"), s "x"
        for m in re.finditer(r'asString\s*\(\s*s\s*"([^"]+)"\s*\)', text):
            vname = m.group(1)
            if vname not in coq_sorts:
                coq_sorts[vname] = "String"
                decls.append(SmtDeclaration(
                    name=_smt_string_var(vname),
                    sort="String",
                    coq_var=vname,
                ))

        for m in re.finditer(r'asZ\s*\(\s*s\s*"([^"]+)"\s*\)', text):
            vname = m.group(1)
            if vname not in coq_sorts:
                coq_sorts[vname] = "Int"
                decls.append(SmtDeclaration(
                    name=_smt_string_var(vname),
                    sort="Int",
                    coq_var=vname,
                ))

        # Also match bare forall params from param_types
        for vname, vtype in param_types.items():
            if vname in coq_sorts:
                continue
            if vtype in ("str", "string"):
                coq_sorts[vname] = "String"
                decls.append(SmtDeclaration(
                    name=_smt_string_var(vname),
                    sort="String",
                    coq_var=vname,
                ))
            elif vtype in ("int", "Z", "nat"):
                coq_sorts[vname] = "Int"
                decls.append(SmtDeclaration(
                    name=_smt_string_var(vname),
                    sort="Int",
                    coq_var=vname,
                ))

        return decls, coq_sorts

    def _encode_expr(
        self,
        expr: str,
        coq_sorts: dict[str, str],
    ) -> Optional[str]:
        """Encode a single Coq expression as SMTLIB2. Returns None if unsupported."""
        expr = expr.strip()

        # String.append s1 s2 = s3  ->  (= (str.++ ...) ...)
        m = re.match(
            r'String\.append\s+(.+?)\s+(.+?)\s*=\s*(.+)$', expr)
        if m:
            s1 = self._coq_string_to_smt(m.group(1), coq_sorts)
            s2 = self._coq_string_to_smt(m.group(2), coq_sorts)
            s3 = self._coq_string_to_smt(m.group(3), coq_sorts)
            return f"(= (str.++ {s1} {s2}) {s3})"

        # s1 ++ s2 = s3  (Coq notation for String.append)
        m = re.search(r'^(.+?)\s*\+\+\s*(.+?)\s*=\s*(.+)$', expr)
        if m:
            s1 = self._coq_string_to_smt(m.group(1), coq_sorts)
            s2 = self._coq_string_to_smt(m.group(2), coq_sorts)
            s3 = self._coq_string_to_smt(m.group(3), coq_sorts)
            return f"(= (str.++ {s1} {s2}) {s3})"

        # String.length s = n  ->  (= (str.len s) n)
        m = re.match(r'String\.length\s+(.+?)\s*=\s*(.+)$', expr)
        if m:
            s = self._coq_string_to_smt(m.group(1), coq_sorts)
            n = self._coq_int_to_smt(m.group(2), coq_sorts)
            return f"(= (str.len {s}) {n})"

        # String.eqb s1 s2 = true/false
        m = re.match(r'String\.eqb\s+(.+?)\s+(.+?)\s*=\s*(true|false)$', expr)
        if m:
            s1 = self._coq_string_to_smt(m.group(1), coq_sorts)
            s2 = self._coq_string_to_smt(m.group(2), coq_sorts)
            eq = f"(= {s1} {s2})"
            return eq if m.group(3) == "true" else f"(not {eq})"

        # String.index 0 s1 s2 <> None  ->  (str.contains s2 s1)
        m = re.match(
            r'String\.index\s+0\s+(.+?)\s+(.+?)\s*<>\s*None$', expr)
        if m:
            s1 = self._coq_string_to_smt(m.group(1), coq_sorts)
            s2 = self._coq_string_to_smt(m.group(2), coq_sorts)
            return f"(str.contains {s2} {s1})"

        # String.index 0 s1 s2 = None  ->  (not (str.contains s2 s1))
        m = re.match(
            r'String\.index\s+0\s+(.+?)\s+(.+?)\s*=\s*None$', expr)
        if m:
            s1 = self._coq_string_to_smt(m.group(1), coq_sorts)
            s2 = self._coq_string_to_smt(m.group(2), coq_sorts)
            return f"(not (str.contains {s2} {s1}))"

        # String.prefix s1 s2 = true  ->  (str.prefixof s1 s2)
        m = re.match(
            r'String\.prefix\s+(.+?)\s+(.+?)\s*=\s*(true|false)$', expr)
        if m:
            s1 = self._coq_string_to_smt(m.group(1), coq_sorts)
            s2 = self._coq_string_to_smt(m.group(2), coq_sorts)
            pref = f"(str.prefixof {s1} {s2})"
            return pref if m.group(3) == "true" else f"(not {pref})"

        # VString s1 = VString s2
        m = re.match(r'VString\s+(.+?)\s*=\s*VString\s+(.+)$', expr)
        if m:
            s1 = self._coq_string_to_smt(m.group(1), coq_sorts)
            s2 = self._coq_string_to_smt(m.group(2), coq_sorts)
            return f"(= {s1} {s2})"

        # General string equality: s1 = s2 where either side may be ++, asString, literal
        # Try splitting on = and encoding both sides as strings
        eq_pos = expr.find(" = ")
        if eq_pos > 0:
            lhs = expr[:eq_pos].strip()
            rhs = expr[eq_pos + 3:].strip()
            # Check if at least one side is string-typed (contains ++ or asString or known string var)
            def _looks_like_string(s: str) -> bool:
                return ("++" in s or "asString" in s or "VString" in s
                        or any(s.strip().startswith(f'"{c}') for c in "abcdefghijklmnopqrstuvwxyz(")
                        or s.strip() in coq_sorts and coq_sorts[s.strip()] == "String")
            if _looks_like_string(lhs) or _looks_like_string(rhs):
                s1 = self._coq_string_to_smt(lhs, coq_sorts)
                s2 = self._coq_string_to_smt(rhs, coq_sorts)
                return f"(= {s1} {s2})"

        # Logical connectives: A /\ B, A \/ B, ~ A
        m = re.match(r'^(.+)\s*/\\\\\s*(.+)$', expr, re.DOTALL)
        if m:
            a = self._encode_expr(m.group(1), coq_sorts)
            b = self._encode_expr(m.group(2), coq_sorts)
            if a and b:
                return f"(and {a} {b})"

        m = re.match(r'^(.+)\s*\\\\/\s*(.+)$', expr, re.DOTALL)
        if m:
            a = self._encode_expr(m.group(1), coq_sorts)
            b = self._encode_expr(m.group(2), coq_sorts)
            if a and b:
                return f"(or {a} {b})"

        m = re.match(r'^~\s*(.+)$', expr)
        if m:
            a = self._encode_expr(m.group(1), coq_sorts)
            if a:
                return f"(not {a})"

        return None   # unsupported pattern -- caller will fall through

    def _coq_string_to_smt(self, s: str, coq_sorts: dict[str, str]) -> str:
        """Convert a Coq string expression to SMTLIB2."""
        s = s.strip()
        # asString (s "x")  ->  x (the declared SMT variable)
        m = re.match(r'asString\s*\(\s*s\s*"([^"]+)"\s*\)', s)
        if m:
            return _smt_string_var(m.group(1))
        # String literal: "hello"%string  ->  "hello"
        m = re.match(r'"([^"]*)"%string$', s)
        if m:
            return f'"{m.group(1)}"'
        # Bare string literal
        m = re.match(r'^"([^"]*)"$', s)
        if m:
            return s
        # Bare variable name that we know is a string
        if s in coq_sorts and coq_sorts[s] == "String":
            return _smt_string_var(s)
        # String.append / ++ -- recurse
        m = re.match(r'^(.+?)\s*\+\+\s*(.+)$', s)
        if m:
            a = self._coq_string_to_smt(m.group(1), coq_sorts)
            b = self._coq_string_to_smt(m.group(2), coq_sorts)
            return f"(str.++ {a} {b})"
        # Fallback: emit as-is (solver will reject if wrong)
        return _smt_string_var(s)

    def _coq_int_to_smt(self, n: str, coq_sorts: dict[str, str]) -> str:
        """Convert a Coq integer expression to SMTLIB2."""
        n = n.strip()
        # asZ (s "x")  ->  x
        m = re.match(r'asZ\s*\(\s*s\s*"([^"]+)"\s*\)', n)
        if m:
            return _smt_string_var(m.group(1))
        # String.length s  ->  (str.len s)
        m = re.match(r'String\.length\s+(.+)$', n)
        if m:
            s = self._coq_string_to_smt(m.group(1), coq_sorts)
            return f"(str.len {s})"
        # Integer literal
        m = re.match(r'^-?\d+$', n)
        if m:
            return n
        # Arithmetic: n1 + n2, n1 - n2, etc.
        for coq_op, smt_op in [('+', '+'), ('-', '-'), ('*', '*')]:
            idx = n.rfind(coq_op)
            if idx > 0:
                left  = n[:idx].strip()
                right = n[idx+1:].strip()
                if left and right:
                    return f"({smt_op} {self._coq_int_to_smt(left, coq_sorts)} {self._coq_int_to_smt(right, coq_sorts)})"
        # Bare variable
        if n in coq_sorts:
            return _smt_string_var(n)
        return n

    def _build_coq_prop(
        self,
        goal_text: str,
        coq_vars: list[str],
        coq_sorts: dict[str, str],
    ) -> str:
        """Build the universally quantified Coq Prop for the Axiom."""
        if not coq_vars:
            return goal_text
        binders = " ".join(
            f"({v} : {coq_sorts.get(v, 'Z')})"
            for v in coq_vars
        )
        return f"forall {binders}, {goal_text}"


# ── Float theory encoder ──────────────────────────────────────────

class FloatTheoryEncoder:
    """Encode VFloat goals as QF_LRA (linear real arithmetic).

    VFloat in IMP is stored as Z * 100 (2 decimal places).
    We declare floats as Real and assert the /100 relationship.
    """

    FLOAT_SCALE = 100

    def encode(
        self,
        goal_text: str,
        hyp_texts: list[str],
        param_types: dict[str, str],
    ) -> Optional[SmtFragment]:
        decls, coq_sorts = self._extract_declarations(
            " ".join([goal_text] + hyp_texts), param_types
        )
        if not decls:
            return None

        encoded_hyps = []
        for h in hyp_texts:
            enc = self._encode_expr(h, coq_sorts)
            if enc:
                encoded_hyps.append(enc)

        goal_enc = self._encode_expr(goal_text, coq_sorts)
        if not goal_enc:
            return None

        coq_vars = [d.coq_var for d in decls]
        coq_sorts_prop = {
            d.coq_var: ("Z" if d.sort == "Int" else "Z")
            for d in decls
        }
        prop = f"forall {' '.join(f'({v} : Z)' for v in coq_vars)}, {goal_text}"

        return SmtFragment(
            theory=FLOAT_THEORY,
            declarations=decls,
            hypotheses=encoded_hyps,
            goal_negation=goal_enc,
            coq_prop=prop,
            coq_vars=coq_vars,
            coq_sorts=coq_sorts_prop,
        )

    def _extract_declarations(
        self,
        text: str,
        param_types: dict[str, str],
    ) -> tuple[list[SmtDeclaration], dict[str, str]]:
        decls: list[SmtDeclaration] = []
        coq_sorts: dict[str, str] = {}

        # asFloat (s "x") or VFloat patterns
        for m in re.finditer(r'asFloat\s*\(\s*s\s*"([^"]+)"\s*\)', text):
            vname = m.group(1)
            if vname not in coq_sorts:
                coq_sorts[vname] = "Real"
                decls.append(SmtDeclaration(
                    name=_normalize_var(vname),
                    sort="Real",
                    coq_var=vname,
                ))

        # Integers that appear alongside floats
        for m in re.finditer(r'asZ\s*\(\s*s\s*"([^"]+)"\s*\)', text):
            vname = m.group(1)
            if vname not in coq_sorts:
                coq_sorts[vname] = "Int"
                decls.append(SmtDeclaration(
                    name=_normalize_var(vname),
                    sort="Int",
                    coq_var=vname,
                ))

        return decls, coq_sorts

    def _encode_expr(
        self,
        expr: str,
        coq_sorts: dict[str, str],
    ) -> Optional[str]:
        expr = expr.strip()

        # asFloat (s "x") op asFloat (s "y")  for basic comparisons
        m = re.match(
            r'asFloat\s*\(\s*s\s*"([^"]+)"\s*\)\s*([<>=!]+)\s*asFloat\s*\(\s*s\s*"([^"]+)"\s*\)',
            expr,
        )
        if m:
            v1 = _normalize_var(m.group(1))
            op = {"<=": "<=", ">=": ">=", "<": "<", ">": ">", "=": "="}.get(
                m.group(2), "="
            )
            v2 = _normalize_var(m.group(3))
            return f"({op} {v1} {v2})"

        # VFloat z = asFloat (s "x") * 100  ->  (= (/ x 100) z)
        # (simplified: treat z as scaled integer)
        m = re.match(
            r'asFloat\s*\(\s*s\s*"([^"]+)"\s*\)\s*=\s*(-?\d+)$', expr
        )
        if m:
            v = _normalize_var(m.group(1))
            n = int(m.group(2))
            real_val = n / self.FLOAT_SCALE
            return f"(= {v} {real_val})"

        return None


# ── SMT Oracle ────────────────────────────────────────────────────

_SOLVER_CACHE: dict[str, Optional[str]] = {}  # solver -> version or None


def _find_solver(prefs: tuple[str, ...]) -> Optional[tuple[str, str]]:
    """Find the first available solver from prefs. Returns (name, version)."""
    for solver in prefs:
        if solver not in _SOLVER_CACHE:
            try:
                r = subprocess.run(
                    [solver, "--version"],
                    capture_output=True, text=True, timeout=5,
                )
                ver = r.stdout.strip().split("\n")[0][:40] if r.returncode == 0 else ""
                _SOLVER_CACHE[solver] = ver if ver else None
            except (FileNotFoundError, subprocess.TimeoutExpired):
                _SOLVER_CACHE[solver] = None
        ver = _SOLVER_CACHE[solver]
        if ver is not None:
            return solver, ver
    return None


def _run_fragment(
    fragment: SmtFragment,
    timeout: int = 15,
) -> tuple[str, str, str]:
    """Run the SMT query. Returns (status, raw_output, solver_name).

    status is one of: "unsat", "sat", "unknown", "error"
    """
    solver_info = _find_solver(fragment.theory.solver_prefs)
    if not solver_info:
        return "error", "No solver available", ""
    solver, _ver = solver_info

    smt2 = fragment.to_smt2()
    tmp_path = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".smt2", delete=False,
            prefix=f"theory_{fragment.theory.kind.value}_",
        ) as f:
            f.write(smt2)
            tmp_path = f.name

        result = subprocess.run(
            [solver, tmp_path],
            capture_output=True, text=True, timeout=timeout,
        )
        output = result.stdout + result.stderr
        first_line = output.strip().split("\n")[0].strip() if output.strip() else ""
        if first_line == "unsat":
            return "unsat", output, solver
        elif first_line == "sat":
            return "sat", output, solver
        else:
            return "unknown", output, solver

    except subprocess.TimeoutExpired:
        return "unknown", f"{solver} timed out after {timeout}s", solver
    except FileNotFoundError:
        return "error", f"Solver '{solver}' not found", solver
    finally:
        if tmp_path:
            try:
                os.unlink(tmp_path)
            except OSError:
                pass


def _parse_model(
    raw_output: str,
    declarations: list[SmtDeclaration],
) -> dict[str, TheoryValue]:
    """Parse an SMT model into typed TheoryValues.

    Handles both Z3 and CVC4/CVC5 model formats:
      Z3:   (define-fun x () String "hello")
      CVC4: (define-fun x () String "hello")
    """
    values: dict[str, TheoryValue] = {}
    decl_map = {d.name: d for d in declarations}

    # Match: (define-fun <name> () <sort> <value>)
    # Value may span multiple tokens: (/ 1 3), (- 42), "multi word", etc.
    pattern = re.compile(
        r'\(define-fun\s+(\S+)\s+\(\)\s+(\S+)\s+((?:[^()"\n]+|"(?:[^"\\]|\\.)*"|\([^)]*\))+)\)',
        re.MULTILINE,
    )

    for m in pattern.finditer(raw_output):
        name  = m.group(1)
        sort  = m.group(2)
        value = m.group(3).strip()

        if name not in decl_map:
            continue

        d = decl_map[name]
        if sort == "String" or d.sort == "String":
            values[d.coq_var] = TheoryValue.from_smt_string(value)
        elif sort == "Real" or d.sort == "Real":
            values[d.coq_var] = TheoryValue.from_smt_real(value)
        else:
            values[d.coq_var] = TheoryValue.from_smt_int(value)

    return values


# ── Theory Dispatcher ─────────────────────────────────────────────

class TheoryDispatcher:
    """Orchestrate goal classification, encoding, SMT execution, and result assembly.

    Usage:
        dispatcher = TheoryDispatcher(param_types={"name": "str", "n": "int"})
        result = dispatcher.dispatch(goal_texts, hyp_texts)

        if result.has_counterexample:
            # contract is wrong, surface the counterexample
            ...
        elif result.all_proved:
            # inject axioms and apply them
            coq_source = inject_axioms(coq_source, result)
    """

    # Registry: TheoryKind -> Encoder class
    _ENCODERS: dict[TheoryKind, type] = {
        TheoryKind.STRING: StringTheoryEncoder,
        TheoryKind.FLOAT:  FloatTheoryEncoder,
        TheoryKind.MIXED:  StringTheoryEncoder,  # mixed uses string encoder (QF_SLIA)
    }

    def __init__(
        self,
        param_types: Optional[dict[str, str]] = None,
        timeout: int = 15,
    ):
        self.param_types = param_types or {}
        self.timeout = timeout

    def dispatch(
        self,
        goal_texts: list[str],
        hyp_texts: Optional[list[str]] = None,
    ) -> TheoryOracleResult:
        """Classify and dispatch each goal to the appropriate theory encoder."""
        hyp_texts = hyp_texts or []
        result = TheoryOracleResult()

        for goal in goal_texts:
            theory = classify_goal(goal)
            if theory is None:
                # Pure integer -- not our responsibility
                continue

            encoder_cls = self._ENCODERS.get(theory.kind)
            if encoder_cls is None:
                result.unknown.append(
                    SmtFragment(
                        theory=theory,
                        declarations=[],
                        hypotheses=[],
                        goal_negation=goal,
                        coq_prop=goal,
                        coq_vars=[],
                        coq_sorts={},
                    )
                )
                continue

            encoder = encoder_cls()
            fragment = encoder.encode(goal, hyp_texts, self.param_types)

            if fragment is None:
                # Encoding failed -- fall through to LLM
                result.unknown.append(
                    SmtFragment(
                        theory=theory,
                        declarations=[],
                        hypotheses=[],
                        goal_negation=goal,
                        coq_prop=goal,
                        coq_vars=[],
                        coq_sorts={},
                    )
                )
                continue

            status, raw_output, solver = _run_fragment(fragment, self.timeout)

            if status == "unsat":
                solver_ver = _SOLVER_CACHE.get(solver, "") or ""
                axiom_name = f"smt_{theory.kind.value}_{fragment.query_hash()}"
                axiom = AxiomRecord(
                    axiom_name=axiom_name,
                    coq_statement=fragment.coq_prop,
                    query_hash=fragment.query_hash(),
                    theory=theory.kind,
                    solver=solver,
                    solver_version=solver_ver,
                    fragment=fragment,
                )
                result.proved.append(axiom)

            elif status == "sat":
                # Parse the counterexample model
                model = _parse_model(raw_output, fragment.declarations)
                ce = TheoryCounterexample(
                    theory=theory.kind,
                    assignments=model,
                    violated_prop=fragment.coq_prop,
                    query_hash=fragment.query_hash(),
                    solver=solver,
                    raw_model=raw_output,
                )
                result.counterexamples.append(ce)

            else:
                # unknown or error -- fall through
                result.unknown.append(fragment)

        return result


# ── Coq source injection ──────────────────────────────────────────

def inject_theory_axioms(
    coq_source: str,
    oracle_result: TheoryOracleResult,
    func_name: str,
) -> str:
    """Inject theory axioms into the Coq proof source.

    Replaces the Proof...Qed block with:
      Proof.
        [axiom declarations]
        intros; wp_reduce; repeat split;
        try (exact smt_string_<hash>).
        ...
        try lia.
      Qed.
    """
    if not oracle_result.proved:
        return coq_source

    axiom_block = oracle_result.coq_axiom_block()
    apply_block = oracle_result.proof_apply_block()

    new_proof = (
        f"Proof.\n"
        f"{axiom_block}\n"
        f"{apply_block}\n"
        f"Qed."
    )

    # Replace the existing Proof...Qed block
    coq_source = re.sub(
        r'Proof\.\n.*?Qed\.',
        new_proof,
        coq_source,
        count=1,
        flags=re.DOTALL,
    )
    return coq_source


def format_counterexample_report(
    oracle_result: TheoryOracleResult,
    func_name: str,
) -> str:
    """Format all counterexamples as a human-readable report."""
    if not oracle_result.has_counterexample:
        return ""
    lines = [f"## Theory SMT counterexample(s) for `{func_name}`", ""]
    for ce in oracle_result.counterexamples:
        lines.append(ce.format_report())
    return "\n".join(lines)
