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


# ── Python regex to SMTLIB2 RegLan translator ─────────────────────
#
# Uses Python's own sre_parse module to obtain a typed AST for the
# pattern, then walks that AST to emit SMTLIB2 RegLan expressions.
# This means we never hand-parse regex syntax -- we delegate that
# entirely to the stdlib and only handle the semantic mapping.
#
# sre_parse AST nodes are (opcode, data) pairs where opcode is one of
# the constants in the sre_constants module.  A SubPattern is a list
# of such pairs.
#
# Supported opcodes -> SMTLIB2:
#   LITERAL c           -> (str.to_re "c")
#   NOT_LITERAL c       -> (re.comp (str.to_re "c"))
#   ANY                 -> re.allchar
#   IN [items]          -> re.union / re.range / re.comp
#   BRANCH [alts]       -> re.union
#   SUBPATTERN (n,a,b,p)-> recurse into p (groups are transparent)
#   MAX_REPEAT (lo,hi,p)-> re.* / re.+ / re.opt / (_ re.^ n) / (_ re.loop n m)
#   AT (AT_BEGINNING/END)-> epsilon (anchors implicit in str.in_re)
#   CATEGORY WORD/DIGIT/SPACE -> named character classes
#
# Unsupported: GROUPREF, ASSERT (lookahead), AT_WORD_BOUNDARY, etc.
# Returns None on unsupported features or parse errors.

import re as _re_module
import warnings as _warnings
with _warnings.catch_warnings():
    _warnings.simplefilter("ignore", DeprecationWarning)
    import sre_parse as _sre_parse
    import sre_constants as _sre_const


def _python_re_to_smt(pattern: str) -> Optional[str]:
    """Translate a Python regex pattern to a SMTLIB2 RegLan term.

    Uses sre_parse for the AST -- no hand-written regex parsing.
    Returns None if the pattern uses unsupported features.
    """
    try:
        # sre_parse.parse returns a SubPattern (list of (op, av) pairs)
        parsed = _sre_parse.parse(pattern)
        return _sre_subpattern_to_smt(parsed)
    except Exception:
        return None


def _sre_subpattern_to_smt(nodes: "_sre_parse.SubPattern | list") -> Optional[str]:
    """Translate a sre_parse SubPattern (sequence of nodes) to SMTLIB2.

    A sequence is a concatenation; emit re.++ over each node.
    Empty sequence = epsilon = (str.to_re "").
    """
    parts = []
    for op, av in nodes:
        part = _sre_node_to_smt(op, av)
        if part is None:
            return None   # unsupported feature -- propagate failure
        parts.append(part)
    return _smt_concat(parts)


def _smt_concat(parts: list[str]) -> str:
    """Build a SMTLIB2 re.++ chain from a list of RegLan expressions."""
    if not parts:
        return '(str.to_re "")'   # epsilon
    if len(parts) == 1:
        return parts[0]
    result = parts[0]
    for p in parts[1:]:
        result = f"(re.++ {result} {p})"
    return result


def _smt_union(parts: list[str]) -> str:
    """Build a SMTLIB2 re.union chain from a list of RegLan expressions."""
    if not parts:
        return "re.none"
    if len(parts) == 1:
        return parts[0]
    result = parts[0]
    for p in parts[1:]:
        result = f"(re.union {result} {p})"
    return result


def _smt_literal(code_point: int) -> str:
    """Emit a single-character RegLan from a Unicode code point."""
    c = chr(code_point)
    # SMTLIB2 strings use "" to escape a literal double-quote inside a string.
    if c == '"':
        return '(str.to_re "\\"\\"")'
    if c == '\\':
        return '(str.to_re "\\\\")'
    return f'(str.to_re "{c}")'


def _sre_node_to_smt(op, av) -> Optional[str]:
    """Translate one sre_parse (op, av) node to a SMTLIB2 RegLan term."""

    if op is _sre_const.LITERAL:
        # av = Unicode code point
        return _smt_literal(av)

    if op is _sre_const.NOT_LITERAL:
        return f"(re.comp {_smt_literal(av)})"

    if op is _sre_const.ANY:
        # . matches any character (re.allchar is all single-char strings)
        return "re.allchar"

    if op is _sre_const.AT:
        # ^ / $ anchors -- implicit in str.in_re; emit epsilon
        return '(str.to_re "")'

    if op is _sre_const.SUBPATTERN:
        # av = (group_id, add_flags, del_flags, pattern)
        # Groups are transparent for our purposes -- just recurse.
        _, _, _, subpat = av
        return _sre_subpattern_to_smt(subpat)

    if op is _sre_const.BRANCH:
        # av = (None, [alt1, alt2, ...]) where each alt is a SubPattern
        _, alts = av
        parts = [_sre_subpattern_to_smt(a) for a in alts]
        if any(p is None for p in parts):
            return None
        return _smt_union(parts)  # type: ignore[arg-type]

    if op is _sre_const.IN:
        # av = list of items inside [...].
        # First item may be NEGATE.
        items = list(av)
        negate = False
        if items and items[0][0] is _sre_const.NEGATE:
            negate = True
            items = items[1:]
        parts = []
        for item_op, item_av in items:
            part = _sre_class_item_to_smt(item_op, item_av)
            if part is None:
                return None
            parts.append(part)
        union = _smt_union(parts)
        return f"(re.comp {union})" if negate else union

    if op is _sre_const.MAX_REPEAT:
        lo, hi, subpat = av
        inner = _sre_subpattern_to_smt(subpat)
        if inner is None:
            return None
        # MAXREPEAT sentinel means unbounded
        if lo == 0 and hi is _sre_const.MAXREPEAT:
            return f"(re.* {inner})"
        if lo == 1 and hi is _sre_const.MAXREPEAT:
            return f"(re.+ {inner})"
        if lo == 0 and hi == 1:
            return f"(re.opt {inner})"
        if lo == hi:
            # Exact repetition: (_ re.^ n)
            return f"((_ re.^ {lo}) {inner})"
        if hi is _sre_const.MAXREPEAT:
            # {lo,} -- at least lo repetitions
            return f"(re.++ ((_ re.^ {lo}) {inner}) (re.* {inner}))"
        # {lo,hi} range
        return f"((_ re.loop {lo} {hi}) {inner})"

    if op is _sre_const.MIN_REPEAT:
        # Lazy quantifiers (* ? +) -- semantically same as greedy for str.in_re
        lo, hi, subpat = av
        return _sre_node_to_smt(_sre_const.MAX_REPEAT, (lo, hi, subpat))

    if op is _sre_const.CATEGORY:
        # \d \w \s and their complements
        return _sre_category_to_smt(av)

    # Unsupported: GROUPREF, ASSERT (lookahead/lookbehind), etc.
    return None


def _sre_class_item_to_smt(op, av) -> Optional[str]:
    """Translate one item inside [...] to a SMTLIB2 RegLan term."""
    if op is _sre_const.LITERAL:
        return _smt_literal(av)
    if op is _sre_const.RANGE:
        lo, hi = av
        return f'(re.range "{chr(lo)}" "{chr(hi)}")'
    if op is _sre_const.CATEGORY:
        return _sre_category_to_smt(av)
    if op is _sre_const.NEGATE:
        return None   # handled by caller
    return None


def _sre_category_to_smt(category) -> Optional[str]:
    """Translate a sre CATEGORY (\\d, \\w, \\s, \\D, \\W, \\S) to SMTLIB2."""
    _DIGITS    = '(re.range "0" "9")'
    _LOWER     = '(re.range "a" "z")'
    _UPPER     = '(re.range "A" "Z")'
    _UNDERSCORE = '(str.to_re "_")'
    _WORD      = f"(re.union (re.union {_LOWER} {_UPPER}) (re.union {_DIGITS} {_UNDERSCORE}))"
    _SPACE     = '(re.union (str.to_re " ") (re.union (str.to_re "\\t") (re.union (str.to_re "\\n") (str.to_re "\\r"))))'

    if category is _sre_const.CATEGORY_DIGIT:
        return _DIGITS
    if category is _sre_const.CATEGORY_NOT_DIGIT:
        return f"(re.comp {_DIGITS})"
    if category is _sre_const.CATEGORY_WORD:
        return _WORD
    if category is _sre_const.CATEGORY_NOT_WORD:
        return f"(re.comp {_WORD})"
    if category is _sre_const.CATEGORY_SPACE:
        return _SPACE
    if category is _sre_const.CATEGORY_NOT_SPACE:
        return f"(re.comp {_SPACE})"
    return None   # unknown category


# ── Theory classifier ─────────────────────────────────────────────

# Coq terms that signal string theory involvement
_STRING_SIGNALS = frozenset([
    "String.eqb", "String.append", "String.length", "String.index",
    "String.prefix", "String.substring", "String.concat",
    "asString", "VString", "isVString",
    "smem_f",       # our string-keyed set field
    "re_match",     # regex membership contract predicate: s.re_match("pat")
    "str.in_re",    # SMTLIB2 regex (may appear in post-reduction goals)
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
        # s1 and s2 may be paren-wrapped: (asString (s "name"))
        m = re.match(
            r'String\.index\s+0\s+(.+?)\s*<>\s*None$', expr)
        if m:
            rest = m.group(1).strip()
            s1, s2 = self._split_two_args(rest)
            if s1 is not None and s2 is not None:
                return f"(str.contains {self._coq_string_to_smt(s2, coq_sorts)} {self._coq_string_to_smt(s1, coq_sorts)})"

        # String.index 0 s1 s2 = None  ->  (not (str.contains s2 s1))
        m = re.match(
            r'String\.index\s+0\s+(.+?)\s*=\s*None$', expr)
        if m:
            rest = m.group(1).strip()
            s1, s2 = self._split_two_args(rest)
            if s1 is not None and s2 is not None:
                return f"(not (str.contains {self._coq_string_to_smt(s2, coq_sorts)} {self._coq_string_to_smt(s1, coq_sorts)}))"

        # String.prefix s1 s2 = true  ->  (str.prefixof s1 s2)
        m = re.match(
            r'String\.prefix\s+(.+?)\s*=\s*(true|false)$', expr)
        if m:
            rest = m.group(1).strip()
            s1, s2 = self._split_two_args(rest)
            if s1 is not None and s2 is not None:
                pref = f"(str.prefixof {self._coq_string_to_smt(s1, coq_sorts)} {self._coq_string_to_smt(s2, coq_sorts)})"
                return pref if m.group(2) == "true" else f"(not {pref})"

        # VString s1 = VString s2
        m = re.match(r'VString\s+(.+?)\s*=\s*VString\s+(.+)$', expr)
        if m:
            s1 = self._coq_string_to_smt(m.group(1), coq_sorts)
            s2 = self._coq_string_to_smt(m.group(2), coq_sorts)
            return f"(= {s1} {s2})"

        # String.length s > 0 / = n / >= n  (integer comparison on length)
        m = re.match(r'String\.length\s+(.+?)\s*([<>=!]+)\s*(.+)$', expr)
        if m:
            s = self._coq_string_to_smt(m.group(1), coq_sorts)
            coq_op = m.group(2)
            n = self._coq_int_to_smt(m.group(3), coq_sorts)
            smt_op = {"=": "=", ">": ">", "<": "<", ">=": ">=", "<=": "<=",
                      "!=": "distinct", "<>": "distinct"}.get(coq_op)
            if smt_op:
                return f"({smt_op} (str.len {s}) {n})"

        # re_match subject "pattern" [= true|false]  ->  (str.in_re s <re>)
        # Must come BEFORE the general equality check, because
        # 're_match (...) "pat" = true' would be misparse as LHS=re_match... RHS=true.
        if expr.startswith("re_match"):
            parsed = self._parse_re_match_call(expr, coq_sorts)
            if parsed:
                return parsed

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

        # str.in_re s r  (already in SMTLIB2 form, pass through)
        m = re.match(r'str\.in_re\s+(.+?)\s+(.+)$', expr)
        if m:
            s = self._coq_string_to_smt(m.group(1), coq_sorts)
            return f"(str.in_re {s} {m.group(2)})"

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

        # Strip outer parens and recurse (handles (asString (s "x")) etc.)
        if s.startswith('(') and s.endswith(')'):
            inner = s[1:-1].strip()
            # Only strip if balanced
            depth = 0
            for c in inner:
                if c == '(': depth += 1
                elif c == ')': depth -= 1
                if depth < 0:
                    break
            else:
                if depth == 0:
                    candidate = self._coq_string_to_smt(inner, coq_sorts)
                    # Only accept if it changed (otherwise infinite loop on bare literals)
                    if candidate != _smt_string_var(s):
                        return candidate

        # asString (s "x")  ->  x (the declared SMT variable)
        # Use fullmatch / $ anchor so partial prefix doesn't swallow a chain
        m = re.match(r'asString\s*\(\s*s\s*"([^"]+)"\s*\)\s*$', s)
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

        # String.append / ++ chain -- find the leftmost top-level ++
        # and recurse. Use paren-depth scanning so nested calls don't confuse.
        pp = self._split_concat(s)
        if pp is not None:
            a = self._coq_string_to_smt(pp[0], coq_sorts)
            b = self._coq_string_to_smt(pp[1], coq_sorts)
            return f"(str.++ {a} {b})"

        # Fallback: emit as-is (solver will reject if wrong)
        return _smt_string_var(s)

    def _parse_re_match_call(
        self, expr: str, coq_sorts: dict[str, str]
    ) -> Optional[str]:
        """Parse: re_match <subject> "<pattern>" [= true|false]

        The Coq form emitted by ReMatchExpr.to_coq():
          re_match subject "pattern"
          re_match (asString (s "result"%string)) "pattern" = true

        <subject> may be any Coq string expression.
        <pattern> is a Python regex literal (quoted string).

        Handles depth-aware parsing since <subject> may contain
        embedded quotes (e.g. asString (s "result")).
        """
        expr = expr.strip()
        if not expr.startswith('re_match'):
            return None
        rest = expr[8:].strip()   # everything after 're_match'

        # Parse the subject: either paren-wrapped or a bare token
        subject, after_subject = self._consume_one_arg(rest)
        if subject is None:
            return None

        after_subject = after_subject.strip()

        # Parse the pattern: a quoted string
        if not after_subject.startswith('"'):
            return None
        # Find closing quote (pattern may contain [ ] - + etc but not ")
        pat_end = after_subject.find('"', 1)
        if pat_end < 0:
            return None
        pattern = after_subject[1:pat_end]
        suffix = after_subject[pat_end+1:].strip()

        # re_match is now a Prop -- no = true / = false suffix.
        # Negation is expressed as ~ re_match ... in Coq, which appears
        # in the goal text as (not (re_match ...)) after wp_reduce.
        # We encode the positive form; the ~ case is handled by the
        # outer ~ / not handling in _encode_expr.
        negate = suffix.strip().startswith("= false")

        # Encode
        s_smt = self._coq_string_to_smt(subject, coq_sorts)
        re_smt = _python_re_to_smt(pattern)
        if not re_smt:
            return None
        membership = f"(str.in_re {s_smt} {re_smt})"
        return f"(not {membership})" if negate else membership

    def _consume_one_arg(self, s: str) -> "tuple[str | None, str]":
        """Consume one argument from the start of s.

        If s starts with '(', find the matching ')' and return
        (content_with_parens, rest). Otherwise take one whitespace-delimited token.
        Returns (arg, remainder) or (None, s) on failure.
        """
        s = s.strip()
        if not s:
            return (None, s)
        if s.startswith('('):
            depth = 0
            for i, c in enumerate(s):
                if c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                    if depth == 0:
                        return (s[:i+1], s[i+1:])
            return (None, s)
        # Bare token: take until whitespace
        m = re.match(r'(\S+)(.*)', s, re.DOTALL)
        if m:
            return (m.group(1), m.group(2))
        return (None, s)

    def _split_two_args(self, s: str) -> "tuple[str | None, str | None]":
        """Split 'arg1 arg2' where each arg may be paren-wrapped.

        Handles: 'name result', '(asString (s "name")) (asString (s "result"))'
        Returns (arg1, arg2) or (None, None).
        """
        s = s.strip()
        # If starts with '(', find matching ')' as arg1
        if s.startswith('('):
            depth = 0
            for i, c in enumerate(s):
                if c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                    if depth == 0:
                        arg1 = s[:i+1].strip()
                        arg2 = s[i+1:].strip()
                        return (arg1, arg2) if arg2 else (None, None)
            return (None, None)
        # Otherwise split on first whitespace
        parts = s.split(None, 1)
        if len(parts) == 2:
            return (parts[0], parts[1])
        return (None, None)

    def _split_concat(self, s: str) -> "tuple[str, str] | None":
        """Find the first top-level ++ in s (not inside parens or quotes).
        Returns (left, right) or None.
        """
        depth = 0
        in_str = False
        i = 0
        while i < len(s):
            c = s[i]
            if c == '"' and not in_str:
                # scan to end of string literal
                j = i + 1
                while j < len(s) and s[j] != '"':
                    j += 1
                i = j + 1
                continue
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            elif c == '+' and depth == 0 and i + 1 < len(s) and s[i+1] == '+':
                left  = s[:i].strip()
                right = s[i+2:].strip()
                if left and right:
                    return (left, right)
                break
            i += 1
        return None

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

    def dispatch_cases(
        self,
        case_branches: "list[CaseBranch]",
        property_spec,  # Callable[[CaseBranch], Optional[SmtFragment]]
    ) -> TheoryOracleResult:
        """Run SMT verification per case branch (case-dispatch verification).

        For each CaseBranch, calls property_spec to construct an SmtFragment,
        runs the SMT solver, and collects AxiomRecords (UNSAT) or
        TheoryCounterexamples (SAT).

        This is the core of the Herbrand-instantiation approach: each case
        is a ground QF_SLIA check, and the universal follows by Coq case analysis.

        Args:
            case_branches: List of CaseBranch extracted from IMP IR.
            property_spec:  Callable that maps a CaseBranch to an optional
                           SmtFragment.  Return None to skip a branch
                           (e.g., trivial cases that don't need SMT checks).

        Returns:
            TheoryOracleResult with per-case axioms or counterexamples.
        """
        result = TheoryOracleResult()

        for i, branch in enumerate(case_branches):
            fragment = property_spec(branch, i)
            if fragment is None:
                continue   # skip (e.g., empty branch, trivially true)

            status, raw_output, solver = _run_fragment(fragment, self.timeout)

            if status == "unsat":
                solver_ver = _SOLVER_CACHE.get(solver, "") or ""
                axiom_name = f"smt_case_{fragment.theory.kind.value}_{fragment.query_hash()}"
                axiom = AxiomRecord(
                    axiom_name=axiom_name,
                    coq_statement=fragment.coq_prop,
                    query_hash=fragment.query_hash(),
                    theory=fragment.theory.kind,
                    solver=solver,
                    solver_version=solver_ver,
                    fragment=fragment,
                )
                result.proved.append(axiom)

            elif status == "sat":
                model = _parse_model(raw_output, fragment.declarations)
                ce = TheoryCounterexample(
                    theory=fragment.theory.kind,
                    assignments=model,
                    violated_prop=fragment.coq_prop,
                    query_hash=fragment.query_hash(),
                    solver=solver,
                    raw_model=raw_output,
                )
                result.counterexamples.append(ce)

            else:
                result.unknown.append(fragment)

        return result


# ── Case-dispatch property specifications ────────────────────────────

def _expand_params_property_spec(branch: "CaseBranch", index: int) -> Optional[SmtFragment]:
    """Property spec for the type-convention of _expand_params.

    For each case branch, verifies that the output variables
    (expanded, parts/params_coq) follow the suffix convention:
      - If an output name ends in '_str', the Coq forall binder
        in params_coq uses ': string'.
      - Other suffixes (__len, __count) use ': Z'.
    """
    from .case_extractor import CaseBranch
    from .imp_ir import ImpCListAppend, ImpAString, ImpAVar
    from .imp_ir import ImpCIf, ImpBEq

    # Determine what this branch produces based on assignments.
    #
    # Each branch appends to 'expanded' and 'parts' using CListAppend.
    # We collect the concrete string patterns that this branch appends
    # to figure out what suffixes are produced.
    produced_suffixes: list[str] = []  # e.g. ["_str", "__len"]
    for cmd in branch.assignments:
        if isinstance(cmd, ImpCListAppend):
            if cmd.name == "expanded" and isinstance(cmd.value, ImpAVar):
                # Variable name is the output -- check suffix
                name = cmd.value.name
                if name.endswith("_str"):
                    produced_suffixes.append("_str")
                elif name.endswith("__len"):
                    produced_suffixes.append("__len")
                elif name.endswith("__count"):
                    produced_suffixes.append("__count")
            elif cmd.name == "expanded" and isinstance(cmd.value, ImpAString):
                # String literal -- check suffix
                val = cmd.value.value
                if val.endswith("_str"):
                    produced_suffixes.append("_str")
                elif val.endswith("__len"):
                    produced_suffixes.append("__len")

    if not produced_suffixes:
        return None   # no string classification needed

    # Build SMT query: for each suffix s in produced_suffixes,
    # verify the Coq type convention.
    # We use a simple QF_SLIA check:
    #   - Declare a string variable p (the parameter name)
    #   - Assert the path condition (p is in the right category)
    #   - Assert the generated suffix is correct
    #   - Check that params_coq contains the right binder

    # For now, return None to indicate "not yet fully automated"
    # -- we'll wire this in after the core dispatch infrastructure
    # is ready.
    return None


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
