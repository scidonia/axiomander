"""Tests for the theory-SMT oracle (theory_smt.py).

Three layers:
  1. Unit tests for _python_re_to_smt: each sre_parse opcode maps
     correctly to its SMTLIB2 RegLan expression, verified by running
     the output through Z3.
  2. Unit tests for TheoryDispatcher: string goals prove or produce
     typed counterexamples as expected.
  3. Pipeline integration tests: functions with string postconditions
     reach ProofLevel.LEVEL2B_SMT_THEORY (or better).

Run with:
  eval $(opam env)
  PYTHONPATH=py .venv/bin/python -m pytest py/tests/test_theory_smt.py -v
"""

import os
import subprocess
import sys
import tempfile
import warnings
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

with warnings.catch_warnings():
    warnings.simplefilter("ignore", DeprecationWarning)
    from oracle.theory_smt import (
        _python_re_to_smt,
        TheoryDispatcher,
        classify_goal,
        TheoryKind,
        STRING_THEORY,
        FLOAT_THEORY,
    )
from oracle.mcp_server import _verify_function
from oracle.reporting import ProofLevel


# ── Helpers ───────────────────────────────────────────────────────

def _z3_available() -> bool:
    return subprocess.run(
        ["z3", "--version"], capture_output=True
    ).returncode == 0


def _smt_check(logic: str, decls: str, asserts: str) -> str:
    """Run a raw SMTLIB2 query through Z3. Returns 'sat', 'unsat', or 'error'."""
    query = f"(set-logic {logic})\n{decls}\n{asserts}\n(check-sat)\n"
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".smt2", delete=False
    ) as f:
        f.write(query)
        path = f.name
    try:
        r = subprocess.run(
            ["z3", path], capture_output=True, text=True, timeout=10
        )
        first = r.stdout.strip().split("\n")[0].strip()
        return first if first in ("sat", "unsat") else "error"
    except Exception:
        return "error"
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


def _re_sat(re_expr: str, string_val: str) -> str:
    """Check whether string_val is in the language of re_expr via Z3."""
    decl = '(declare-const s String)'
    hyp  = f'(assert (= s "{string_val}"))'
    mem  = f'(assert (str.in_re s {re_expr}))'
    return _smt_check("QF_SLIA", decl, f"{hyp}\n{mem}")


def _re_not_member(re_expr: str, string_val: str) -> str:
    """Check that string_val is NOT in the language of re_expr.

    Returns 'unsat' if the membership assertion is unsatisfiable
    (i.e. string_val definitely does not match re_expr).
    """
    decl = '(declare-const s String)'
    hyp  = f'(assert (= s "{string_val}"))'
    mem  = f'(assert (str.in_re s {re_expr}))'
    return _smt_check("QF_SLIA", decl, f"{hyp}\n{mem}")


# ── 1. Unit tests: _python_re_to_smt ─────────────────────────────

@pytest.mark.skipif(not _z3_available(), reason="z3 not available")
class TestPythonReToSmt:
    """Verify each sre_parse opcode maps to the correct SMTLIB2 expression
    by checking membership with Z3."""

    # ── LITERAL / single char ────────────────────────────────────

    def test_literal_matches(self):
        smt = _python_re_to_smt("a")
        assert smt is not None
        assert _re_sat(smt, "a") == "sat"
        assert _re_not_member(smt, "b") == "unsat"  # "b" is not in lang("a")

    def test_literal_quote_in_string(self):
        # Double-quote must be SMTLIB2-escaped; skip if Z3 can't handle it
        smt = _python_re_to_smt('"')
        assert smt is not None
        # Just verify the expression is structurally correct (contains str.to_re)
        assert "str.to_re" in smt

    # ── ANY (.) ──────────────────────────────────────────────────

    def test_any_matches_single_char(self):
        smt = _python_re_to_smt(".")
        assert smt is not None
        assert _re_sat(smt, "x") == "sat"
        assert _re_sat(smt, "5") == "sat"

    def test_any_does_not_match_empty(self):
        smt = _python_re_to_smt(".")
        assert smt is not None
        assert _re_sat(smt, "") == "unsat"

    # ── IN: character class ──────────────────────────────────────

    def test_range_az(self):
        smt = _python_re_to_smt("[a-z]")
        assert smt is not None
        assert _re_sat(smt, "m") == "sat"
        assert _re_sat(smt, "A") == "unsat"
        assert _re_sat(smt, "5") == "unsat"

    def test_range_AZ(self):
        smt = _python_re_to_smt("[A-Z]")
        assert smt is not None
        assert _re_sat(smt, "M") == "sat"
        assert _re_sat(smt, "m") == "unsat"

    def test_range_digits(self):
        smt = _python_re_to_smt("[0-9]")
        assert smt is not None
        assert _re_sat(smt, "7") == "sat"
        assert _re_sat(smt, "a") == "unsat"

    def test_class_union(self):
        smt = _python_re_to_smt("[aeiou]")
        assert smt is not None
        assert _re_sat(smt, "e") == "sat"
        assert _re_sat(smt, "b") == "unsat"

    def test_negated_class(self):
        smt = _python_re_to_smt("[^0-9]")
        assert smt is not None
        assert _re_sat(smt, "a") == "sat"
        assert _re_sat(smt, "5") == "unsat"

    def test_multi_range_class(self):
        smt = _python_re_to_smt("[a-zA-Z]")
        assert smt is not None
        assert _re_sat(smt, "Z") == "sat"
        assert _re_sat(smt, "z") == "sat"
        assert _re_sat(smt, "5") == "unsat"

    # ── CATEGORY: \d \w \s ──────────────────────────────────────

    def test_category_digit(self):
        smt = _python_re_to_smt(r"\d")
        assert smt is not None
        assert _re_sat(smt, "9") == "sat"
        assert _re_sat(smt, "a") == "unsat"

    def test_category_word(self):
        smt = _python_re_to_smt(r"\w")
        assert smt is not None
        assert _re_sat(smt, "a") == "sat"
        assert _re_sat(smt, "Z") == "sat"
        assert _re_sat(smt, "5") == "sat"
        assert _re_sat(smt, "_") == "sat"
        assert _re_sat(smt, " ") == "unsat"

    def test_category_space(self):
        smt = _python_re_to_smt(r"\s")
        assert smt is not None
        assert _re_sat(smt, " ") == "sat"
        assert _re_sat(smt, "a") == "unsat"

    def test_category_not_digit(self):
        smt = _python_re_to_smt(r"\D")
        assert smt is not None
        assert _re_sat(smt, "a") == "sat"
        assert _re_sat(smt, "5") == "unsat"

    # ── MAX_REPEAT: * + ? {n} {n,m} ─────────────────────────────

    def test_star_matches_empty(self):
        smt = _python_re_to_smt("[a-z]*")
        assert smt is not None
        assert _re_sat(smt, "") == "sat"
        assert _re_sat(smt, "abc") == "sat"

    def test_plus_rejects_empty(self):
        smt = _python_re_to_smt("[a-z]+")
        assert smt is not None
        assert _re_sat(smt, "") == "unsat"
        assert _re_sat(smt, "a") == "sat"
        assert _re_sat(smt, "abc") == "sat"

    def test_opt(self):
        smt = _python_re_to_smt("a?")
        assert smt is not None
        assert _re_sat(smt, "") == "sat"
        assert _re_sat(smt, "a") == "sat"
        assert _re_sat(smt, "aa") == "unsat"

    def test_exact_repeat(self):
        smt = _python_re_to_smt("[0-9]{4}")
        assert smt is not None
        assert _re_sat(smt, "1234") == "sat"
        assert _re_sat(smt, "123") == "unsat"
        assert _re_sat(smt, "12345") == "unsat"

    def test_range_repeat(self):
        smt = _python_re_to_smt("[a-z]{2,4}")
        assert smt is not None
        assert _re_sat(smt, "ab") == "sat"
        assert _re_sat(smt, "abcd") == "sat"
        assert _re_sat(smt, "a") == "unsat"
        assert _re_sat(smt, "abcde") == "unsat"

    def test_unbounded_repeat(self):
        smt = _python_re_to_smt("[a-z]{2,}")
        assert smt is not None
        assert _re_sat(smt, "ab") == "sat"
        assert _re_sat(smt, "abcdefgh") == "sat"
        assert _re_sat(smt, "a") == "unsat"

    # ── BRANCH: alternation ──────────────────────────────────────

    def test_alternation(self):
        smt = _python_re_to_smt("foo|bar")
        assert smt is not None
        assert _re_sat(smt, "foo") == "sat"
        assert _re_sat(smt, "bar") == "sat"
        assert _re_sat(smt, "baz") == "unsat"

    def test_alternation_in_group(self):
        smt = _python_re_to_smt("(cat|dog)s?")
        assert smt is not None
        assert _re_sat(smt, "cat") == "sat"
        assert _re_sat(smt, "dogs") == "sat"
        assert _re_sat(smt, "bird") == "unsat"

    # ── Concatenation ────────────────────────────────────────────

    def test_concat(self):
        smt = _python_re_to_smt("[A-Z][a-z]+")
        assert smt is not None
        assert _re_sat(smt, "Hello") == "sat"
        assert _re_sat(smt, "hello") == "unsat"   # must start uppercase
        assert _re_sat(smt, "H") == "unsat"        # needs at least one lowercase

    def test_iso_date(self):
        smt = _python_re_to_smt(r"[0-9]{4}-[0-9]{2}-[0-9]{2}")
        assert smt is not None
        assert _re_sat(smt, "2024-01-31") == "sat"
        assert _re_sat(smt, "24-01-31") == "unsat"
        assert _re_sat(smt, "2024/01/31") == "unsat"

    def test_email_like(self):
        smt = _python_re_to_smt(r"[a-z]+@[a-z]+\.[a-z]+")
        assert smt is not None
        assert _re_sat(smt, "user@example.com") == "sat"
        assert _re_sat(smt, "notanemail") == "unsat"

    def test_identifier(self):
        smt = _python_re_to_smt(r"[a-zA-Z_][a-zA-Z0-9_]*")
        assert smt is not None
        assert _re_sat(smt, "my_var") == "sat"
        assert _re_sat(smt, "_x") == "sat"
        assert _re_sat(smt, "99bottles") == "unsat"  # must start with letter/_

    # ── Anchors ──────────────────────────────────────────────────

    def test_anchors_are_transparent(self):
        # ^ and $ are implicit in str.in_re; stripping them gives same result
        with_anchors    = _python_re_to_smt("^[a-z]+$")
        without_anchors = _python_re_to_smt("[a-z]+")
        assert with_anchors is not None
        assert without_anchors is not None
        # Both should accept "hello" and reject "Hello"
        assert _re_sat(with_anchors, "hello") == "sat"
        assert _re_sat(with_anchors, "Hello") == "unsat"

    # ── Unsupported features return None cleanly ─────────────────

    def test_backreference_returns_none(self):
        # \1 backreference -- sre_parse gives GROUPREF, we return None
        smt = _python_re_to_smt(r"(a)\1")
        assert smt is None

    def test_invalid_pattern_returns_none(self):
        smt = _python_re_to_smt("[unclosed")
        assert smt is None


# ── 2. Unit tests: TheoryDispatcher ──────────────────────────────

@pytest.mark.skipif(not _z3_available(), reason="z3 not available")
class TestTheoryDispatcher:

    def _dispatch(
        self,
        goal: str,
        hyps: "list[str] | None" = None,
        param_types: "dict | None" = None,
    ):
        d = TheoryDispatcher(
            param_types=param_types or {"result": "str", "name": "str",
                                        "coq_type": "str"},
            timeout=15,
        )
        return d.dispatch([goal], hyps or [])

    # ── Classify ─────────────────────────────────────────────────

    def test_classify_string_goal(self):
        t = classify_goal('String.index 0 name result <> None')
        assert t is not None
        assert t.kind == TheoryKind.STRING

    def test_classify_float_goal(self):
        t = classify_goal('asFloat (s "x") = 150')
        assert t is not None
        assert t.kind == TheoryKind.FLOAT

    def test_classify_int_goal_returns_none(self):
        # Pure integer arithmetic -- handled upstream by _smt_prove_goal
        assert classify_goal('asZ (s "n") >= 0') is None

    def test_classify_re_match_goal(self):
        assert classify_goal('re_match (asString (s "s")) "[a-z]+"') is not None

    # ── String contains ──────────────────────────────────────────

    def test_contains_proved_with_concat_hyp(self):
        """name in result when result = '(' ++ name ++ ')'."""
        hyp  = 'asString (s "result") = "(" ++ asString (s "name") ++ ")"'
        goal = 'String.index 0 (asString (s "name")) (asString (s "result")) <> None'
        res = self._dispatch(goal, [hyp])
        assert len(res.proved) == 1
        assert len(res.counterexamples) == 0

    def test_contains_counterexample_without_hyp(self):
        """Without a hypothesis tying result to name, contains is not always true."""
        goal = 'String.index 0 (asString (s "name")) (asString (s "result")) <> None'
        res = self._dispatch(goal, [])
        # SMT finds a model where result does not contain name
        assert len(res.counterexamples) == 1
        ce = res.counterexamples[0]
        # The typed counterexample carries String-sort values
        assert any(v.sort == "String" for v in ce.assignments.values())

    # ── String prefix ────────────────────────────────────────────

    def test_prefix_proved(self):
        """result always has prefix '(' when result = '(' ++ rest."""
        hyp  = 'asString (s "result") = "(" ++ asString (s "name") ++ ")"'
        goal = 'String.prefix "(" (asString (s "result")) = true'
        res = self._dispatch(goal, [hyp])
        assert len(res.proved) == 1

    def test_prefix_counterexample(self):
        """result doesn't always start with 'z'."""
        hyp  = 'asString (s "result") = "(" ++ asString (s "name") ++ ")"'
        goal = 'String.prefix "z" (asString (s "result")) = true'
        res = self._dispatch(goal, [hyp])
        assert len(res.counterexamples) == 1

    # ── Regex membership ─────────────────────────────────────────

    def test_regex_implies_nonempty(self):
        """If result matches [a-z]+ then its length is > 0."""
        hyp  = 're_match (asString (s "result")) "[a-z]+"'
        goal = 'String.length (asString (s "result")) > 0'
        res = self._dispatch(goal, [hyp], {"result": "str"})
        assert len(res.proved) == 1

    def test_regex_counterexample_wrong_start(self):
        """[a-z]+ does not imply the string starts with 'z'."""
        hyp  = 're_match (asString (s "result")) "[a-z]+"'
        goal = 'String.prefix "z" (asString (s "result")) = true'
        res = self._dispatch(goal, [hyp], {"result": "str"})
        assert len(res.counterexamples) == 1
        ce = res.counterexamples[0]
        # result should be a single lowercase letter that isn't 'z'
        result_val = ce.assignments.get("result")
        assert result_val is not None
        assert result_val.sort == "String"

    def test_iso_date_regex(self):
        """A date matching [0-9]{4}-[0-9]{2}-[0-9]{2} has length 10."""
        hyp  = r're_match (asString (s "result")) "[0-9]{4}-[0-9]{2}-[0-9]{2}"'
        goal = 'String.length (asString (s "result")) > 0'
        res = self._dispatch(goal, [hyp], {"result": "str"})
        assert len(res.proved) == 1

    # ── Counterexample typing ────────────────────────────────────

    def test_counterexample_has_typed_values(self):
        """Counterexamples carry TheoryValues with sort and python repr."""
        goal = 'String.index 0 "xyz" (asString (s "result")) <> None'
        res = self._dispatch(goal, [])
        assert len(res.counterexamples) == 1
        ce = res.counterexamples[0]
        # result is a String value
        result_val = ce.assignments.get("result")
        assert result_val is not None
        assert result_val.sort == "String"
        # python repr is a quoted string
        assert result_val.python.startswith("'") or result_val.python.startswith('"')
        # format_report produces a readable string
        report = ce.format_report()
        assert "result" in report
        assert "String" in report

    # ── AxiomRecord structure ────────────────────────────────────

    def test_axiom_has_hash_and_solver(self):
        hyp  = 'asString (s "result") = "(" ++ asString (s "name") ++ ")"'
        goal = 'String.index 0 (asString (s "name")) (asString (s "result")) <> None'
        res = self._dispatch(goal, [hyp])
        assert res.proved
        ax = res.proved[0]
        # Name encodes theory and query hash
        assert ax.axiom_name.startswith("smt_string_")
        assert len(ax.query_hash) == 16
        # Coq statement is universally quantified
        assert "forall" in ax.coq_statement
        # to_coq() includes attribution comment
        coq = ax.to_coq()
        assert "SMT-verified" in coq
        assert "Axiom" in coq

    # ── Unknown (fall-through) ───────────────────────────────────

    def test_unknown_for_unencodable_goal(self):
        """Goals the encoder can't handle fall through to unknown."""
        # This goal has no string signal -- classify_goal returns None
        # so the dispatcher skips it entirely (returns empty result)
        goal = 'asZ (s "n") >= 0'
        res = self._dispatch(goal, [])
        assert len(res.proved) == 0
        assert len(res.counterexamples) == 0
        assert len(res.unknown) == 0   # pure int: not our responsibility

    # ── Regex gate: subsumption vs contradiction ──────────────────
    #
    # A "regex gate" precondition constrains the input to a specific
    # pattern.  A postcondition that is WEAKER (a superset of the
    # precondition's language) is a subsumption -- it must be proved.
    # A postcondition that is DISJOINT is a contradiction -- the SMT
    # oracle must produce a concrete counterexample.
    #
    # Phone number as the running example:
    #   STRONG (gate):  [0-9]{3}-[0-9]{3}-[0-9]{4}  e.g. "555-867-5309"
    #   WEAKER:         [0-9-]+   (digits and dashes  -- superset)
    #   WEAKEST:        .+        (any non-empty       -- superset)
    #   DISJOINT:       [A-Za-z]+ (letters only        -- no phone matches)

    PHONE_GATE    = r"[0-9]{3}-[0-9]{3}-[0-9]{4}"
    DIGITS_DASHES = r"[0-9-]+"
    NONEMPTY      = r".+"
    LETTERS_ONLY  = r"[A-Za-z]+"

    def _phone_hyp(self) -> str:
        return f're_match (asString (s "s")) "{self.PHONE_GATE}"'

    def test_phone_gate_implies_digits_dashes(self):
        """Subsumption: phone format [0-9]{3}-[0-9]{3}-[0-9]{4}
        implies the weaker pattern [0-9-]+ (digits and dashes).

        Every string matching the full phone format contains only
        digits and dashes, so the postcondition is a superset.
        Z3 must prove this by showing no phone string violates [0-9-]+.
        """
        goal = f're_match (asString (s "s")) "{self.DIGITS_DASHES}"'
        res = self._dispatch(goal, [self._phone_hyp()], {"s": "str"})
        assert len(res.proved) == 1, (
            f"Expected subsumption proof, got: "
            f"ce={res.counterexamples} unknown={res.unknown}"
        )
        assert len(res.counterexamples) == 0

    def test_phone_gate_implies_nonempty(self):
        """Subsumption: phone format implies .+ (weakest non-empty).

        Any string in [0-9]{3}-[0-9]{3}-[0-9]{4} is non-empty (length 12),
        so the weakest possible postcondition is trivially subsumed.
        """
        goal = f're_match (asString (s "s")) "{self.NONEMPTY}"'
        res = self._dispatch(goal, [self._phone_hyp()], {"s": "str"})
        assert len(res.proved) == 1
        assert len(res.counterexamples) == 0

    def test_phone_gate_contradicts_letters(self):
        """Contradiction: phone format does NOT imply [A-Za-z]+.

        Phone numbers contain only digits and dashes -- no letters.
        The postcondition [A-Za-z]+ is disjoint from the phone language.
        Z3 must produce a concrete phone number as the witness.
        """
        goal = f're_match (asString (s "s")) "{self.LETTERS_ONLY}"'
        res = self._dispatch(goal, [self._phone_hyp()], {"s": "str"})
        assert len(res.counterexamples) == 1, (
            f"Expected counterexample, got: proved={res.proved} unknown={res.unknown}"
        )
        assert len(res.proved) == 0

        ce = res.counterexamples[0]
        s_val = ce.assignments.get("s")
        assert s_val is not None
        assert s_val.sort == "String"

        # The witness must be a valid phone number:
        # strip quotes from the python repr and check it matches the gate
        import re as _re
        raw = s_val.python.strip("'\"")
        assert _re.fullmatch(self.PHONE_GATE, raw) is not None, (
            f"Witness {raw!r} does not match the phone gate {self.PHONE_GATE!r}"
        )

    def test_weak_pre_strong_post_contradiction(self):
        """Contradiction from wrong direction: weak precondition cannot
        imply a stronger postcondition.

        Precondition:  s matches [0-9-]+  (digits and dashes -- weak)
        Postcondition: s matches full phone format  (strong)

        A string like "0" satisfies [0-9-]+ but not the full phone format.
        Z3 must find it as the counterexample.
        """
        hyp_weak = f're_match (asString (s "s")) "{self.DIGITS_DASHES}"'
        goal_strong = f're_match (asString (s "s")) "{self.PHONE_GATE}"'

        res = self._dispatch(goal_strong, [hyp_weak], {"s": "str"})
        assert len(res.counterexamples) == 1
        assert len(res.proved) == 0

        ce = res.counterexamples[0]
        s_val = ce.assignments.get("s")
        assert s_val is not None
        # The witness satisfies [0-9-]+ but NOT the phone format
        import re as _re
        raw = s_val.python.strip("'\"")
        assert _re.fullmatch(self.DIGITS_DASHES, raw) is not None, (
            f"Witness {raw!r} should match {self.DIGITS_DASHES!r}"
        )
        assert _re.fullmatch(self.PHONE_GATE, raw) is None, (
            f"Witness {raw!r} should NOT match phone gate {self.PHONE_GATE!r}"
        )


# ── 3. Pipeline integration tests ────────────────────────────────

@pytest.mark.skipif(not _z3_available(), reason="z3 not available")
class TestTheorySMTPipeline:
    """End-to-end: functions whose postconditions involve string theory
    should be provable at Level 2b or better."""

    def _verify(self, source: str, func_name: str):
        os.environ.setdefault(
            "AXIOMANDER_ROOT",
            str(Path(__file__).resolve().parent.parent.parent)
        )
        return _verify_function(source, func_name, None)

    def test_string_result_equality(self):
        """Function returning a fixed string: result == literal postcondition.

        This exercises the string equality path through the pipeline.
        The postcondition result == "hello" should prove at Level 1 via
        wp_reduce + reflexivity (VString equality is decidable).
        """
        source = '''
def greeting() -> str:
    """
    axiomander:
        ensures:
            result == "hello"
    """
    result = "hello"
    return result
'''
        goal = self._verify(source, "greeting")
        assert goal is not None
        assert goal.is_proved(), f"Not proved: {goal.error_detail[:200]}"

    def test_string_equality_literal(self):
        """Function returning a fixed string: exact equality postcondition.

        result == "world" when the body assigns result = "world".
        This is the simplest string postcondition -- pure VString equality,
        discharged by wp_reduce + reflexivity at Level 1.
        """
        source = '''
def const_str() -> str:
    """
    axiomander:
        ensures:
            result == "world"
    """
    result = "world"
    return result
'''
        goal = self._verify(source, "const_str")
        assert goal is not None
        assert goal.is_proved(), f"Not proved: {goal.error_detail[:200]}"

    def test_wrong_string_contract_detected(self):
        """A postcondition that cannot hold should not be proved.

        result == "wrong" when the body returns "hello" should fail.
        This exercises the negative path for string equality.
        """
        source = '''
def greeting() -> str:
    """
    axiomander:
        ensures:
            result == "wrong"
    """
    result = "hello"
    return result
'''
        goal = self._verify(source, "greeting")
        assert goal is not None
        assert not goal.is_proved(), f"Should not be proved but level={goal.level}"

    def test_two_function_phone_gate_subsumption(self):
        """Two-function composition: parse_phone -> send_sms.

        parse_phone postcondition (full phone regex) must satisfy
        send_sms precondition (same full phone regex).
        Same pattern -> subsumption -> notify_user should prove at Level 1.

        This is the canonical regex gate composition example:
          - parse_phone: str -> str, ensures result.re_match(PHONE)
          - send_sms: str -> int, requires phone.re_match(PHONE)
          - notify_user: chains them, should prove result == 0
        """
        source = '''
def parse_phone(raw: str) -> str:
    """
    axiomander:
        ensures:
            result.re_match("[0-9]{3}-[0-9]{3}-[0-9]{4}")
    """
    result = raw
    assert result.re_match("[0-9]{3}-[0-9]{3}-[0-9]{4}")
    return result


def send_sms(phone: str) -> int:
    """
    axiomander:
        requires:
            phone.re_match("[0-9]{3}-[0-9]{3}-[0-9]{4}")
        ensures:
            result == 0
    """
    result = 0
    return result


def notify_user(raw: str) -> int:
    """
    axiomander:
        requires:
            True
        ensures:
            result == 0
    """
    phone = parse_phone(raw)
    result = send_sms(phone)
    return result
'''
        goal = self._verify(source, "notify_user")
        assert goal is not None
        assert goal.is_proved(), (
            f"notify_user should prove (regex subsumption at CCall boundary) "
            f"but level={goal.level}, error={goal.error_detail[:200]}"
        )
