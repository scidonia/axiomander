"""Tests for the case extractor (case-dispatch verification Phase 1)."""

import pytest
from axiomander.oracle.case_extractor import (
    CaseBranch,
    extract_cases,
    _has_loops,
    validate_mutual_exclusivity,
)
from axiomander.oracle.imp_ir import (
    ImpCIf, ImpCSeq, ImpCWhile, ImpCAss,
    ImpBEq, ImpBTrue, ImpBFalse, ImpBNot,
    ImpANum, ImpAVar,
    ImpCSkip, ImpCTry, ImpCRaise,
    ImpAString,
)


def test_simple_if_two_cases():
    """if x=0 then a:=1 else a:=2 → 2 cases."""
    com = ImpCIf(
        condition=ImpBEq(left=ImpANum(value=0), right=ImpANum(value=0)),
        then_branch=ImpCAss(target="a", value=ImpANum(value=1)),
        else_branch=ImpCAss(target="a", value=ImpANum(value=2)),
    )
    cases = extract_cases(com)
    assert len(cases) == 2
    assert len(cases[0].path_conditions) == 1  # condition
    assert len(cases[1].path_conditions) == 1  # NOT condition
    assert isinstance(cases[1].path_conditions[0], ImpBNot)


def test_nested_if_three_cases():
    """if x then (if y then a:=1 else a:=2) else a:=3 → 3 cases."""
    com = ImpCIf(
        condition=ImpBTrue(),
        then_branch=ImpCIf(
            condition=ImpBTrue(),
            then_branch=ImpCAss(target="a", value=ImpANum(value=1)),
            else_branch=ImpCAss(target="a", value=ImpANum(value=2)),
        ),
        else_branch=ImpCAss(target="a", value=ImpANum(value=3)),
    )
    cases = extract_cases(com)
    assert len(cases) == 3
    # then-then: 2 conditions
    assert len(cases[0].path_conditions) == 2
    # then-else: 2 conditions (first true, second negated)
    assert len(cases[1].path_conditions) == 2


def test_cseq_linear_single_case():
    """a:=1; b:=2 → 1 case with 2 assignments."""
    com = ImpCSeq(commands=[
        ImpCAss(target="a", value=ImpANum(value=1)),
        ImpCAss(target="b", value=ImpANum(value=2)),
    ])
    cases = extract_cases(com)
    assert len(cases) == 1
    assert len(cases[0].assignments) == 2
    assert len(cases[0].path_conditions) == 0


def test_cif_in_cseq():
    """a:=1; if x then b:=2 else b:=3; c:=4 → 2 cases, each 3 assignments."""
    com = ImpCSeq(commands=[
        ImpCAss(target="a", value=ImpANum(value=1)),
        ImpCIf(
            condition=ImpBTrue(),
            then_branch=ImpCAss(target="b", value=ImpANum(value=2)),
            else_branch=ImpCAss(target="b", value=ImpANum(value=3)),
        ),
        ImpCAss(target="c", value=ImpANum(value=4)),
    ])
    cases = extract_cases(com)
    assert len(cases) == 2
    for br in cases:
        assert len(br.assignments) == 3
        # First assignment: a:=1
        assert isinstance(br.assignments[0], ImpCAss)
        # Last assignment: c:=4
        assert isinstance(br.assignments[2], ImpCAss)
        assert br.assignments[2].target == "c"  # type: ignore[attr-defined]


def test_reject_loop_in_then_branch():
    """if x then (while true skip) else skip → ValueError."""
    com = ImpCIf(
        condition=ImpBTrue(),
        then_branch=ImpCWhile(
            condition=ImpBTrue(),
            invariant="(fun _ => True)",
            body=ImpCSkip(),
        ),
        else_branch=ImpCSkip(),
    )
    with pytest.raises(ValueError, match="loops inside branches"):
        extract_cases(com)


def test_reject_loop_in_else_branch():
    """if x then skip else (while true skip) → ValueError."""
    com = ImpCIf(
        condition=ImpBTrue(),
        then_branch=ImpCSkip(),
        else_branch=ImpCWhile(
            condition=ImpBTrue(),
            invariant="(fun _ => True)",
            body=ImpCSkip(),
        ),
    )
    with pytest.raises(ValueError, match="loops inside branches"):
        extract_cases(com)


def test_skip_is_filtered():
    """CSkip in sequence is filtered out."""
    com = ImpCSeq(commands=[
        ImpCAss(target="a", value=ImpANum(value=1)),
        ImpCSkip(),
        ImpCAss(target="b", value=ImpANum(value=2)),
        ImpCSkip(),
    ])
    cases = extract_cases(com)
    assert len(cases) == 1
    assert len(cases[0].assignments) == 2


def test_mutual_exclusivity_detects_conflict():
    """if x=1 then ... else ... → conditions are exclusive."""
    cases = extract_cases(ImpCIf(
        condition=ImpBEq(left=ImpAVar(name="x"), right=ImpANum(value=1)),
        then_branch=ImpCSkip(),
        else_branch=ImpCSkip(),
    ))
    assert validate_mutual_exclusivity(cases) is None  # no overlap found


def test_mutual_exclusivity_non_exclusive():
    """Identical path conditions → overlap detected."""
    br_a = CaseBranch(path_conditions=[ImpBTrue()], assignments=[])
    br_b = CaseBranch(path_conditions=[ImpBTrue()], assignments=[])
    result = validate_mutual_exclusivity([br_a, br_b])
    assert result is not None
    assert "may overlap" in result


def test_empty_cseq():
    """Empty CSeq → single empty case."""
    cases = extract_cases(ImpCSeq(commands=[]))
    assert len(cases) == 1
    assert len(cases[0].assignments) == 0


def test_deeply_nested_exponential():
    """3-level nested if → 8 cases."""
    def mk_if(depth: int) -> ImpCIf:
        if depth == 0:
            return ImpCIf(
                condition=ImpBTrue(),
                then_branch=ImpCAss(target="a", value=ImpANum(value=0)),
                else_branch=ImpCAss(target="a", value=ImpANum(value=1)),
            )
        inner = mk_if(depth - 1)
        return ImpCIf(
            condition=ImpBTrue(),
            then_branch=inner,
            else_branch=inner,
        )

    com = mk_if(2)  # 2^3 = 8 cases
    cases = extract_cases(com)
    assert len(cases) == 8
    # Each case should have 3 conditions
    for br in cases:
        assert len(br.path_conditions) == 3


def test_has_loops_deep_try():
    """CWhile inside CTry handler → detected."""
    com = ImpCTry(
        body=ImpCSkip(),
        exc="e",
        handler=ImpCWhile(
            condition=ImpBTrue(),
            invariant="(fun _ => True)",
            body=ImpCSkip(),
        ),
    )
    assert _has_loops(com) is True


def test_has_loops_no_loop():
    """Linear sequence without loops → no loops."""
    com = ImpCSeq(commands=[
        ImpCAss(target="a", value=ImpANum(value=1)),
        ImpCAss(target="b", value=ImpANum(value=2)),
    ])
    assert _has_loops(com) is False


def test_condition_conjunct():
    """condition_conjunct builds BAnd chain."""
    from axiomander.oracle.imp_ir import ImpBAnd
    br = CaseBranch(
        path_conditions=[ImpBTrue(), ImpBTrue()],
        assignments=[],
    )
    conj = br.condition_conjunct()
    assert conj is not None
    assert isinstance(conj, ImpBAnd)
