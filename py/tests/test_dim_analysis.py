"""Tests for the dimensional analysis system.

Three layers:
  1. DimVec algebra -- correct composition under *, /, **
  2. dim_parse -- correct parsing of dimension expression strings  
  3. DimChecker -- correct detection of violations and consistency

Run with:
  PYTHONPATH=py .venv/bin/python -m pytest py/tests/test_dim_analysis.py -v
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import pytest
from oracle.dim_ir import (
    DimVec, dim_parse, parse_units_section,
    DimConstraint, check_constraints,
)
from oracle.dim_checker import check_dimensions_from_source


# ── 1. DimVec algebra ─────────────────────────────────────────────

class TestDimVec:

    def test_base_dimension(self):
        d = DimVec.base("USD")
        assert d.components == {"USD": 1}

    def test_dimensionless(self):
        d = DimVec.dimensionless()
        assert d.is_dimensionless()
        assert d.components == {}

    def test_multiply_composes(self):
        usd = DimVec.base("USD")
        person = DimVec.base("person")
        result = usd * person
        assert result.components == {"USD": 1, "person": 1}

    def test_divide_subtracts(self):
        usd = DimVec.base("USD")
        person = DimVec.base("person")
        result = usd / person
        assert result.components == {"USD": 1, "person": -1}

    def test_divide_cancels(self):
        usd = DimVec.base("USD")
        result = usd / usd
        assert result.is_dimensionless()

    def test_power_scales(self):
        m = DimVec.base("m")
        result = m ** 2
        assert result.components == {"m": 2}

    def test_power_zero_is_dimensionless(self):
        m = DimVec.base("m")
        result = m ** 0
        assert result.is_dimensionless()

    def test_negative_power(self):
        s = DimVec.base("s")
        result = s ** -1
        assert result.components == {"s": -1}

    def test_exchange_rate(self):
        gbp = DimVec.base("GBP")
        usd = DimVec.base("USD")
        rate = usd / gbp          # [USD/GBP]
        amount_gbp = gbp          # [GBP]
        result = amount_gbp * rate
        assert result.components == {"USD": 1}  # [USD]

    def test_per_capita_income(self):
        usd = DimVec.base("USD")
        person = DimVec.base("person")
        per_capita = usd / person   # [USD/person]
        population = person          # [person]
        total = per_capita * population
        assert total.components == {"USD": 1}  # [USD]

    def test_portfolio_value(self):
        share = DimVec.base("share")
        usd = DimVec.base("USD")
        price_per_share = usd / share      # [USD/share]
        quantity = share                    # [share]
        value = price_per_share * quantity
        assert value.components == {"USD": 1}

    def test_incompatible_currencies_not_equal(self):
        usd = DimVec.base("USD")
        gbp = DimVec.base("GBP")
        assert not usd.compatible_with(gbp)

    def test_same_currency_compatible(self):
        usd1 = DimVec.base("USD")
        usd2 = DimVec.base("USD")
        assert usd1.compatible_with(usd2)

    def test_dimensionless_times_dimensioned(self):
        usd = DimVec.base("USD")
        scale = DimVec.dimensionless()
        result = usd * scale
        assert result.components == {"USD": 1}

    def test_repr_simple(self):
        d = DimVec.base("USD")
        assert repr(d) == "[USD]"

    def test_repr_ratio(self):
        usd = DimVec.base("USD")
        person = DimVec.base("person")
        d = usd / person
        assert repr(d) == "[USD/person]"

    def test_repr_dimensionless(self):
        d = DimVec.dimensionless()
        assert repr(d) == "[1]"

    def test_equality(self):
        a = DimVec({"USD": 1, "person": -1})
        b = DimVec({"person": -1, "USD": 1})
        assert a == b  # order-independent

    def test_hashable(self):
        d = DimVec.base("USD")
        s = {d, DimVec.base("USD")}
        assert len(s) == 1

    def test_zero_exponent_eliminated(self):
        # USD^1 * USD^-1 = {} (zero exponents pruned)
        usd = DimVec.base("USD")
        result = usd / usd
        assert "USD" not in result.components

    def test_joules(self):
        # kg * m^2 / s^2
        kg = DimVec.base("kg")
        m  = DimVec.base("m")
        s  = DimVec.base("s")
        J  = kg * (m ** 2) / (s ** 2)
        assert J.components == {"kg": 1, "m": 2, "s": -2}

    def test_annual_per_capita(self):
        # USD / person / year
        usd    = DimVec.base("USD")
        person = DimVec.base("person")
        year   = DimVec.base("year")
        result = usd / person / year
        assert result.components == {"USD": 1, "person": -1, "year": -1}
        # Multiplying by person * year gives USD
        total = result * person * year
        assert total.components == {"USD": 1}


# ── 2. dim_parse ──────────────────────────────────────────────────

class TestDimParse:

    def test_simple_base(self):
        assert dim_parse("USD") == DimVec.base("USD")

    def test_dimensionless_one(self):
        assert dim_parse("1") == DimVec.dimensionless()

    def test_ratio(self):
        d = dim_parse("USD/person")
        assert d.components == {"USD": 1, "person": -1}

    def test_product(self):
        d = dim_parse("kg*m")
        assert d.components == {"kg": 1, "m": 1}

    def test_power(self):
        d = dim_parse("m^2")
        assert d.components == {"m": 2}

    def test_negative_power(self):
        d = dim_parse("s^-1")
        assert d.components == {"s": -1}

    def test_complex_physical(self):
        d = dim_parse("kg*m^2/s^2")
        assert d.components == {"kg": 1, "m": 2, "s": -2}

    def test_exchange_rate(self):
        d = dim_parse("GBP/USD")
        assert d.components == {"GBP": 1, "USD": -1}

    def test_per_capita(self):
        d = dim_parse("USD/person")
        assert d.components == {"USD": 1, "person": -1}

    def test_per_capita_per_year(self):
        d = dim_parse("USD/person/year")
        assert d.components == {"USD": 1, "person": -1, "year": -1}

    def test_share_price(self):
        d = dim_parse("USD/share")
        assert d.components == {"USD": 1, "share": -1}

    def test_parens(self):
        d = dim_parse("(USD/person)*year")
        assert d.components == {"USD": 1, "person": -1, "year": 1}

    def test_whitespace_ignored(self):
        d1 = dim_parse("USD / person")
        d2 = dim_parse("USD/person")
        assert d1 == d2

    def test_invalid_raises(self):
        with pytest.raises(ValueError):
            dim_parse("")

    def test_unknown_char_raises(self):
        with pytest.raises(ValueError):
            dim_parse("USD@person")

    def test_items_per_transaction(self):
        d = dim_parse("item/transaction")
        assert d.components == {"item": 1, "transaction": -1}


# ── 3. parse_units_section ────────────────────────────────────────

class TestParseUnitsSection:

    def test_simple_declaration(self):
        lines = ["revenue: [USD]", "headcount: [person]"]
        section = parse_units_section(lines)
        assert section.dim_of("revenue") == DimVec.base("USD")
        assert section.dim_of("headcount") == DimVec.base("person")

    def test_result_declaration(self):
        lines = ["result: [USD/person]"]
        section = parse_units_section(lines)
        assert section.dim_of("result") == dim_parse("USD/person")

    def test_field_declaration(self):
        lines = ["result.total: [USD]"]
        section = parse_units_section(lines)
        assert section.dim_of("result.total") == DimVec.base("USD")

    def test_conversion_declaration(self):
        lines = ["convert GBP to USD: rate"]
        section = parse_units_section(lines)
        assert len(section.conversions) == 1
        c = section.conversions[0]
        assert c.from_dim == DimVec.base("GBP")
        assert c.to_dim == DimVec.base("USD")
        assert c.via_param == "rate"

    def test_comments_ignored(self):
        lines = ["# exchange rate", "rate: [USD/GBP]"]
        section = parse_units_section(lines)
        assert section.dim_of("rate") == dim_parse("USD/GBP")

    def test_dimensionless_declaration(self):
        lines = ["ratio: [1]"]
        section = parse_units_section(lines)
        assert section.dim_of("ratio") == DimVec.dimensionless()


# ── 4. DimChecker end-to-end ──────────────────────────────────────

class TestDimChecker:

    # ── Consistent functions ─────────────────────────────────────

    def test_revenue_per_user_consistent(self):
        source = '''
def revenue_per_user(revenue: float, users: int) -> float:
    """
    axiomander:
        units:
            revenue: [USD]
            users: [person]
            result: [USD/person]
        requires:
            users > 0
    """
    result = revenue / users
    return result
'''
        result = check_dimensions_from_source(source, "revenue_per_user", [
            "revenue: [USD]",
            "users: [person]",
            "result: [USD/person]",
        ])
        assert result.is_consistent

    def test_portfolio_value_consistent(self):
        source = '''
def portfolio_value(shares: int, price: float) -> float:
    result = shares * price
    return result
'''
        result = check_dimensions_from_source(source, "portfolio_value", [
            "shares: [share]",
            "price: [USD/share]",
            "result: [USD]",
        ])
        assert result.is_consistent

    def test_currency_conversion_consistent(self):
        source = '''
def convert_to_usd(amount: float, rate: float) -> float:
    result = amount * rate
    return result
'''
        result = check_dimensions_from_source(source, "convert_to_usd", [
            "amount: [GBP]",
            "rate: [USD/GBP]",
            "result: [USD]",
        ])
        assert result.is_consistent

    def test_accumulation_with_declared_initial(self):
        """Accumulation over unknown list elements -- checker can't infer element dim.
        The initialiser total = 0.0 is dimensionless, which conflicts with result: [USD].
        The correct contract annotates the initial value explicitly."""
        source = '''
def total_revenue(revenues: list) -> float:
    total = 0.0
    for r in revenues:
        total += r
    result = total
    return result
'''
        result = check_dimensions_from_source(source, "total_revenue", [
            "result: [USD]",
        ])
        # The checker correctly flags: total is inferred as [1] (from 0.0 literal),
        # which conflicts with the declared result: [USD].
        # This is expected -- the user needs to annotate the accumulator or
        # initialise with a dimensioned value.
        assert not result.is_consistent
        assert any("USD" in v.message or "1" in v.message for v in result.violations)

    def test_accumulation_no_result_decl_is_consistent(self):
        """Without a result: declaration, there's nothing to violate."""
        source = '''
def total_revenue(revenues: list) -> float:
    total = 0.0
    for r in revenues:
        total += r
    result = total
    return result
'''
        result = check_dimensions_from_source(source, "total_revenue", [])
        assert result.is_consistent

    def test_dimensionless_scaling_consistent(self):
        # Multiplying a USD amount by a dimensionless scale factor
        source = '''
def apply_discount(price: float, discount_rate: float) -> float:
    result = price * (1 - discount_rate)
    return result
'''
        result = check_dimensions_from_source(source, "apply_discount", [
            "price: [USD]",
            "discount_rate: [1]",  # dimensionless
            "result: [USD]",
        ])
        assert result.is_consistent

    def test_per_capita_per_year_consistent(self):
        source = '''
def annual_per_capita(gdp: float, population: int, years: int) -> float:
    result = gdp / population / years
    return result
'''
        result = check_dimensions_from_source(source, "annual_per_capita", [
            "gdp: [USD]",
            "population: [person]",
            "years: [year]",
            "result: [USD/person/year]",
        ])
        assert result.is_consistent

    # ── Violations ───────────────────────────────────────────────

    def test_currency_addition_violation(self):
        """Adding USD and GBP is a dimension error."""
        source = '''
def wrong_add(a: float, b: float) -> float:
    result = a + b
    return result
'''
        result = check_dimensions_from_source(source, "wrong_add", [
            "a: [USD]",
            "b: [GBP]",
            "result: [USD]",
        ])
        assert not result.is_consistent
        assert len(result.violations) >= 1
        v = result.violations[0]
        assert v.lhs_dim == DimVec.base("USD")
        assert v.rhs_dim == DimVec.base("GBP")

    def test_money_plus_people_violation(self):
        """Adding USD and person is a dimension error."""
        source = '''
def nonsense(revenue: float, headcount: int) -> float:
    result = revenue + headcount
    return result
'''
        result = check_dimensions_from_source(source, "nonsense", [
            "revenue: [USD]",
            "headcount: [person]",
            "result: [USD]",
        ])
        assert not result.is_consistent

    def test_wrong_return_dimension(self):
        """Returning [USD/person] when [USD] is declared."""
        source = '''
def wrong_return(revenue: float, headcount: int) -> float:
    result = revenue / headcount
    return result
'''
        result = check_dimensions_from_source(source, "wrong_return", [
            "revenue: [USD]",
            "headcount: [person]",
            "result: [USD]",   # wrong -- should be [USD/person]
        ])
        assert not result.is_consistent

    def test_missing_conversion_violation(self):
        """Assigning GBP to a USD variable without conversion."""
        source = '''
def wrong_assign(amount_gbp: float) -> float:
    result = amount_gbp   # should be amount_gbp * rate first
    return result
'''
        result = check_dimensions_from_source(source, "wrong_assign", [
            "amount_gbp: [GBP]",
            "result: [USD]",
        ])
        assert not result.is_consistent

    def test_augassign_currency_violation(self):
        """Using += with incompatible currencies."""
        source = '''
def wrong_total(a: float, b: float) -> float:
    total = a
    total += b
    result = total
    return result
'''
        result = check_dimensions_from_source(source, "wrong_total", [
            "a: [USD]",
            "b: [GBP]",
            "result: [USD]",
        ])
        assert not result.is_consistent

    # ── No units section -- check is skipped ─────────────────────

    def test_no_units_section_is_consistent(self):
        """Functions without a units: section pass the dimension check."""
        source = '''
def add(a: int, b: int) -> int:
    result = a + b
    return result
'''
        result = check_dimensions_from_source(source, "add", [])
        assert result.is_consistent

    # ── Violation report format ───────────────────────────────────

    def test_violation_report_contains_dims(self):
        source = '''
def wrong(a: float, b: float) -> float:
    result = a + b
    return result
'''
        result = check_dimensions_from_source(source, "wrong", [
            "a: [USD]",
            "b: [GBP]",
            "result: [USD]",
        ])
        report = result.format_report("wrong")
        assert "USD" in report
        assert "GBP" in report
        assert "wrong" in report

    # ── Integration: check-function path ─────────────────────────

    def test_check_function_with_units_violation(self):
        """End-to-end: _verify_function_full returns COUNTEREXAMPLE for dim error
        and does NOT pass the result to coq-lsp or LLM oracles."""
        import os
        os.environ.setdefault(
            "AXIOMANDER_ROOT",
            str(Path(__file__).resolve().parent.parent.parent)
        )
        from oracle.mcp_server import _verify_function_full
        from oracle.reporting import ProofLevel

        source = '''
def wrong_add(revenue: float, headcount: int) -> float:
    """
    axiomander:
        units:
            revenue: [USD]
            headcount: [person]
            result: [USD]
        requires:
            True
        ensures:
            result >= 0
    """
    result = revenue + headcount
    return result
'''
        goal = _verify_function_full(source, "wrong_add", None)
        assert goal is not None
        assert goal.level == ProofLevel.COUNTEREXAMPLE
        assert goal.proof_method == "dim_check"
        assert "USD" in goal.error_detail
        assert "person" in goal.error_detail

    def test_check_function_consistent_units_passes(self):
        """End-to-end: consistent units don't block verification."""
        import os
        os.environ.setdefault(
            "AXIOMANDER_ROOT",
            str(Path(__file__).resolve().parent.parent.parent)
        )
        from oracle.mcp_server import _verify_function_full
        from oracle.reporting import ProofLevel

        source = '''
def revenue_per_user(revenue: float, users: int) -> float:
    """
    axiomander:
        units:
            revenue: [USD]
            users: [person]
            result: [USD/person]
        requires:
            users > 0
        ensures:
            result >= 0
    """
    assert users > 0
    result = revenue / users
    assert result >= 0
    return result
'''
        goal = _verify_function_full(source, "revenue_per_user", None)
        assert goal is not None
        # Dimensionally consistent -- dim_check does not block, WP runs
        assert goal.proof_method != "dim_check"
        assert goal.is_proved()
