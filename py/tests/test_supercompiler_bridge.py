"""Tests for the supercompiler bridge (contract_ir -> p_expr -> supercompile -> Prop).

Coverage:
  - expr_to_p_expr: all supported contract_ir nodes
  - expr_to_p_expr: unsupported nodes return None (negative tests)
  - supercompile_p_expr: constant folding
  - supercompile_p_expr: open variables preserved
  - pipeline: supercompile_contracts=True produces correct IrisProof
  - pipeline: constant boolean triggers replacement
  - pipeline: non-constant keeps original contract
"""

import pytest
from axiomander.supercompiler_bridge import (
    expr_to_p_expr,
    supercompile_p_expr,
    supercompile_contract,
    supercompile_contract_to_prop,
    make_supercompiled_coq_block,
)
from axiomander.oracle.contract_ir import (
    Var, IntLit, BoolLit, BinOp, Logical,
    StrLitExpr, FloatExpr, TupleExpr,
    ImpliesExpr, AllExpr, AnyExpr, LenExpr, FieldAccess,
)
from axiomander.oracle.iris_pipeline import python_to_iris_proof
from axiomander.oracle.iris_proof_gen import FunTable


# ── expr_to_p_expr: supported nodes ─────────────────────────────────

class TestExprToPExpr:
    def test_var(self):
        assert expr_to_p_expr(Var(name="x")) == '(PVar "x"%string)'

    def test_int_positive(self):
        assert expr_to_p_expr(IntLit(value=42)) == '(PVal (PLitInt 42))'

    def test_int_negative(self):
        assert expr_to_p_expr(IntLit(value=-5)) == '(PVal (PLitInt (- 5)))'

    def test_bool_true(self):
        assert expr_to_p_expr(BoolLit(value=True)) == '(PVal (PLitBool true))'

    def test_bool_false(self):
        assert expr_to_p_expr(BoolLit(value=False)) == '(PVal (PLitBool false))'

    def test_string(self):
        assert expr_to_p_expr(StrLitExpr(value="hello")) == '(PVal (PLitString "hello"%string))'

    def test_float(self):
        result = expr_to_p_expr(FloatExpr(value=314))  # Z-encoded: 3.14 * 100
        assert result is not None
        assert 'PLitFloat' in result

    def test_tuple(self):
        result = expr_to_p_expr(TupleExpr(elements=[IntLit(value=1), IntLit(value=2)]))
        assert result is not None
        assert 'PLitTuple' in result
        assert 'PLitInt 1' in result
        assert 'PLitInt 2' in result

    def test_arithmetic_binop(self):
        result = expr_to_p_expr(BinOp(op='+', left=IntLit(value=1), right=IntLit(value=2)))
        assert result == '(PBinOp PAddOp (PVal (PLitInt 1)) (PVal (PLitInt 2)))'

    def test_comparison_binop(self):
        result = expr_to_p_expr(BinOp(op='>', left=Var(name='x'), right=IntLit(value=0)))
        assert result == '(PBinOp PGtOp (PVar "x"%string) (PVal (PLitInt 0)))'

    def test_logical_and(self):
        result = expr_to_p_expr(Logical(op='and', operands=[
            BoolLit(value=True),
            BinOp(op='>', left=Var(name='x'), right=IntLit(value=0)),
        ]))
        assert result is not None
        assert 'PAndOp' in result
        assert 'PLitBool true' in result

    def test_logical_or(self):
        result = expr_to_p_expr(Logical(op='or', operands=[
            BoolLit(value=False),
            BoolLit(value=True),
        ]))
        assert result is not None
        assert 'POrOp' in result

    def test_logical_not(self):
        result = expr_to_p_expr(Logical(op='not', operands=[BoolLit(value=True)]))
        assert result is not None
        assert 'PEqOp' in result
        assert 'PLitBool false' in result

    def test_implies(self):
        from axiomander.oracle.contract_ir import ImpliesExpr
        ante = BinOp(op='>', left=Var(name='x'), right=IntLit(value=0))
        cons = BinOp(op='>', left=Var(name='x'), right=IntLit(value=5))
        result = expr_to_p_expr(ImpliesExpr(left=ante, right=cons))
        assert result is not None
        assert 'POrOp' in result

    def test_len(self):
        result = expr_to_p_expr(LenExpr(name='xs'))
        assert result is not None
        assert 'PLenOp' in result
        assert 'PVar "xs"' in result


# ── expr_to_p_expr: unsupported nodes return None ───────────────────

class TestExprToPExprNegative:
    def test_all_expr(self):
        """AllExpr (forall) has no LambdaA equivalent."""
        result = expr_to_p_expr(AllExpr(var='x', lst='xs',
                                         pred=BoolLit(value=True)))
        assert result is None

    def test_any_expr(self):
        """AnyExpr (exists) has no LambdaA equivalent."""
        result = expr_to_p_expr(AnyExpr(var='x', lst='xs',
                                         pred=BoolLit(value=True)))
        assert result is None

    def test_field_access(self):
        """FieldAccess (model.field projection) has no LambdaA equivalent."""
        result = expr_to_p_expr(FieldAccess(obj='account', field='balance'))
        assert result is None


# ── supercompile_p_expr: constant folding ───────────────────────────

class TestSupercompile:
    def test_literal_addition(self):
        """1 + 2 -> 3"""
        p_expr = '(PBinOp PAddOp (PVal (PLitInt 1)) (PVal (PLitInt 2)))'
        result = supercompile_p_expr(p_expr)
        assert result == 'PVal (PLitInt 3)'

    def test_literal_multiplication(self):
        """3 * 4 -> 12"""
        p_expr = '(PBinOp PMulOp (PVal (PLitInt 3)) (PVal (PLitInt 4)))'
        result = supercompile_p_expr(p_expr)
        assert result == 'PVal (PLitInt 12)'

    def test_comparison_true(self):
        """5 > 3 -> true"""
        p_expr = '(PBinOp PGtOp (PVal (PLitInt 5)) (PVal (PLitInt 3)))'
        result = supercompile_p_expr(p_expr)
        assert result == 'PVal (PLitBool true)'

    def test_comparison_false(self):
        """2 < 1 -> false"""
        p_expr = '(PBinOp PLtOp (PVal (PLitInt 2)) (PVal (PLitInt 1)))'
        result = supercompile_p_expr(p_expr)
        assert result == 'PVal (PLitBool false)'

    def test_nested_constant_folding(self):
        """(1 + 2) > 0 -> 3 > 0 -> true"""
        p_expr = '(PBinOp PGtOp (PBinOp PAddOp (PVal (PLitInt 1)) (PVal (PLitInt 2))) (PVal (PLitInt 0)))'
        result = supercompile_p_expr(p_expr)
        assert result == 'PVal (PLitBool true)'

    def test_and_short_circuit_left_true(self):
        """True AND (3 > 0) -> 3 > 0 -> true (via re-driving)"""
        p_expr = '(PBinOp PAndOp (PVal (PLitBool true)) (PBinOp PGtOp (PVal (PLitInt 3)) (PVal (PLitInt 0))))'
        result = supercompile_p_expr(p_expr)
        # Both operands must be literals for drive_step to fire.
        # supercompile recurses: left is True, right is 3>0.
        # After recursive supercompile: PBinOp PAndOp True True
        # Then drive_step fires: True AND True -> True
        assert result == 'PVal (PLitBool true)'

    def test_open_variable_preserved(self):
        """x > 5 -> unchanged (can't reduce open variable)"""
        p_expr = '(PBinOp PGtOp (PVar "x"%string) (PVal (PLitInt 5)))'
        result = supercompile_p_expr(p_expr)
        assert result is not None
        assert 'PVar' in result
        assert 'x' in result
        assert 'PLitInt 5' in result

    def test_open_variable_addition_preserved(self):
        """x + 0 -> unchanged (driver only handles literal pairs)"""
        p_expr = '(PBinOp PAddOp (PVar "x"%string) (PVal (PLitInt 0)))'
        result = supercompile_p_expr(p_expr)
        assert result is not None
        assert 'PAddOp' in result
        assert 'PVar' in result
        assert 'x' in result

    def test_full_contract_pipeline(self):
        """contract_ir -> p_expr -> supercompile -> constant detection"""
        expr = BinOp(op='>', left=BinOp(op='+', left=IntLit(value=1), right=IntLit(value=2)), right=IntLit(value=0))
        result = supercompile_contract(expr)
        assert result == 'PVal (PLitBool true)'

    def test_contract_to_prop(self):
        """Full pipeline: contract -> supercompile -> Prop string"""
        expr = BinOp(op='>', left=BinOp(op='+', left=IntLit(value=1), right=IntLit(value=2)), right=IntLit(value=0))
        prop = supercompile_contract_to_prop(expr)
        assert prop is not None
        assert 'p_expr_prop_Z' in prop
        assert 'PLitBool true' in prop


# ── make_supercompiled_coq_block ────────────────────────────────────

class TestCoqBlock:
    def test_pre_only(self):
        p_expr = 'PVal (PLitBool true)'
        pre_prop, post_prop, block = make_supercompiled_coq_block(
            p_expr, None, ['x'], {'x': 'int'})
        assert pre_prop == '_super_pre_prop x'
        assert post_prop is None
        assert 'PExprToProp' in block
        assert 'Definition _super_pre_body' in block
        assert 'Definition _super_pre_prop' in block
        assert 'String.eqb "x"%string' in block

    def test_post_only(self):
        p_expr = 'PVal (PLitInt 42)'
        pre_prop, post_prop, block = make_supercompiled_coq_block(
            None, p_expr, ['x'], {'x': 'int'})
        assert pre_prop is None
        assert post_prop == '_super_post_prop x v'
        assert 'Definition _super_post_body' in block

    def test_both(self):
        pre_prop, post_prop, block = make_supercompiled_coq_block(
            'PVal (PLitBool true)', 'PVal (PLitInt 42)',
            ['x', 'y'], {'x': 'int', 'y': 'bool'})
        assert pre_prop == '_super_pre_prop x y'
        assert post_prop == '_super_post_prop x y v'
        assert 'Definition _super_pre_body' in block
        assert 'Definition _super_post_body' in block

    def test_no_params(self):
        pre_prop, post_prop, block = make_supercompiled_coq_block(
            'PVal (PLitBool false)', None, [], {})
        assert pre_prop.strip() == '_super_pre_prop'
        assert block is not None


# ── Pipeline integration tests ──────────────────────────────────────

class TestPipelineIntegration:
    def test_supercompile_contracts_flag_accepted(self):
        """Verify the flag is accepted and produces valid output."""
        source = '''
def echo(x: int) -> int:
    assert 1 + 2 > 0
    return x + 1
'''
        table = FunTable({})
        proof = python_to_iris_proof(
            source, table, func_name='echo',
            supercompile_contracts=True, _cwd='.')
        result = proof.emit_exn()
        assert 'Lemma echo_correct' in result
        assert 'WPE' in result
        # Should have supercompiled block (constant-folded precondition)
        assert proof.supercompiled_block != ''
        assert '_super_pre_body' in proof.supercompiled_block

    def test_constant_pre_triggers_replacement(self):
        """When precondition reduces to constant True, it replaces original."""
        source = '''
def const_pre(x: int) -> int:
    assert 1 + 2 > 0
    return x
'''
        table = FunTable({})
        proof = python_to_iris_proof(
            source, table, func_name='const_pre',
            supercompile_contracts=True, _cwd='.')
        assert proof.supercompiled_pre is not None
        assert '_super_pre_prop' in proof.supercompiled_pre

    def test_non_constant_does_not_replace(self):
        """When precondition cannot be reduced, original is kept."""
        source = '''
def open_pre(x: int) -> int:
    assert x > 0
    return x
'''
        table = FunTable({})
        proof = python_to_iris_proof(
            source, table, func_name='open_pre',
            supercompile_contracts=True, _cwd='.')
        assert proof.supercompiled_pre is None
        # Original precondition should still be present
        result = proof.emit_exn()
        assert '(0 <? x) = true' in result or 'x >' in result or '0 <? x' in result

    def test_no_contract_at_all(self):
        """Function with no asserts still works fine."""
        source = '''
def no_contract(x: int) -> int:
    return x + 1
'''
        table = FunTable({})
        proof = python_to_iris_proof(
            source, table, func_name='no_contract',
            supercompile_contracts=True, _cwd='.')
        result = proof.emit_exn()
        assert 'Lemma no_contract_correct' in result

    def test_flag_off_produces_no_supercompilation(self):
        """When flag is False, no supercompiled block is generated."""
        source = '''
def normal(x: int) -> int:
    assert 1 + 2 > 0
    return x
'''
        table = FunTable({})
        proof = python_to_iris_proof(
            source, table, func_name='normal',
            supercompile_contracts=False, _cwd='.')
        assert proof.supercompiled_block == ''
        assert proof.supercompiled_pre is None
