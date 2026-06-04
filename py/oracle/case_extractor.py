"""
Case extractor for case-dispatch verification.

Walks an IMP IR tree and extracts a list of CaseBranch pairs.
Each pair records the path conditions (ImpBExp conjunction) and
the linear assignment sequence (list of ImpCom) for one execution path.

The extractor only applies to decision-tree bodies -- no CWhile/CFor
inside the branching structure.  This enables ground SMT verification
per case rather than induction.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, Union

from .imp_ir import (
    ImpBExp,
    ImpBNot,
    ImpCom,
    ImpCSkip,
    ImpCSeq,
    ImpCIf,
    ImpCWhile,
    ImpCCall,
    ImpCTry,
    ImpCListNew,
    ImpCListAppend,
    ImpCListPop,
    ImpCListPopTo,
    ImpCSetAdd,
    ImpCSetDiscard,
    ImpCListSet,
    ImpCDictSet,
    ImpCDictGet,
    ImpCDictEnsureList,
    ImpCDictAppend,
    ImpCDictAppendKv,
    ImpCAss,
    ImpCAssume,
    ImpCHavoc,
    ImpCRaise,
)


@dataclass
class CaseBranch:
    """One execution path through a decision tree.

    path_conditions: Conjunction of ImpBExp conditions that must hold
        for execution to reach this branch (outermost first).
    assignments:     Linear sequence of ImpCom commands executed in this
        branch (no nested CIf/CWhile -- the tree has been flattened).
    """

    path_conditions: list[ImpBExp] = field(default_factory=list)
    assignments: list[ImpCom] = field(default_factory=list)

    def condition_conjunct(self) -> Optional[ImpBExp]:
        """Return the conjunction of all path conditions, or None if empty."""
        if not self.path_conditions:
            return None
        result = self.path_conditions[0]
        for c in self.path_conditions[1:]:
            from .imp_ir import ImpBAnd
            result = ImpBAnd(left=result, right=c)  # type: ignore[arg-type]
        return result


def extract_cases(com: ImpCom) -> list[CaseBranch]:
    """Extract case branches from an IMP IR decision tree.

    Walks CIf/CSeq nodes.  Any branch that contains CWhile/CFor
    is rejected (raises ValueError) because loops require induction.
    """
    return _extract(com, [])


def _extract(com: ImpCom, conditions: list[ImpBExp]) -> list[CaseBranch]:
    if isinstance(com, ImpCIf):
        then_conds = list(conditions) + [com.condition]
        else_conds = list(conditions) + [ImpBNot(operand=com.condition)]

        _reject_loops(com.then_branch, then_conds)
        _reject_loops(com.else_branch, else_conds)

        then_cases = _extract(com.then_branch, then_conds)
        else_cases = _extract(com.else_branch, else_conds)
        return then_cases + else_cases

    if isinstance(com, ImpCSeq):
        # Collect all assignments from the flat command list.
        # If any nested command is itself a CIf, recurse into it
        # with the accumulated assignments so far as a prefix.
        return _extract_seq(com.commands, conditions)

    # Leaf: any other command type
    return [CaseBranch(path_conditions=list(conditions), assignments=[com])]


def _extract_seq(
    commands: list[ImpCom], conditions: list[ImpBExp]
) -> list[CaseBranch]:
    """Walk a sequence of commands, collecting assignments up to any CIf.

    When we hit a CIf, we recurse into both branches with the
    accumulated prefix assignments prepended to each branch's
    assignment list.
    """
    prefix: list[ImpCom] = []

    for i, cmd in enumerate(commands):
        if isinstance(cmd, ImpCIf):
            # Recurse into both branches.  Each branch gets the
            # prefix so far plus its own assignments.
            then_conds = list(conditions) + [cmd.condition]
            else_conds = list(conditions) + [ImpBNot(operand=cmd.condition)]

            _reject_loops(cmd.then_branch, then_conds)
            _reject_loops(cmd.else_branch, else_conds)

            then_inner = _extract(cmd.then_branch, then_conds)
            else_inner = _extract(cmd.else_branch, else_conds)

            # Any remaining commands after this CIf belong to ALL branches.
            # Recurse into the remaining sequence for each branch.
            remaining = commands[i + 1 :]

            if remaining:
                # Collect remaining into a CSeq and recurse
                remaining_com: ImpCom = ImpCSeq(commands=list(remaining))
                then_cases = []
                for tb in then_inner:
                    nested = _extract_seq(
                        tb.assignments + [remaining_com] if not isinstance(tb.assignments[-1], ImpCSeq)
                        else tb.assignments[:-1] + [ImpCSeq(commands=list(tb.assignments[-1].commands) + list(remaining))],
                        tb.path_conditions,
                    )
                    then_cases.extend(nested) if nested else then_cases.append(tb)
                # Simpler: treat remaining as postfix for each branch
                result: list[CaseBranch] = []
                for tb in then_inner:
                    result.append(CaseBranch(
                        path_conditions=list(tb.path_conditions),
                        assignments=list(prefix) + list(tb.assignments),
                    ))
                for eb in else_inner:
                    result.append(CaseBranch(
                        path_conditions=list(eb.path_conditions),
                        assignments=list(prefix) + list(eb.assignments),
                    ))
                # Now recurse remaining into each result
                final: list[CaseBranch] = []
                for br in result:
                    final.extend(_extend_with_seq(br, remaining))
                return final
            else:
                result = []
                for tb in then_inner:
                    result.append(CaseBranch(
                        path_conditions=list(tb.path_conditions),
                        assignments=list(prefix) + list(tb.assignments),
                    ))
                for eb in else_inner:
                    result.append(CaseBranch(
                        path_conditions=list(eb.path_conditions),
                        assignments=list(prefix) + list(eb.assignments),
                    ))
                return result

        if isinstance(cmd, ImpCSeq):
            # Flatten nested CSeq
            inner = _extract_seq(list(cmd.commands), list(conditions))
            # Prepend prefix to each result
            for br in inner:
                br.assignments = list(prefix) + list(br.assignments)
            # Continue with remaining commands
            remaining = commands[i + 1 :]
            if remaining:
                result = []
                for br in inner:
                    result.extend(_extend_with_seq(br, remaining))
                return result
            return inner

        # Linear command: accumulate
        if not isinstance(cmd, ImpCSkip):
            prefix.append(cmd)

    # No CIf found: the whole sequence is linear
    return [CaseBranch(path_conditions=list(conditions), assignments=list(prefix))]


def _extend_with_seq(
    branch: CaseBranch, remaining: list[ImpCom]
) -> list[CaseBranch]:
    """Extend a branch's assignments with remaining commands.

    If remaining contains a CIf, we need to split again.
    """
    remaining_com: ImpCom = ImpCSeq(commands=list(remaining))
    has_if = any(isinstance(c, ImpCIf) for c in remaining)

    if not has_if:
        return [CaseBranch(
            path_conditions=list(branch.path_conditions),
            assignments=list(branch.assignments) + list(remaining),
        )]

    # Contains CIf: recurse with the branch's conditions and prefix
    inner = _extract_seq(list(remaining), list(branch.path_conditions))
    for br in inner:
        br.assignments = list(branch.assignments) + list(br.assignments)
    return inner


# ── Loop rejection ──────────────────────────────────────────────────

def _has_loops(com: ImpCom) -> bool:
    """Check if an IMP command tree contains any CWhile."""
    if isinstance(com, ImpCWhile):
        return True
    if isinstance(com, ImpCSeq):
        return any(_has_loops(c) for c in com.commands)
    if isinstance(com, ImpCIf):
        return _has_loops(com.then_branch) or _has_loops(com.else_branch)
    if isinstance(com, ImpCTry):
        return _has_loops(com.body) or _has_loops(com.handler)
    return False


def _reject_loops(com: ImpCom, conditions: list[ImpBExp]) -> None:
    """Raise ValueError if any branch contains a CWhile."""
    if _has_loops(com):
        cond_text = " /\\ ".join(c.to_coq() for c in conditions[:3])
        raise ValueError(
            f"Case-dispatch verification does not support loops inside branches.\n"
            f"  Path conditions: {cond_text if cond_text else '(none)'}\n"
            f"  Branch contains CWhile -- needs induction, not case analysis."
        )


# ── Branch validation ───────────────────────────────────────────────

def validate_mutual_exclusivity(cases: list[CaseBranch]) -> Optional[str]:
    """Check that branch conditions are pairwise mutually exclusive.

    Returns None if all pairs are exclusive, or a description of
    overlapping branches.

    This is a heuristic reachability check -- it only considers
    BEq(x, literal) and BIsVZ/BIsVString conditions.  Full SMT-based
    exclusivity checking would require a solver.
    """
    for i in range(len(cases)):
        for j in range(i + 1, len(cases)):
            conflict = _conditions_conflict(
                cases[i].path_conditions, cases[j].path_conditions
            )
            if conflict:
                return (
                    f"Branches {i} and {j} may overlap: "
                    f"both satisfy condition sets without conflict.\n"
                    f"  Branch {i}: {' /\\ '.join(c.to_coq() for c in cases[i].path_conditions)}\n"
                    f"  Branch {j}: {' /\\ '.join(c.to_coq() for c in cases[j].path_conditions)}"
                )
    return None


def _conditions_conflict(
    conds_a: list[ImpBExp], conds_b: list[ImpBExp]
) -> bool:
    """Heuristic: do two condition sets appear to conflict?

    Looks for:
      - Opposite BNot (X vs ~X)
      - BEq(x, a) vs BEq(x, b) where a != b
      - BIsVZ vs BNot(BIsVZ)
    Returns True if we did NOT find a conflict (i.e., they might overlap).
    """
    from .imp_ir import ImpBEq, ImpBTrue, ImpBFalse

    for ca in conds_a:
        for cb in conds_b:
            # ca = BNot(cb) or cb = BNot(ca)?
            if isinstance(ca, ImpBNot) and _bexp_equal(ca.operand, cb):
                return False  # they conflict, good
            if isinstance(cb, ImpBNot) and _bexp_equal(cb.operand, ca):
                return False

            # ca = BEq(x, a), cb = BEq(x, b), a.to_coq() != b.to_coq()
            if isinstance(ca, ImpBEq) and isinstance(cb, ImpBEq):
                if (
                    ca.left.to_coq() == cb.left.to_coq()
                    and ca.right.to_coq() != cb.right.to_coq()
                ):
                    return False  # x = 1 vs x = 2 -- conflict

    return True  # no conflict found -- might overlap


def _bexp_equal(a: ImpBExp, b: ImpBExp) -> bool:
    """Structural equality of two ImpBExp nodes."""
    return a.to_coq() == b.to_coq()


# ── Case partitioning ───────────────────────────────────────────────

def partition_branches(cases: list[CaseBranch]) -> dict[str, CaseBranch]:
    """Partition branches by a descriptive key derived from path conditions.

    Uses the first BEq in each branch's conditions (if any) as the key.
    Falls back to the branch index for branches without discriminative BEq.

    Returns: {key: CaseBranch} where key is the discriminator value.
    """
    from .imp_ir import ImpBEq, ImpBTrue

    result: dict[str, CaseBranch] = {}
    for i, br in enumerate(cases):
        key = None
        for cond in br.path_conditions:
            if isinstance(cond, ImpBEq):
                # Use the RHS value as the discriminator
                rhs = cond.right.to_coq()
                key = rhs
                break
        if key is None:
            key = f"_branch_{i}"
        result[key] = br
    return result
