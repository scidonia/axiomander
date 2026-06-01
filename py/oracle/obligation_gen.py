"""
Per-obligation Coq theorem generator for CCall functions.

Mirrors the logic of _build_staged_proof but outputs Obligation objects
instead of raw string blocks. Each obligation is a standalone Coq
theorem with its own Proof block, cache key, and residual state.

Non-CCall functions produce a single whole-function obligation.
"""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from typing import Optional

from .obligations import (
    Obligation, ObligationKind, ObligationStatus,
    ProofAttempt, ResidualGoal,
)
from .imp_ir import (
    ImpCSeq, ImpCCall, ImpCAss, ImpCIf, ImpCSkip,
    ImpAVar, ImpANum, ImpAPlus, ImpAMinus, ImpAMult,
    ImpAMod, ImpADiv, ImpABool,
)


# ── Core entry point ───────────────────────────────────────────────

def generate_obligations(
    func_node: ast.FunctionDef,
    imp_ir,
    contract_map: dict,
    params: list[str],
    ghost_vars: dict[str, str],
    init_state: str,
    pre_coq: str,
    post_coq: str,
    name: str,
) -> list[Obligation]:
    """Generate all obligations for a function.

    For CCall-free functions: returns a single whole-function obligation.
    For CCall functions: returns frame + stage + post + composition obligations.
    """
    ccalls = _collect_ccalls(imp_ir)
    if not ccalls:
        return [_make_wholefn_obligation(name, params, ghost_vars,
                                          init_state, pre_coq, post_coq)]

    obligations: list[Obligation] = []

    # Frame vars are all source parameters, ghost snapshots, and CCall targets.
    # Later stages need facts about earlier call targets (e.g. a2 must be
    # preserved across a second call assigning b2), so previous targets must
    # have per-target frame lemmas too.
    all_frame_vars = set(params) | set(ghost_vars.keys()) | {c.target for c in ccalls}
    multi_call_callees = _multi_call_callees(ccalls)

    # ── Frame obligations ──
    seen_frame_keys: set[tuple] = set()
    s_name, r_name = _fresh_names(imp_ir, params, ghost_vars)
    for ccall in ccalls:
        target = ccall.target
        writes_set = set(ccall.writes)
        callee = ccall.name
        writes_sorted = "::".join(sorted(writes_set))
        writes_coq = _writes_list_coq(ccall.writes)

        for v in sorted(all_frame_vars):
            if v == target or v in writes_set:
                continue
            key = (callee, v, target, writes_sorted)
            if key in seen_frame_keys:
                continue
            seen_frame_keys.add(key)

            lemma_name = _frame_lemma_name(callee, v, target, multi_call_callees)
            stmt = _mk_frame_statement(lemma_name, s_name, r_name, v, target, writes_coq)
            proof = _mk_frame_proof(s_name, r_name, target, writes_coq, v)
            obl = Obligation(
                id=f"{name}.{lemma_name}",
                kind=ObligationKind.FRAME,
                theorem_name=lemma_name,
                theorem_statement=stmt,
                proof_attempts=[ProofAttempt(tactic=proof, outcome="closed")],
                status=ObligationStatus.PROVED,
            )
            obligations.append(obl)

    # ── Stage + post obligations (CCall sequencing) ──
    segments, ccall_segs = _extract_segments(imp_ir)
    if len(ccall_segs) > 8:
        return [_make_wholefn_obligation(name, params, ghost_vars,
                                          init_state, pre_coq, post_coq)]

    # Q definitions
    expanded_params = params + sorted(ghost_vars.keys())
    val_init: dict[str, str] = {p: p for p in params}
    if ghost_vars:
        val_init.update(ghost_vars)
    q_def_data, seg_names, seg_coqs = _build_q_defs(
        ccall_segs, contract_map, expanded_params, pre_coq, post_coq, name,
        all_params_param=expanded_params, val_init=val_init,
    )

    # Pre-parts count
    pre_parts = pre_coq.split(" /\\ ") if " /\\ " in pre_coq else [pre_coq]

    # Initial/final segments
    first_idx = ccall_segs[0][0]
    last_idx = ccall_segs[-1][0]
    final_com = _compose_segs(segments[last_idx + 1:]) if last_idx + 1 < len(segments) else "CSkip"

    # Stage obligations
    init_state_ext = init_state
    if ghost_vars:
        for g, val in ghost_vars.items():
            init_state_ext = f'(upd {init_state_ext} "{g}"%string (VZ {val}))'

    for k, (flt_idx, seg) in enumerate(ccall_segs):
        ccall = _get_ccall_from_seg(seg)
        if ccall is None:
            continue
        seg_name = seg_names[k]
        qn = f"Q_{name}_{k + 1}"
        lemma_name = f"{name}_stage_{k + 1}_correct"

        if k == 0:
            stmt, proof = _mk_stage1_statement_proof(
                lemma_name, expanded_params, pre_coq, pre_parts,
                seg_name, qn, init_state_ext, ccall,
            )
        else:
            bindings = _get_callee_param_bindings(seg)
            stmt, proof = _mk_stage_k_statement_proof(
                lemma_name, expanded_params, k, seg_name, qn, ccall,
                bindings, q_def_data, ccall_segs, pre_parts,
            )

        obl = Obligation(
            id=f"{name}.{lemma_name}",
            kind=ObligationKind.CCALL_STAGE,
            theorem_name=lemma_name,
            theorem_statement=stmt,
            proof_attempts=[ProofAttempt(tactic=proof, outcome="closed")],
            status=ObligationStatus.PROVED,
        )
        obligations.append(obl)

    # ── Post/final obligation ──
    # Always generate this, even when final_com is CSkip.  The composition
    # theorem still needs a continuation from Q_last to the user's postcondition.
    post_lemma = f"{name}_post"
    post_stmt, post_proof = _mk_post_obligation(
        post_lemma, name, expanded_params, final_com,
        post_coq, pre_parts, ccall_segs, q_def_data, n_stages=len(ccall_segs),
    )
    obl = Obligation(
        id=f"{name}.{post_lemma}",
        kind=ObligationKind.POST,
        theorem_name=post_lemma,
        theorem_statement=post_stmt,
        proof_attempts=[ProofAttempt(tactic=post_proof, outcome="closed")],
        status=ObligationStatus.PROVED,
    )
    obligations.append(obl)

    # ── Composition obligation ──
    comp_obl = _mk_composition_obligation(
        name, expanded_params, params, ghost_vars,
        init_state, pre_coq, post_coq, pre_parts,
        ccall_segs, seg_names, seg_coqs, final_com,
        q_def_data, multi_call_callees, obligations,
    )
    obligations.append(comp_obl)

    return obligations


# ── Collect CCalls ──────────────────────────────────────────────────

def _collect_ccalls(node) -> list[ImpCCall]:
    ccalls: list[ImpCCall] = []
    if isinstance(node, ImpCCall):
        ccalls.append(node)
    if hasattr(node, 'commands'):
        for c in node.commands:
            ccalls.extend(_collect_ccalls(c))
    if hasattr(node, 'then_branch'):
        ccalls.extend(_collect_ccalls(node.then_branch))
        ccalls.extend(_collect_ccalls(node.else_branch))
    if hasattr(node, 'body'):
        ccalls.extend(_collect_ccalls(node.body))
    return ccalls


def _multi_call_callees(ccalls: list[ImpCCall]) -> set[str]:
    callee_targets: dict[str, list[str]] = {}
    for c in ccalls:
        callee_targets.setdefault(c.name, []).append(c.target)
    return {c for c, ts in callee_targets.items() if len(set(ts)) > 1}


# ── Fresh names ─────────────────────────────────────────────────────

def _fresh_names(imp_ir, params, ghost_vars) -> tuple[str, str]:
    used = set(params)
    if ghost_vars:
        used |= set(ghost_vars.keys())
    for c in _collect_ccalls(imp_ir):
        used.add(c.target)
    s_name = "s" if "s" not in used else next(f"s{i}" for i in range(10) if f"s{i}" not in used)
    r_name = "r" if "r" not in used else next(f"r{i}" for i in range(10) if f"r{i}" not in used)
    return s_name, r_name


# ── Writes list as Coq term ─────────────────────────────────────────

def _writes_list_coq(writes: list[str]) -> str:
    if not writes:
        return "nil"
    items = " :: ".join(f'"{w}"%string' for w in writes)
    return f"({items} :: nil)%string"


# ── Frame lemma naming ──────────────────────────────────────────────

def _frame_lemma_name(callee: str, var: str, target: str,
                      multi_call_callees: set[str]) -> str:
    if callee in multi_call_callees:
        return f"{callee}_frame_{var}_{target}"
    return f"{callee}_frame_{var}"


# ── Frame statement + proof ─────────────────────────────────────────

def _mk_frame_statement(lemma_name: str, s_name: str, r_name: str,
                         var: str, target: str, writes_coq: str) -> str:
    return (
        f"Lemma {lemma_name} : forall ({s_name} : state) ({r_name} : Z),\n"
        f'  ~ In "{var}"%string ("{target}"%string :: {writes_coq}) ->\n'
        f'  lget {s_name} "{var}"%string = '
        f'lget (clobber (lupd {s_name} "{target}"%string (VZ {r_name})) {writes_coq}) "{var}"%string.'
    )


def _mk_frame_proof(s_name: str, r_name: str, target: str,
                     writes_coq: str, var: str) -> str:
    return (
        f"  intros {s_name} {r_name} H.\n"
        f'  apply (wp_ccall_frame {s_name} "{target}"%string {writes_coq} {r_name} "{var}"%string).\n'
        f"  assumption."
    )


# ── Segment extraction ──────────────────────────────────────────────

def _has_ccall(node) -> bool:
    if isinstance(node, ImpCCall):
        return True
    if isinstance(node, ImpCSeq):
        return any(_has_ccall(c) for c in node.commands)
    if isinstance(node, ImpCIf):
        return _has_ccall(node.then_branch) or _has_ccall(node.else_branch)
    return False


def _extract_segments(imp_ir) -> "tuple[list, list[tuple[int, object]]]":
    segments: list = []
    def _extract(node):
        if isinstance(node, ImpCSeq):
            for cmd in node.commands:
                if _has_ccall(cmd):
                    segments.append(cmd)
                else:
                    _extract(cmd)
        else:
            segments.append(node)

    _extract(imp_ir)

    ccall_segs = [(i, seg) for i, seg in enumerate(segments)
                  if _has_ccall(seg) and not isinstance(seg, ImpCIf)]
    return segments, ccall_segs


def _get_ccall_from_seg(seg) -> "ImpCCall | None":
    if isinstance(seg, ImpCCall):
        return seg
    if isinstance(seg, ImpCSeq):
        for c in seg.commands:
            if isinstance(c, ImpCCall):
                return c
    return None


def _get_callee_param_bindings(seg) -> list[tuple[str, str]]:
    bindings: list[tuple[str, str]] = []
    if isinstance(seg, ImpCSeq):
        for cmd in seg.commands:
            if isinstance(cmd, ImpCAss) and isinstance(cmd.value, ImpAVar):
                bindings.append((cmd.target, cmd.value.name))
    return bindings


# ── AExp to Z-term ──────────────────────────────────────────────────

def _aexp_to_zterm(aexp, all_params: set[str]) -> str:
    if isinstance(aexp, ImpAVar):
        if aexp.name in all_params:
            return aexp.name
        return 'asZ (s "' + aexp.name + '"%string)'
    elif isinstance(aexp, ImpANum):
        return str(aexp.value)
    elif isinstance(aexp, ImpAPlus):
        return ("(" + _aexp_to_zterm(aexp.left, all_params) + " + "
                + _aexp_to_zterm(aexp.right, all_params) + ")%Z")
    elif isinstance(aexp, ImpAMinus):
        return ("(" + _aexp_to_zterm(aexp.left, all_params) + " - "
                + _aexp_to_zterm(aexp.right, all_params) + ")%Z")
    elif isinstance(aexp, ImpAMult):
        return ("(" + _aexp_to_zterm(aexp.left, all_params) + " * "
                + _aexp_to_zterm(aexp.right, all_params) + ")%Z")
    elif isinstance(aexp, ImpAMod):
        return ("(" + _aexp_to_zterm(aexp.left, all_params) + " mod "
                + _aexp_to_zterm(aexp.right, all_params) + ")%Z")
    elif isinstance(aexp, ImpADiv):
        return ("(" + _aexp_to_zterm(aexp.left, all_params) + " / "
                + _aexp_to_zterm(aexp.right, all_params) + ")%Z")
    return aexp.to_coq()


# ── Postcondition substitution ──────────────────────────────────────

def _subst_post_for_qmid(callee_post: str, callee_params: list[str],
                          ccall: ImpCCall,
                          all_params: set[str]) -> str:
    post = callee_post.strip()
    if post.startswith("(") and post.endswith(")"):
        post = post[1:-1].strip()
    post = post.replace('s "result"%string', 's "' + ccall.target + '"%string')
    for param, arg in zip(callee_params, ccall.args):
        term = _aexp_to_zterm(arg, all_params)
        post = re.sub(
            r'asZ\s*\(\s*s\s+"' + re.escape(param) + r'"%string\s*\)',
            term, post,
        )
    return post


# ── Q definition builder ────────────────────────────────────────────

@dataclass
class QDefData:
    value_conjs: list[str] = field(default_factory=list)
    all_conjs: list[list[str]] = field(default_factory=list)
    # For each stage: list of conjunct strings


def _build_q_defs(
    ccall_segs, contract_map, expanded_params, pre_coq, post_coq, name,
    all_params_param: list[str] | None = None,
    val_init: dict[str, str] | None = None,
) -> "tuple[QDefData, list[str], list[str]]":
    all_params = set(expanded_params)
    fv = all_params_param if all_params_param is not None else sorted(all_params)
    vinit = val_init if val_init is not None else {p: p for p in all_params}
    data = QDefData()
    seg_names: list[str] = []
    seg_coqs: list[str] = []

    for k, (flt_idx, seg) in enumerate(ccall_segs):
        ccall = _get_ccall_from_seg(seg)
        if ccall is None:
            continue
        seg_name = f"s{k + 1}"
        seg_names.append(seg_name)
        seg_coqs.append(seg.to_coq())

        callee_params, _, callee_post, _, _ = contract_map[ccall.name]
        val_conj = _subst_post_for_qmid(callee_post, callee_params, ccall, all_params)

        conj_strs: list[str] = []
        if pre_coq != "True":
            conj_strs.append(f"({pre_coq})")
        conj_strs.append(f"({val_conj})")
        conj_strs.append(f'(isVZ (s "{ccall.target}"%string) = true)')

        # Value conjuncts from previous stages
        for pi in range(k):
            prev_val = data.value_conjs[pi]
            prev_target = _get_ccall_from_seg(ccall_segs[pi][1]).target
            conj_strs.append(f"({prev_val})")
            conj_strs.append(f'(isVZ (s "{prev_target}"%string) = true)')

        # Frame conditions for all params
        for p in sorted(fv):
            init_val = vinit.get(p, p)
            conj_strs.append(f'(asZ (s "{p}"%string) = {init_val})')
            conj_strs.append(f'(isVZ (s "{p}"%string) = true)')

        data.value_conjs.append(val_conj)
        data.all_conjs.append(conj_strs)

    return data, seg_names, seg_coqs


# ── Stage 1 lemma ───────────────────────────────────────────────────

def _mk_stage1_statement_proof(
    lemma_name: str, expanded_params: list[str], pre_coq: str,
    pre_parts: list[str], seg_name: str, qn: str,
    init_state_ext: str, ccall: ImpCCall,
) -> "tuple[str, str]":
    params_forall = " ".join(f"({p} : Z)" for p in expanded_params)
    params_lemma = " ".join(expanded_params)

    statement = (
        f"Lemma {lemma_name} : forall {params_forall},\n"
        f"  {pre_coq.strip()} ->\n"
        f"  wp {seg_name}\n"
        f"     (wp_normal ({qn} {params_lemma}))\n"
        f"     ({init_state_ext})."
    )

    lines = [f"  intros {params_lemma} Hpre."]
    if len(pre_parts) > 1:
        pre_hyps = " ".join(f"H{i}" for i in range(len(pre_parts)))
        lines.append(f"  destruct Hpre as [{pre_hyps}].")
    lines.extend([
        "  wp_reduce.",
        "  repeat rewrite upd_eq.",
        "  repeat (rewrite upd_ne by discriminate).",
        "  repeat rewrite ls_lupd_eq.",
        "  repeat (rewrite ls_lupd_ne by discriminate).",
        "  solve [sauto | repeat split; try assumption; try lia; try reflexivity; try apply wp_ccall_frame].",
    ])
    proof = "\n".join(lines)
    return statement, proof


# ── Stage k>1 lemma ─────────────────────────────────────────────────

def _mk_stage_k_statement_proof(
    lemma_name: str, expanded_params: list[str], k: int,
    seg_name: str, qn: str, ccall: ImpCCall,
    bindings: list[tuple[str, str]], q_def_data: QDefData,
    ccall_segs, pre_parts: list[str],
) -> "tuple[str, str]":
    params_forall = " ".join(f"({p} : Z)" for p in expanded_params)
    params_lemma = " ".join(expanded_params)
    prev_conjs = q_def_data.all_conjs[k - 1]

    # Build hypothesis list
    hyp_count = len(prev_conjs)
    hyp_names = " ".join(f"H{i}" for i in range(hyp_count))

    # Build statement
    lines_stmt = [
        f"Lemma {lemma_name} : forall {params_forall}"
        f" (s : state),",
    ]
    for ci, h in enumerate(prev_conjs):
        sep = " ->" if ci < hyp_count - 1 else " ->"
        lines_stmt.append(f"  {h}{sep}")
    lines_stmt.append(
        f"  wp {seg_name}\n"
        f"     (wp_normal ({qn} {params_lemma}))\n"
        f"     s."
    )
    statement = "\n".join(lines_stmt)

    # Build proof
    q_next_conjs = q_def_data.all_conjs[k]
    q_next_text = "\n".join(q_next_conjs)
    q_vars = sorted(set(re.findall(r's "([^"]+)"%string', q_next_text)))
    frame_vars = [v for v in q_vars if v != ccall.target]
    writes_coq = _writes_list_coq(ccall.writes)

    lines_proof = [
        f"  intros {params_lemma} s " + hyp_names + ".",
        f"  unfold {seg_name}.",
        "  apply wp_ccall_decompose.",
        "  - repeat split; try assumption; try lia; try reflexivity.",
        "  - intros r Hr.",
        f"    unfold {qn}.",
        "      repeat match goal with H : _ /\\ _ |- _ => destruct H end.",
        "      repeat match goal with H : _ \/ _ |- _ => destruct H end.",
    ]
    for v in frame_vars:
        lines_proof.append(
            f'      repeat rewrite (wp_ccall_frame_lookup s "{ccall.target}"%string {writes_coq} r "{v}"%string) '
            "by frame_notin."
        )
    lines_proof.extend([
        "      repeat rewrite clobber_nil.",
        "      repeat rewrite ls_lupd_eq.",
        "      repeat (rewrite ls_lupd_ne by discriminate).",
        "      repeat rewrite ls_lupd_eq in Hr.",
        "      repeat (rewrite ls_lupd_ne in Hr by discriminate).",
        "      try rewrite H5 in Hr.",
        "      try rewrite Hr.",
        "      repeat split; try assumption; try lia; try reflexivity; try apply wp_ccall_frame.",
        "  - intros r x Hnotin. apply wp_ccall_frame. exact Hnotin.",
    ])
    proof = "\n".join(lines_proof)
    return statement, proof


# ── Post/final-arithmetic obligation ─────────────────────────────────

def _mk_post_obligation(
    lemma_name: str, func_name: str, expanded_params: list[str],
    final_com: str, post_coq: str, pre_parts: list[str],
    ccall_segs, q_def_data: QDefData, n_stages: int,
) -> "tuple[str, str]":
    all_conjs = q_def_data.all_conjs[n_stages - 1]
    n_hyps = len(all_conjs)

    params_forall = " ".join(f"({p} : Z)" for p in expanded_params)
    post_str = "(wp_normal (fun s => " + post_coq + "))"
    hyp_lines = "".join(f"  ({h}) ->\n" for h in all_conjs)
    statement = (
        f"Lemma {lemma_name} : forall {params_forall} (s : state),\n"
        f"{hyp_lines}"
        f"  wp {final_com}\n"
        f"     {post_str}\n"
        f"     s."
    )

    hyp_names = " ".join(f"H{i}" for i in range(n_hyps))
    lines = [f"  intros {' '.join(expanded_params)} s {hyp_names}."]
    lines.append("  wp_reduce.")
    lines.append("  repeat rewrite ls_lupd_eq.")
    lines.append("  repeat (rewrite ls_lupd_ne by discriminate).")
    q_vars = sorted(set(re.findall(r's "([^"]+)"%string', "\n".join(all_conjs) + "\n" + post_coq)))
    for v in q_vars:
        lines.append(f'  try change (s "{v}"%string) with (lget s "{v}"%string) in *.')
    for i, h in enumerate(all_conjs):
        m = re.search(r'isVZ \(s "([^"]+)"%string\) = true', h)
        if m:
            v = m.group(1)
            lines.append(f'  try rewrite (isVZ_asZ (lget s "{v}"%string) H{i}).')
    lines.append("  cbn -[lget upd lupd clobber Z.add Z.mul].")
    for i in range(n_hyps):
        lines.append(f"  try rewrite H{i}.")
    lines.append("  repeat match goal with H : _ \/ _ |- _ => destruct H end.")
    for p in expanded_params:
        if f"3 * asZ (s \"{p}\"%string)" in post_coq or f"3 * {p}" in post_coq:
            lines.append(f"  try change (match {p} with | 0 => 0 | Z.pos y' => Z.pos (y' + y'~0) | Z.neg y' => Z.neg (y' + y'~0) end) with (3 * {p})%Z.")
    lines.append("  try ring; try lia; try reflexivity; try assumption.")
    proof = "\n".join(lines)
    return statement, proof


# ── Composition obligation ──────────────────────────────────────────

def _mk_composition_obligation(
    name: str, expanded_params: list[str], params: list[str],
    ghost_vars: dict[str, str], init_state: str,
    pre_coq: str, post_coq: str, pre_parts: list[str],
    ccall_segs, seg_names: list[str], seg_coqs: list[str],
    final_com: str, q_def_data: QDefData,
    multi_call_callees: set[str], obligations: list[Obligation],
) -> Obligation:
    params_forall = " ".join(f"({p} : Z)" for p in params)
    params_lemma = " ".join(params)
    expanded_params_sorted = sorted(expanded_params)
    expanded_lemma = " ".join(expanded_params_sorted)
    post_str = "(wp_normal (fun s => " + post_coq + "))"

    n_stages = len(ccall_segs)

    # Build composed body
    staged_body = _compose_seg_seq(seg_names, final_com)
    init_state_used = init_state
    if ghost_vars:
        for g, val in ghost_vars.items():
            init_state_used = f'(upd {init_state_used} "{g}"%string (VZ {val}))'

    ghost_has = ghost_vars is not None and len(ghost_vars) > 0

    call_params = expanded_lemma if ghost_has else params_lemma
    proof_params = " ".join(ghost_vars.get(p, p) for p in expanded_params_sorted) if ghost_has else params_lemma

    base_goal = (
        f"(({pre_coq.strip()}) ->\n"
        f"  wp {staged_body}\n"
        f"     {post_str}\n"
        f"     ({init_state_used}))"
    )
    if ghost_has:
        wrapped = base_goal
        for g, init in reversed(list(ghost_vars.items())):
            wrapped = f"(exists ({g} : Z), ({g} = {init} /\\\n  {wrapped}))"
        statement = f"Theorem {name}_correct : forall {params_forall},\n  {wrapped}."
    else:
        statement = f"Theorem {name}_correct : forall {params_forall},\n  {base_goal}."

    # Build proof: chain stage lemmas via wp_seq_decompose, then final post lemma
    lines: list[str] = []

    if ghost_has:
        lines.append("  intros.")
        for _g, init in ghost_vars.items():
            lines.append(f"  exists {init}. split; [reflexivity | ].")
        lines.append("  intros Hpre.")
    else:
        lines.append(f"  intros {call_params} Hpre.")

    if len(pre_parts) > 1:
        pre_hyps = " ".join(f"H{i}" for i in range(len(pre_parts)))
        lines.append(f"  destruct Hpre as [{pre_hyps}].")

    if n_stages == 1:
        seg_name = seg_names[0]
        q1 = f"Q_{name}_1"
        stage1_lemma = f"{name}_stage_1_correct"
        post_lemma = f"{name}_post"
        lines.append(
            f"  apply (wp_seq_decompose_normal {seg_name} {final_com} ({q1} {proof_params}) {post_str} _)."
        )
        pre_solve = "split; assumption" if len(pre_parts) > 1 else "assumption"
        lines.append(f"  {{ apply {stage1_lemma}. {pre_solve}. }}")
        q1_conjs = q_def_data.all_conjs[0]
        lines.append(f"  {{ intros s_final Hq. unfold {q1} in Hq.")
        lines.append(f"    destruct Hq as {_destruct_pat(len(q1_conjs), 'Q')}.")
        q_hyps = " ".join(f"Q{i}" for i in range(len(q1_conjs)))
        lines.append(f"    apply ({post_lemma} {proof_params} s_final {q_hyps}). }}")
    else:
        # Multi-stage chain
        rest_com = _compose_seg_seq(seg_names[1:], final_com)
        q1 = f"Q_{name}_1"

        lines.append(
            f"  apply (wp_seq_decompose_normal {seg_names[0]} {rest_com} ({q1} {proof_params}) {post_str} _)."
        )
        pre_solve = "split; assumption" if len(pre_parts) > 1 else "assumption"
        lines.append(f"  {{ apply {name}_stage_1_correct. {pre_solve}. }}")

        prev_state = "s1"
        for k in range(1, n_stages):
            prev_q_base = f"Q_{name}_{k}"
            qn_next = f"Q_{name}_{k + 1}"
            stage_lemma = f"{name}_stage_{k + 1}_correct"
            prev_conjs = q_def_data.all_conjs[k - 1]

            if k == n_stages - 1:
                next_com = final_com
            else:
                next_com = _compose_seg_seq(seg_names[k + 1:], final_com)

            next_state = f"s{k + 1}"

            lines.append(f"  {{ intros {prev_state} Hq. unfold {prev_q_base} in Hq.")
            dest_pat = _destruct_pat(len(prev_conjs), 'P')
            lines.append(f"    destruct Hq as {dest_pat}.")

            lines.append(
                f"    apply (wp_seq_decompose_normal {seg_names[k]} {next_com} ({qn_next} {proof_params}) {post_str} _)."
            )

            # Apply stage lemma with all hypotheses
            hyps_str = " ".join(f"P{i}" for i in range(len(prev_conjs)))
            lines.append(f"    {{ apply ({stage_lemma} {proof_params} {prev_state} {hyps_str}). }}")

            prev_state = next_state

            if k == n_stages - 1:
                # Innermost: apply post lemma
                post_lemma = f"{name}_post"
                q_next_conjs = q_def_data.all_conjs[k]
                lines.append(f"    {{ intros {next_state} Hq_next. unfold {qn_next} in Hq_next.")
                lines.append(f"      destruct Hq_next as {_destruct_pat(len(q_next_conjs), 'R')}.")
                q_next_hyps = " ".join(f"R{i}" for i in range(len(q_next_conjs)))
                lines.append(f"      apply ({post_lemma} {proof_params} {next_state} {q_next_hyps}). }}")
                lines.append(f"    }}")


    proof = "\n".join(lines)
    return Obligation(
        id=f"{name}.{name}_correct",
        kind=ObligationKind.COMPOSITION,
        theorem_name=f"{name}_correct",
        theorem_statement=statement,
        proof_attempts=[ProofAttempt(tactic=proof, outcome="closed")],
        status=ObligationStatus.PROVED,
    )


# ── Whole-function obligation (non-CCall fallback) ──────────────────

def _make_wholefn_obligation(
    name: str, params: list[str], ghost_vars: dict[str, str],
    init_state: str, pre_coq: str, post_coq: str,
) -> Obligation:
    params_forall = " ".join(f"({p} : Z)" for p in params)
    ghost_has = ghost_vars is not None and len(ghost_vars) > 0

    if ghost_has:
        inner = (
            f"  (({pre_coq}) ->\n"
            f"  wp {name}_body\n"
            f"     (wp_normal (fun s => ({post_coq})))\n"
            f"     ({init_state}))"
        )
        statement = (
            f"Theorem {name}_correct : forall {params_forall},\n"
            + "\n".join(f"  (exists ({g} : Z), (({g} = {init}) /\\" for g, init in ghost_vars.items())
            + inner
            + ")" * len(ghost_vars)
            + "."
        )
    else:
        statement = (
            f"Theorem {name}_correct : forall {params_forall},\n"
            f"  (({pre_coq}) ->\n"
            f"  wp {name}_body\n"
            f"     (wp_normal (fun s => ({post_coq})))\n"
            f"     ({init_state}))."
        )

    return Obligation(
        id=f"{name}.{name}_correct",
        kind=ObligationKind.COMPOSITION,
        theorem_name=f"{name}_correct",
        theorem_statement=statement,
        proof_attempts=[ProofAttempt(tactic="  intros.\n  wp_prove.", outcome="closed")],
        status=ObligationStatus.PROVED,
    )


# ── Helpers ─────────────────────────────────────────────────────────

def _compose_segs(segs) -> str:
    if not segs:
        return "CSkip"
    result = segs[0].to_coq()
    for seg in segs[1:]:
        result = f"(CSeq {result} {seg.to_coq()})"
    return result


def _compose_seg_seq(seg_names: list[str], final_com: str) -> str:
    if not seg_names:
        return final_com
    result = final_com
    for sn in reversed(seg_names):
        result = f"(CSeq {sn} {result})"
    return result


def _destruct_pat(n: int, prefix: str = "H") -> str:
    if n <= 1:
        return f"[{prefix}0]"
    pat = f"[{prefix}0"
    for i in range(1, n):
        if i == n - 1:
            pat += f" {prefix}{i}"
        else:
            pat += f" [{prefix}{i}"
    pat += "]" * (n - 1)
    return pat
