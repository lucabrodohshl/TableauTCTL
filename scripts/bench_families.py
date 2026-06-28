#!/usr/bin/env python3
# ============================================================================
# bench_families.py - Synthetic TCTL formula families for the tableau benchmark
# ============================================================================
#
# This module is the single source of truth for the *generator*.  It defines
# parameterized formula FAMILIES, each with exactly ONE scaling parameter
# (the x-axis of its plot), a documented HYPOTHESIS, and - wherever possible -
# a matched SAT / UNSAT pair whose ground-truth verdict is *controlled by
# construction* (so the runner can validate the solver's answer).
#
# Design goals (TACAS-quality):
#   * Stress the paper's distinctive mechanism: the "double check" = a
#     universal-over-timed-until re-evaluation,  AG[0,b]( E(p U[l,u] q) ).
#   * Give every family a falsifiable hypothesis and a monotone, interpretable
#     scaling curve, with the hardest instances approaching a timeout.
#   * Control the verdict (SAT vs UNSAT) so the benchmark doubles as a
#     correctness oracle, not only a performance probe.
#
# SYNTAX (verified against include/tctl/parser.hpp, src/lexer.cpp,
#         src/parser.cpp, examples/tctl_examples.txt, src/test.cpp):
#   * Atoms        : identifiers  p, q, p1, q1, ...
#   * Booleans     : !  &  |  ->  <->   and constants  true / false
#   * Path/temporal: EF AF EG AG (unary, optionally timed)
#                    E(. U .)  A(. U .)  E(. R .)  A(. R .)  (optionally timed)
#   * Timed form   : the interval is written DIRECTLY after the operator, e.g.
#                       AG[0,5] phi      EF[1,5] phi
#                       E(p U[1,5] q)    A(p R[2,10] q)
#                    Closed [a,b], open (a,b), or unbounded [a,inf) / (a,inf).
#   * NON-PUNCTUAL : every interval has lower < upper (no [a,a]); lower >= 0.
#   * NO next op   : EX / AX are FORBIDDEN (being removed from the language) and
#                    are NEVER emitted here.
#
# Each generator returns a *plain string* in the solver's input syntax.
# ============================================================================

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Callable, Dict, List, Tuple

SAT = "SAT"
UNSAT = "UNSAT"

# ----------------------------------------------------------------------------
# Low-level builders (kept tiny + explicit so the emitted syntax is auditable)
# ----------------------------------------------------------------------------


def _iv(lo: int, hi) -> str:
    """Closed integer interval [lo,hi] (hi may be the string 'inf' -> [lo,inf))."""
    if hi == "inf":
        return f"[{lo},inf)"
    return f"[{lo},{hi}]"


def ag(lo: int, hi, phi: str) -> str:
    """Timed AG over [lo,hi]: AG[lo,hi] (phi)."""
    return f"AG{_iv(lo, hi)} ({phi})"


def ef(lo: int, hi, phi: str) -> str:
    return f"EF{_iv(lo, hi)} ({phi})"


def af(lo: int, hi, phi: str) -> str:
    return f"AF{_iv(lo, hi)} ({phi})"


def eu(lhs: str, lo: int, hi, rhs: str) -> str:
    """Timed existential until: E(lhs U[lo,hi] (rhs))."""
    return f"E({lhs} U{_iv(lo, hi)} ({rhs}))"


def au(lhs: str, lo: int, hi, rhs: str) -> str:
    return f"A({lhs} U{_iv(lo, hi)} ({rhs}))"


def er(lhs: str, lo: int, hi, rhs: str) -> str:
    """Timed existential release: E(lhs R[lo,hi] (rhs))."""
    return f"E({lhs} R{_iv(lo, hi)} ({rhs}))"


def conj(parts: List[str]) -> str:
    return " & ".join(parts)


# ----------------------------------------------------------------------------
# Family generators.  Each takes ONE integer scaling parameter and returns the
# formula string.  Ground-truth verdict is fixed by construction (see HYPS).
# ----------------------------------------------------------------------------

# === Family DCN : nested DOUBLE CHECK, scale = nesting depth d ===============
# Layer(0) = q ; Layer(i) = AG[0,B]( E(p U[L,U] Layer(i-1)) )
# This is the paper's distinctive construct nested d deep: at every time point
# of a universal band we re-open an existential timed-until obligation.
_DCN_L, _DCN_U, _DCN_B = 1, 3, 2  # fixed window/band; depth is the scaling axis


def dcn_core(d: int) -> str:
    core = "q"
    for _ in range(d):
        core = ag(0, _DCN_B, eu("p", _DCN_L, _DCN_U, core))
    return core


def dcn_sat(d: int) -> str:
    # No killer: the model with p,q invariantly true satisfies every layer. SAT.
    return dcn_core(d)


def dcn_unsat(d: int) -> str:
    # A satisfying chain forces q at some absolute time in [d*L, d*U].  Forbid q
    # globally up to d*U+1 (a superset of that band) -> the root obligation can
    # never be discharged -> UNSAT.  The killer constant grows with d, so this
    # also pushes the max-constant; curve stays monotone.
    c = d * _DCN_U + 1
    return conj([dcn_core(d), ag(0, c, "!q")])


# === Family DCM : single DOUBLE CHECK, scale = constant magnitude M ==========
# Base = AG[0,2M]( E(p U[M,2M] q) ).  The SAT/UNSAT verdict is flipped ONLY by
# the killer band c:  SAT when c < L (q allowed inside the window), UNSAT when
# c >= U (the inner window [L,U] sits entirely inside the forbidden band [0,c]).
# Minimal, decisive pair illustrating "window subset of forbidden band".
def _dcm_base(M: int) -> str:
    L, Uu, B = M, 2 * M, 2 * M
    return ag(0, B, eu("p", L, Uu, "q"))


def dcm_sat(M: int) -> str:
    c = M - 1  # c < L = M  -> q can occur in the required window -> SAT
    return conj([_dcm_base(M), ag(0, c, "!q")])


def dcm_unsat(M: int) -> str:
    c = 2 * M + 1  # c >= U = 2M -> window subset of forbidden band -> UNSAT
    return conj([_dcm_base(M), ag(0, c, "!q")])


# === Family MSC : max-constant M scaling (large integer bounds) =============
# A fixed-depth "forced-delay staircase": at each of D levels we MUST elapse to
# the [M-1,M] window before progressing, so a witness reaches p only around
# absolute time D*(M-1)..D*M.  Larger M -> finer zone distinctions up to ~D*M,
# resisting constant-abstraction collapse.
_MSC_DEPTH = 3


def msc_core(M: int) -> str:
    core = "p"
    for _ in range(_MSC_DEPTH):
        core = eu("true", M - 1, M, core)
    return core


def msc_sat(M: int) -> str:
    return msc_core(M)


def msc_unsat(M: int) -> str:
    # The staircase forces p by absolute time <= D*M; forbid p through D*M+1.
    c = _MSC_DEPTH * M + 1
    return conj([msc_core(M), ag(0, c, "!p")])


# === Family OBL : clock / obligation pressure, scale = #conjuncts k =========
# k independent existential timed-untils over FRESH atoms with staggered
# windows [i, i+2] -> k simultaneously-live clocks / windows.
def obl_sat(k: int) -> str:
    return conj([eu("true", i, i + 2, f"q{i}") for i in range(1, k + 1)])


def obl_unsat(k: int) -> str:
    # Same k obligations, but a universal band forbids every target across the
    # union of windows [0,k+2] -> each obligation is individually unsatisfiable.
    killer = ag(0, k + 2, conj([f"!q{i}" for i in range(1, k + 1)]))
    return conj([eu("true", i, i + 2, f"q{i}") for i in range(1, k + 1)] + [killer])


# === Family NUN : UNTIL nesting depth d (small fixed window) ================
def nun_core(d: int) -> str:
    core = "p"
    for _ in range(d):
        core = eu("true", 1, 3, core)
    return core


def nun_sat(d: int) -> str:
    return nun_core(d)


def nun_unsat(d: int) -> str:
    c = 3 * d + 1  # nested untils force p by absolute time <= 3d; forbid it
    return conj([nun_core(d), ag(0, c, "!p")])


# === Family NRL : RELEASE nesting depth d (dual greatest-fixpoint) ==========
# E(false R[1,3] X): on some path X must hold throughout the [1,3] band
# (false never releases).  SAT nests around an always-true atom; UNSAT nests
# around `false` so the innermost release is impossible and the contradiction
# must be unwound through all d levels (also exercises the time-progress test).
def nrl_sat(d: int) -> str:
    core = "p"
    for _ in range(d):
        core = er("false", 1, 3, core)
    return core


def nrl_unsat(d: int) -> str:
    core = "false"
    for _ in range(d):
        core = er("false", 1, 3, core)
    return core


# === Family ZEN : Zeno rejection, scale = M ================================
# Witnesses that exist only under time-convergent (Zeno) runs must be rejected;
# the solver's time-progress / anti-Zeno loop test is the thing under stress.
def zen_unsat_eg(M: int) -> str:
    # EG p forces an infinite p-path; AG[1,M] !p forces !p once time reaches
    # [1,M].  The only "model" keeps time < 1 forever (Zeno) -> must be UNSAT.
    return f"EG p & {ag(1, M, '!p')}"


def zen_unsat_false(M: int) -> str:
    # AG[1,M] false: vacuous under Zeno (never enter [1,M]); UNSAT under
    # time-divergence.
    return f"AG{_iv(1, M)} false"


def zen_sat(M: int) -> str:
    # Genuine divergent witness: p holds forever (EG p) AND q is reached within
    # [1,M] on all paths (AF).  SAT control for the same machinery.
    return f"EG p & {af(1, M, 'q')}"


# ----------------------------------------------------------------------------
# Family / variant registry
# ----------------------------------------------------------------------------


@dataclass
class Variant:
    family: str            # short family code (CSV/plot grouping)
    family_label: str      # human-readable family name
    variant: str           # short variant code
    variant_label: str     # human-readable variant name
    param_name: str        # x-axis parameter name (depth / M / k)
    x_label: str           # axis label for plots
    log_x: bool            # log-scale x?
    expected: str          # designed ground-truth verdict (SAT/UNSAT)
    gen: Callable[[int], str]
    params: List[int]      # default scaling values
    hypothesis: str        # one-line falsifiable hypothesis
    mechanism: str         # which task requirement (a)-(e) this targets


# Default scaling ranges (chosen so the hardest instances approach a timeout).
_DEPTH = list(range(1, 13))                 # 1..12 nesting depth
_M_LOG = [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192]
_K = list(range(1, 19))                     # 1..18 conjuncts
_ZM = [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]


def _mk(fam, fam_lbl, var, var_lbl, pname, xlbl, logx, exp, gen, params, hyp, mech):
    return Variant(fam, fam_lbl, var, var_lbl, pname, xlbl, logx, exp, gen, params, hyp, mech)


REGISTRY: List[Variant] = [
    # --- (a) DOUBLE CHECK, nested (depth) -----------------------------------
    _mk("DCN", "Double-Check (nested)", "DCN_sat", "Nested double-check (SAT)",
        "depth", "nesting depth $d$", False, SAT, dcn_sat, _DEPTH,
        "Cost of re-deriving an existential timed-until at every universally "
        "quantified state grows monotonically (super-linearly) with nesting "
        "depth; SAT witness is the q-invariant model.",
        "(a) double check"),
    _mk("DCN", "Double-Check (nested)", "DCN_unsat", "Nested double-check (UNSAT)",
        "depth", "nesting depth $d$", False, UNSAT, dcn_unsat, _DEPTH,
        "Forbidding q across the whole reachable band [0,d*U+1] makes the nested "
        "obligation unsatisfiable; refutation requires unwinding all d layers, so "
        "cost grows faster than the SAT side.",
        "(a) double check"),

    # --- (a)+(b) DOUBLE CHECK, single, constant magnitude (M) ---------------
    _mk("DCM", "Double-Check (constant sweep)", "DCM_sat", "Double-check window (SAT)",
        "M", "max constant $M$", True, SAT, dcm_sat, _M_LOG,
        "With killer band c=M-1 < L the required window [M,2M] is reachable, so "
        "the double-check is SAT; runtime grows with M only through zone "
        "constant magnitude.",
        "(a) double check + (b) max-constant"),
    _mk("DCM", "Double-Check (constant sweep)", "DCM_unsat", "Double-check window (UNSAT)",
        "M", "max constant $M$", True, UNSAT, dcm_unsat, _M_LOG,
        "Flipping ONLY the killer band to c=2M+1 puts the inner window [M,2M] "
        "entirely inside the forbidden band -> UNSAT.  Demonstrates verdict "
        "control by a single constant and isolates constant-magnitude cost.",
        "(a) double check + (b) max-constant"),

    # --- (b) MAX-CONSTANT M scaling -----------------------------------------
    _mk("MSC", "Max-constant staircase", "MSC_sat", "Forced-delay staircase (SAT)",
        "M", "max constant $M$", True, SAT, msc_sat, _M_LOG,
        "A fixed-depth staircase of [M-1,M] delays forces witness times up to "
        "~D*M; runtime/zones grow with M if constant-abstraction does not fully "
        "collapse the bound.",
        "(b) max-constant"),
    _mk("MSC", "Max-constant staircase", "MSC_unsat", "Forced-delay staircase (UNSAT)",
        "M", "max constant $M$", True, UNSAT, msc_unsat, _M_LOG,
        "Forbidding p through D*M+1 contradicts the staircase deadline; the "
        "conflict is only detectable after exploring the bound, so cost grows "
        "with M.",
        "(b) max-constant"),

    # --- (c) CLOCK / OBLIGATION pressure ------------------------------------
    _mk("OBL", "Obligation pressure", "OBL_sat", "Independent timed untils (SAT)",
        "k", "number of obligations $k$", False, SAT, obl_sat, _K,
        "k conjoined independent timed-untils over fresh atoms force k live "
        "clocks/windows; DBM dimension is k+1 so per-step zone work is "
        "Theta(k^2) and the SAT curve grows polynomially in k.",
        "(c) clock/obligation pressure"),
    _mk("OBL", "Obligation pressure", "OBL_unsat", "Killed timed untils (UNSAT)",
        "k", "number of obligations $k$", False, UNSAT, obl_unsat, _K,
        "A universal band forbids every target, so all k obligations must be "
        "individually refuted; refutation cost grows with k.",
        "(c) clock/obligation pressure"),

    # --- (d) UNTIL / RELEASE nesting depth ----------------------------------
    _mk("NUN", "Until nesting", "NUN_sat", "Nested timed until (SAT)",
        "depth", "nesting depth $d$", False, SAT, nun_sat, _DEPTH,
        "Pure least-fixpoint nesting: d stacked existential timed-untils; cost "
        "tracks the number of simultaneously open eventualities.",
        "(d) until/release nesting"),
    _mk("NUN", "Until nesting", "NUN_unsat", "Nested timed until (UNSAT)",
        "depth", "nesting depth $d$", False, UNSAT, nun_unsat, _DEPTH,
        "Forbidding p past the cumulative deadline 3d makes the whole nest "
        "unsatisfiable; full unwinding required.",
        "(d) until/release nesting"),
    _mk("NRL", "Release nesting", "NRL_sat", "Nested timed release (SAT)",
        "depth", "nesting depth $d$", False, SAT, nrl_sat, _DEPTH,
        "Pure greatest-fixpoint nesting (dual of NUN): d stacked existential "
        "timed-releases accepted by a safe loop; stresses loop ACCEPTANCE.",
        "(d) until/release nesting"),
    _mk("NRL", "Release nesting", "NRL_unsat", "Nested timed release (UNSAT)",
        "depth", "nesting depth $d$", False, UNSAT, nrl_unsat, _DEPTH,
        "Innermost E(false R[1,3] false) is unsatisfiable under time progress; "
        "the contradiction must be propagated through all d release layers.",
        "(d) until/release nesting"),

    # --- (e) ZENO rejection -------------------------------------------------
    _mk("ZEN", "Zeno rejection", "ZEN_unsat_eg", "EG vs timed safety (UNSAT)",
        "M", "max constant $M$", False, UNSAT, zen_unsat_eg, _ZM,
        "EG p & AG[1,M] !p is satisfiable ONLY by time-convergent runs; the "
        "time-progress loop test must reject them, so the answer is UNSAT.",
        "(e) Zeno rejection"),
    _mk("ZEN", "Zeno rejection", "ZEN_unsat_false", "Timed safety vacuity (UNSAT)",
        "M", "max constant $M$", False, UNSAT, zen_unsat_false, _ZM,
        "AG[1,M] false is vacuous only under Zeno escapes; correct non-Zeno "
        "semantics force time into [1,M] and yield UNSAT.",
        "(e) Zeno rejection"),
    _mk("ZEN", "Zeno rejection", "ZEN_sat", "Divergent witness (SAT)",
        "M", "max constant $M$", False, SAT, zen_sat, _ZM,
        "EG p & AF[1,M] q has a genuine time-divergent witness; the SAME loop "
        "machinery must ACCEPT it -> SAT (control for the two UNSAT variants).",
        "(e) Zeno rejection"),
]


def families() -> Dict[str, List[Variant]]:
    out: Dict[str, List[Variant]] = {}
    for v in REGISTRY:
        out.setdefault(v.family, []).append(v)
    return out


# ----------------------------------------------------------------------------
# Structural self-check (cheap grammar sanity, NOT a full parser).
# Verifies: no EX/AX; balanced brackets; every numeric interval is
# non-punctual with lower>=0 and inf only with ')'.
# ----------------------------------------------------------------------------

_INTERVAL_RE = re.compile(r"[\[(]\s*(\d+)\s*,\s*(\d+|inf)\s*[\])]")
_NEXT_RE = re.compile(r"\b(EX|AX)\b")


class ValidationError(ValueError):
    pass


def validate(formula: str) -> None:
    """Raise ValidationError if `formula` violates a basic grammar invariant."""
    if _NEXT_RE.search(formula):
        raise ValidationError(f"forbidden next operator (EX/AX) in: {formula}")

    # Balanced brackets.
    stack = []
    pairs = {")": "(", "]": "[", "}": "{"}
    for ch in formula:
        if ch in "([{":
            stack.append(ch)
        elif ch in ")]}":
            if not stack or stack[-1] != pairs[ch]:
                raise ValidationError(f"unbalanced brackets in: {formula}")
            stack.pop()
    if stack:
        raise ValidationError(f"unbalanced brackets in: {formula}")

    # Numeric intervals: non-punctual, lower>=0, inf -> open upper ')'.
    for m in _INTERVAL_RE.finditer(formula):
        lo_s, hi_s = m.group(1), m.group(2)
        lo = int(lo_s)
        if lo < 0:
            raise ValidationError(f"negative lower bound in {m.group(0)}: {formula}")
        if hi_s == "inf":
            if not m.group(0).endswith(")"):
                raise ValidationError(f"inf upper must use ')' in {m.group(0)}: {formula}")
            continue
        hi = int(hi_s)
        if lo >= hi:
            raise ValidationError(
                f"punctual/empty interval {m.group(0)} (need lower<upper): {formula}")


def max_constant(formula: str) -> int:
    """Largest integer time constant appearing in any interval (0 if none)."""
    best = 0
    for m in _INTERVAL_RE.finditer(formula):
        for g in m.groups():
            if g != "inf":
                best = max(best, int(g))
    return best


def instances() -> List[Tuple[Variant, int, str]]:
    """Materialise (variant, param, formula) for every registry entry."""
    out: List[Tuple[Variant, int, str]] = []
    for v in REGISTRY:
        for p in v.params:
            out.append((v, p, v.gen(p)))
    return out


# ----------------------------------------------------------------------------
# Dry-run self-test: print a sample per variant and validate every instance.
# ----------------------------------------------------------------------------

if __name__ == "__main__":
    import sys

    n_ok = 0
    n_bad = 0
    print("# TCTL benchmark families - structural self-check\n")
    for v in REGISTRY:
        sample_p = v.params[min(2, len(v.params) - 1)]
        sample = v.gen(sample_p)
        try:
            validate(sample)
            tag = "ok"
            n_ok += 1
        except ValidationError as e:
            tag = f"FAIL: {e}"
            n_bad += 1
        print(f"[{v.family}/{v.variant}]  ({v.param_name}={sample_p}, exp={v.expected})")
        print(f"    {sample}")
        print(f"    -> {tag}\n")

    # Validate ALL instances.
    total = 0
    for v, p, f in instances():
        total += 1
        try:
            validate(f)
        except ValidationError as e:
            n_bad += 1
            print(f"INVALID [{v.variant} {v.param_name}={p}]: {e}")
    print(f"# samples ok={n_ok} bad={n_bad}; validated {total} total instances")
    sys.exit(1 if n_bad else 0)
