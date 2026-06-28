#!/usr/bin/env python3
# ============================================================================
# perf_families.py - Formula families for the TCTL *performance* evaluation
# ============================================================================
#
# This module is the single source of truth for the PERFORMANCE benchmark
# (PERF_EVAL_PLAN.md).  It mirrors bench_families.py (same `Variant` dataclass,
# same low-level builders) but defines the two-research-question family set:
#
#   RQ1 - Cost drivers & scalability (one structural factor per family):
#       F1  DEPTH    : nesting depth d of the timed double-check  (dominant)
#       F2  OBL      : # simultaneously-active clocks/obligations k (zone dim.)
#       F3  MAXCONST : magnitude of the largest constant M  (negative control)
#       F4  SIZE     : raw propositional payload size m       (control)
#
#   RQ2 - Flat / 1-level UPPAAL-style queries over atomic propositions:
#       U1  EF reachability   |  U2  AG safety   |  U3  AF bounded liveness
#       U4  AG(p->AF q) leads-to | U5  EG  (optional)
#     Each U-shape is swept on TWO axes: query payload size m (bound b=4 fixed)
#     and time-bound b (size m=4 fixed).  SAT instances are primary; each shape
#     (U1-U4) also ships a controlled UNSAT instance so the procedure is shown
#     doing real refutation work.
#
# IMPORTANT: this is a PERFORMANCE eval.  The designed verdict (SAT/UNSAT) is
# recorded ONLY to colour/split the curves -- it is NOT re-validated against an
# oracle here (the correctness suite bench_*.py already did that).
#
# SYNTAX (identical constraints to bench_families.py):
#   * Atoms p,q,p1,q1,... ; Booleans ! & | -> <-> ; true/false
#   * EF AF EG AG (timed: AG[0,5] phi) ; E(. U .) A(. U .) E(. R .) A(. R .)
#   * Intervals [a,b] (a,b) [a,inf) ; NON-PUNCTUAL (lower<upper); lower>=0
#   * NO next operator (EX/AX) is ever emitted.
# ============================================================================

from __future__ import annotations

import re
from typing import Callable, Dict, List, Tuple

# Reuse the low-level builders, the Variant dataclass and the max-constant helper
# directly from the correctness harness (no rewrite).  NOTE: we deliberately do
# NOT import bench_families.validate -- its naive bracket matcher treats the
# legitimate non-punctual unbounded interval `[a,inf)` (which mixes `[` and `)`)
# as unbalanced.  The correctness suite never emits `[a,inf)`, so the bug was
# latent; the flat UPPAAL families here DO use it, so we override validate()
# below with an interval-aware version.
from bench_families import (  # noqa: F401  (re-exported for bench_generate.py)
    SAT,
    UNSAT,
    Variant,
    ValidationError,
    max_constant,
    _iv,
    ag,
    ef,
    af,
    eu,
    au,
    er,
    conj,
)


# ----------------------------------------------------------------------------
# Interval-aware grammar validator (overrides bench_families.validate).
# ----------------------------------------------------------------------------

_INTERVAL_RE = re.compile(r"[\[(]\s*(\d+)\s*,\s*(\d+|inf)\s*[\])]")
_NEXT_RE = re.compile(r"\b(EX|AX)\b")


def validate(formula: str) -> None:
    """Raise ValidationError if `formula` violates a basic grammar invariant.

    Identical contract to bench_families.validate but interval-aware: interval
    tokens are stripped before the grouping-paren balance check, so `[a,inf)`
    is accepted.  Numeric intervals must still be non-punctual (lower<upper),
    have lower>=0, and use ')' for an `inf` upper bound.
    """
    if _NEXT_RE.search(formula):
        raise ValidationError(f"forbidden next operator (EX/AX) in: {formula}")

    # Interval sanity on the ORIGINAL string.
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

    # Grouping-paren balance, AFTER removing interval tokens (so the `[..)` of an
    # unbounded interval does not look unbalanced).  Grouping uses only `()`.
    stripped = _INTERVAL_RE.sub(" ", formula)
    depth = 0
    for ch in stripped:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth < 0:
                raise ValidationError(f"unbalanced brackets in: {formula}")
        elif ch in "[]":
            raise ValidationError(f"stray interval bracket in: {formula}")
    if depth != 0:
        raise ValidationError(f"unbalanced brackets in: {formula}")


# ----------------------------------------------------------------------------
# Extra low-level builders not present in bench_families.
# ----------------------------------------------------------------------------


def disj(parts: List[str]) -> str:
    """Disjunction p1 | p2 | ... (single element -> bare atom)."""
    return " | ".join(parts)


def eg(lo: int, hi, phi: str) -> str:
    """Timed EG over [lo,hi]: EG[lo,hi] (phi)."""
    return f"EG{_iv(lo, hi)} ({phi})"


def _ors(prefix: str, m: int) -> str:
    return disj([f"{prefix}{i}" for i in range(1, m + 1)])


def _ands(prefix: str, m: int) -> str:
    return conj([f"{prefix}{i}" for i in range(1, m + 1)])


# ============================================================================
# RQ1 families - one structural factor each, others held fixed.
# ============================================================================

# --- F1  DEPTH : nesting depth d of the timed double-check -------------------
# Layer0 = q ; Layer_i = AG[0,B]( E(p U[L,U] Layer_{i-1}) ).  This is the
# paper's distinctive "double check" nested d deep (the 2^{O(n)} handle).
_F1_L, _F1_U, _F1_B = 1, 3, 2  # window [1,3], band 2 held fixed; depth scales


def _depth_core(d: int) -> str:
    core = "q"
    for _ in range(d):
        core = ag(0, _F1_B, eu("p", _F1_L, _F1_U, core))
    return core


def depth_sat(d: int) -> str:
    # No killer: the p,q-invariant model satisfies every layer -> SAT, and a
    # witness short-circuits the search (near-linear curve).
    return _depth_core(d)


def depth_unsat(d: int) -> str:
    # Forbid q across the whole reachable band [0, d*U+1] (a superset of the
    # absolute window [d*L, d*U] the chain forces q into) -> the root obligation
    # can never be discharged; refutation must unwind all d layers -> UNSAT.
    c = d * _F1_U + 1
    return conj([_depth_core(d), ag(0, c, "!q")])


# --- F2  OBL : # simultaneously-active clocks / obligations k ----------------
# k conjoined independent existential timed-untils over FRESH atoms with
# staggered narrow windows [i,i+2] -> k simultaneously-live formula-clocks
# (DBM dimension k+1).  This is the M^{O(K^2)} zone-dimension handle.


def obl_sat(k: int) -> str:
    return conj([eu("true", i, i + 2, f"q{i}") for i in range(1, k + 1)])


def obl_unsat(k: int) -> str:
    # A universal band forbids every target across the union of windows -> all k
    # obligations must be refuted simultaneously.
    killer = ag(0, k + 2, conj([f"!q{i}" for i in range(1, k + 1)]))
    return conj([eu("true", i, i + 2, f"q{i}") for i in range(1, k + 1)] + [killer])


# --- F3  MAXCONST : magnitude of the largest constant M (negative control) ---
# Structure is a SINGLE flat double-check (depth 1, K=O(1) clocks); only the
# interval constants scale with M.  Expected FLAT in M (DBM/`=_M` absorbs it).
def _mc_base(M: int) -> str:
    # AG[0,2M]( E(p U[M,2M] q) )
    return ag(0, 2 * M, eu("p", M, 2 * M, "q"))


def maxconst_sat(M: int) -> str:
    # Killer band [0,M-1] sits strictly BELOW the window [M,2M] -> q reachable in
    # the required window -> SAT.  (Degenerate at M=1: [0,0] is punctual and is
    # auto-skipped by validate(); see PERF report.)
    return conj([_mc_base(M), ag(0, M - 1, "!q")])


def maxconst_unsat(M: int) -> str:
    # Killer band [0,2M+1] CONTAINS the window [M,2M] -> window inside forbidden
    # band -> UNSAT.  One constant flips the verdict; structure is identical.
    return conj([_mc_base(M), ag(0, 2 * M + 1, "!q")])


# --- F4  SIZE : raw propositional payload size m (control) -------------------
# Exactly ONE timed modality wrapping a large Boolean payload, so K stays O(1)
# while |phi| grows linearly in m.  Expected near-flat / mild polynomial.
_F4_M = 4  # small fixed max-constant


def size_sat(m: int) -> str:
    # EF[1,4]( p_1 & p_2 & ... & p_m ) -- always satisfiable.
    return ef(1, _F4_M, _ands("p", m))


# ============================================================================
# RQ2 families - flat 1-level UPPAAL-style queries.
# Each shape: SAT size-sweep (vary m, b=4), SAT bound-sweep (vary b, m=4),
# and (U1-U4) UNSAT bound-sweep.
# ============================================================================

_RQ2_B = 4  # bound held fixed while sweeping size m
_RQ2_M = 4  # payload size held fixed while sweeping bound b


# --- U1  Reachability  EF[0,b](Phi) -----------------------------------------
def u1_sat_size(m: int) -> str:
    return ef(0, _RQ2_B, _ors("q", m))


def u1_sat_bound(b: int) -> str:
    return ef(0, b, _ors("q", _RQ2_M))


def u1_unsat_bound(b: int) -> str:
    # target reachable in [1,b] yet globally forbidden -> UNSAT.
    return conj([ef(1, b, "q"), ag(0, b, "!q")])


# --- U2  Safety  AG[0,b](Phi) -----------------------------------------------
def u2_sat_size(m: int) -> str:
    return ag(0, _RQ2_B, _ors("p", m))


def u2_sat_bound(b: int) -> str:
    return ag(0, b, _ors("p", _RQ2_M))


def u2_unsat_bound(b: int) -> str:
    # invariant q contradicted by a forced !q in [1,b] -> UNSAT.
    return conj([ag(0, "inf", "q"), ef(1, b, "!q")])


# --- U3  Bounded liveness  AF[1,b](Phi) -------------------------------------
def u3_sat_size(m: int) -> str:
    return af(1, _RQ2_B, _ors("q", m))


def u3_sat_bound(b: int) -> str:
    return af(1, b, _ors("q", _RQ2_M))


def u3_unsat_bound(b: int) -> str:
    # must reach q within [1,b] on all paths, q forbidden -> UNSAT.
    return conj([af(1, b, "q"), ag(0, b, "!q")])


# --- U4  Leads-to / bounded response  AG[0,inf]( Phi_p -> AF[1,b] q ) --------
def u4_sat_size(m: int) -> str:
    return ag(0, "inf", f"({_ors('p', m)}) -> {af(1, _RQ2_B, 'q')}")


def u4_sat_bound(b: int) -> str:
    return ag(0, "inf", f"({_ors('p', _RQ2_M)}) -> {af(1, b, 'q')}")


def u4_unsat_bound(b: int) -> str:
    # a p-state is forced (EF[0,b] p), demands a q-response in [1,b], but q is
    # globally forbidden across the whole response window -> UNSAT.
    #   NOTE: a p-state reached at absolute time t<=b places its AF[1,b] response
    #   at absolute time up to t+b<=2b, so the killer must forbid q through 2b.
    #   The plan's "B>=b" with B=b is escapable (the solver correctly calls it
    #   SAT); we use B=2b, which still satisfies B>=b -- see PERF report.
    return conj([
        ef(0, b, "p"),
        ag(0, "inf", f"(p) -> {af(1, b, 'q')}"),
        ag(0, 2 * b, "!q"),
    ])


# --- U5  E[]  EG[0,inf](Phi)  (optional 5th shape, SAT only) -----------------
def u5_sat_size(m: int) -> str:
    return eg(0, "inf", _ands("p", m))


# ----------------------------------------------------------------------------
# Default scaling ranges (from PERF_EVAL_PLAN.md sections 2 and 3).
# ----------------------------------------------------------------------------
# Beefier ranges (300 s timeout): walls (depth, clocks) extended a little past the
# new solved frontier; the *absorbed* axes (M, size, bound) pushed to 2^20 ~ 1e6 to
# demonstrate constant/size absorption across six extra orders of magnitude.
_POW2_20 = [1 << i for i in range(0, 21)]                     # 1,2,...,1048576
_DEPTH = list(range(1, 13))                                   # d in 1..12
_K = list(range(1, 21))                                       # k in 1..20
_M_LOG = _POW2_20                                             # M up to 2^20
_SIZE = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]         # m (log2) to 1024
_BOUND = _POW2_20                                             # b up to 2^20


# ----------------------------------------------------------------------------
# Registry.
# ----------------------------------------------------------------------------


def _mk(fam, fam_lbl, var, var_lbl, pname, xlbl, logx, exp, gen, params, hyp, mech):
    return Variant(fam, fam_lbl, var, var_lbl, pname, xlbl, logx, exp, gen, params, hyp, mech)


REGISTRY: List[Variant] = [
    # ===================== RQ1 =====================================
    # --- F1 DEPTH (dominant driver) ---
    _mk("DEPTH", "F1 nesting depth", "DEPTH_sat", "DEPTH (SAT)",
        "d", r"nesting depth $d$", False, SAT, depth_sat, _DEPTH,
        "Witness short-circuits the search -> near-linear in depth.",
        "RQ1/F1 depth (2^{O(n)} handle)"),
    _mk("DEPTH", "F1 nesting depth", "DEPTH_unsat", "DEPTH (UNSAT)",
        "d", r"nesting depth $d$", False, UNSAT, depth_unsat, _DEPTH,
        "Refutation must exhaust the AND-OR graph -> exponential in depth.",
        "RQ1/F1 depth (2^{O(n)} handle)"),

    # --- F2 OBL (secondary wall: zone dimension) ---
    _mk("OBL", "F2 simultaneous clocks", "OBL_sat", "OBL (SAT)",
        "k", r"# obligations $k$", False, SAT, obl_sat, _K,
        "k live clocks -> per-node zone work Theta(k^2); super-polynomial zones.",
        "RQ1/F2 clocks (M^{O(K^2)} handle)"),
    _mk("OBL", "F2 simultaneous clocks", "OBL_unsat", "OBL (UNSAT)",
        "k", r"# obligations $k$", False, UNSAT, obl_unsat, _K,
        "All k obligations refute simultaneously; cost grows with k.",
        "RQ1/F2 clocks (M^{O(K^2)} handle)"),

    # --- F3 MAXCONST (negative control: M is not a driver) ---
    _mk("MAXCONST", "F3 max constant", "MAXCONST_sat", "MAXCONST (SAT)",
        "M", r"max constant $M$", True, SAT, maxconst_sat, _M_LOG,
        "Flat in M: DBM/`=_M` absorbs large bounds without enumerating time.",
        "RQ1/F3 max-constant (absorbed)"),
    _mk("MAXCONST", "F3 max constant", "MAXCONST_unsat", "MAXCONST (UNSAT)",
        "M", r"max constant $M$", True, UNSAT, maxconst_unsat, _M_LOG,
        "Flat in M; one constant flips the verdict, structure identical.",
        "RQ1/F3 max-constant (absorbed)"),

    # --- F4 SIZE (control: raw propositional size) ---
    _mk("SIZE", "F4 formula size", "SIZE_sat", "SIZE (SAT)",
        "m", r"formula size $m$", True, SAT, size_sat, _SIZE,
        "Near-flat: on-the-fly memoisation realises few nodes despite large |phi|.",
        "RQ1/F4 size (absorbed)"),

    # ===================== RQ2 (flat UPPAAL queries) ===============
    # --- U1 reachability EF ---
    _mk("U1", "U1 reachability (EF)", "U1_sat", "U1 EF (SAT)",
        "m", r"query size $m$", True, SAT, u1_sat_size, _SIZE,
        "Flat 1-level reachability: sub-second, flat in size.",
        "RQ2/U1 reachability"),
    _mk("U1", "U1 reachability (EF)", "U1_sat", "U1 EF (SAT)",
        "b", r"time-bound $b$", True, SAT, u1_sat_bound, _BOUND,
        "Flat 1-level reachability: sub-second, flat in bound.",
        "RQ2/U1 reachability"),
    _mk("U1", "U1 reachability (EF)", "U1_unsat", "U1 EF (UNSAT)",
        "b", r"time-bound $b$", True, UNSAT, u1_unsat_bound, _BOUND,
        "Controlled refutation: target globally forbidden.",
        "RQ2/U1 reachability"),

    # --- U2 safety AG ---
    _mk("U2", "U2 safety (AG)", "U2_sat", "U2 AG (SAT)",
        "m", r"query size $m$", True, SAT, u2_sat_size, _SIZE,
        "Flat 1-level safety: sub-second, flat in size.",
        "RQ2/U2 safety"),
    _mk("U2", "U2 safety (AG)", "U2_sat", "U2 AG (SAT)",
        "b", r"time-bound $b$", True, SAT, u2_sat_bound, _BOUND,
        "Flat 1-level safety: sub-second, flat in bound.",
        "RQ2/U2 safety"),
    _mk("U2", "U2 safety (AG)", "U2_unsat", "U2 AG (UNSAT)",
        "b", r"time-bound $b$", True, UNSAT, u2_unsat_bound, _BOUND,
        "Controlled refutation: invariant contradicted by a forced !q.",
        "RQ2/U2 safety"),

    # --- U3 bounded liveness AF ---
    _mk("U3", "U3 bounded liveness (AF)", "U3_sat", "U3 AF (SAT)",
        "m", r"query size $m$", True, SAT, u3_sat_size, _SIZE,
        "Flat 1-level liveness: sub-second, flat in size.",
        "RQ2/U3 bounded liveness"),
    _mk("U3", "U3 bounded liveness (AF)", "U3_sat", "U3 AF (SAT)",
        "b", r"time-bound $b$", True, SAT, u3_sat_bound, _BOUND,
        "Flat 1-level liveness: sub-second, flat in bound.",
        "RQ2/U3 bounded liveness"),
    _mk("U3", "U3 bounded liveness (AF)", "U3_unsat", "U3 AF (UNSAT)",
        "b", r"time-bound $b$", True, UNSAT, u3_unsat_bound, _BOUND,
        "Controlled refutation: q forbidden across the response window.",
        "RQ2/U3 bounded liveness"),

    # --- U4 leads-to AG(p->AF q) ---
    _mk("U4", "U4 leads-to (AG(p->AF q))", "U4_sat", "U4 leads-to (SAT)",
        "m", r"query size $m$", True, SAT, u4_sat_size, _SIZE,
        "Flat leads-to (depth 2): sub-second, flat in size.",
        "RQ2/U4 leads-to"),
    _mk("U4", "U4 leads-to (AG(p->AF q))", "U4_sat", "U4 leads-to (SAT)",
        "b", r"time-bound $b$", True, SAT, u4_sat_bound, _BOUND,
        "Flat leads-to (depth 2): sub-second, flat in bound.",
        "RQ2/U4 leads-to"),
    _mk("U4", "U4 leads-to (AG(p->AF q))", "U4_unsat", "U4 leads-to (UNSAT)",
        "b", r"time-bound $b$", True, UNSAT, u4_unsat_bound, _BOUND,
        "Controlled refutation: forced p-state demands a globally-forbidden q.",
        "RQ2/U4 leads-to"),

    # --- U5 EG (optional, SAT only) ---
    _mk("U5", "U5 E[] (EG)", "U5_sat", "U5 EG (SAT)",
        "m", r"query size $m$", True, SAT, u5_sat_size, _SIZE,
        "Flat invariant existence: sub-second, flat in size.",
        "RQ2/U5 EG"),
]


def families() -> Dict[str, List[Variant]]:
    out: Dict[str, List[Variant]] = {}
    for v in REGISTRY:
        out.setdefault(v.family, []).append(v)
    return out


def instances() -> List[Tuple[Variant, int, str]]:
    """Materialise (variant, param, formula) for every registry entry."""
    out: List[Tuple[Variant, int, str]] = []
    for v in REGISTRY:
        for p in v.params:
            out.append((v, p, v.gen(p)))
    return out


# ----------------------------------------------------------------------------
# Dry-run self-test: print a sample per registry entry, validate every instance.
# ----------------------------------------------------------------------------

if __name__ == "__main__":
    import sys

    n_ok = 0
    n_bad = 0
    n_skip = 0
    print("# TCTL PERFORMANCE families - structural self-check\n")
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

    total = 0
    for v, p, f in instances():
        total += 1
        try:
            validate(f)
        except ValidationError as e:
            # Punctual-interval degenerate corners (M=1 SAT killer [0,0];
            # b=1 with a [1,b] modality) are expected to be skipped, not failures.
            n_skip += 1
            print(f"SKIP (degenerate) [{v.variant} {v.param_name}={p}]: {e}")
    print(f"\n# samples ok={n_ok} bad={n_bad}; validated {total} instances, "
          f"{n_skip} degenerate-skipped")
    sys.exit(1 if n_bad else 0)
