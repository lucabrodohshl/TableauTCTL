#!/usr/bin/env python3
# ============================================================================
# perf_families_big.py - Extended family set for the overnight benchmark.
# ============================================================================
#
# Same two research questions and the same builders as perf_families.py, with
# (a) much longer sweeps, so the walls are actually located rather than merely
# approached, and (b) four extra nesting families that vary *what* is nested,
# not just how deep:
#
#   DEPTH    narrow-window double check          d = 1..50
#   DEPTHW   the same, wide window and band      d = 1..40
#   ALT      alternating universal/existential   d = 1..40
#   RNEST    nested existential releases         d = 1..40
#   OBL      simultaneously live clocks          k = 1..28
#   MIX      depth x clocks, jointly             d,k = 1..8
#   MAXCONST largest constant                    M up to 2^30
#   SIZE     propositional payload               m up to 16384
#   U1..U5   the UPPAAL shapes, size / bound / diagonal sweeps
#
# The earlier run finished every instance inside 600 s and never reached the
# 10 GB cap, so nothing here is trimmed to be safe: OBL and MIX are expected to
# exhaust both budgets, which is the point.
# ============================================================================

from __future__ import annotations

from typing import Dict, List, Tuple

from bench_families import (  # noqa: F401
    SAT, UNSAT, Variant, ValidationError, max_constant,
    _iv, ag, ef, af, eu, au, er, conj,
)
from perf_families import (  # noqa: F401
    validate,
    depth_sat, depth_unsat, obl_sat, obl_unsat,
    maxconst_sat, maxconst_unsat, size_sat,
    u1_sat_size, u1_sat_bound, u1_unsat_bound,
    u2_sat_size, u2_sat_bound, u2_unsat_bound,
    u3_sat_size, u3_sat_bound, u3_unsat_bound,
    u4_sat_size, u4_sat_bound, u4_unsat_bound,
    u5_sat_size,
    _mk,
)

# ----------------------------------------------------------------------------
# Extra nesting families
# ----------------------------------------------------------------------------

_W_L, _W_U, _W_B = 1, 7, 5        # wide window/band for DEPTHW


def _depthw_core(d: int) -> str:
    core = "q"
    for _ in range(d):
        core = ag(0, _W_B, eu("p", _W_L, _W_U, core))
    return core


def depthw_sat(d: int) -> str:
    return _depthw_core(d)


def depthw_unsat(d: int) -> str:
    return conj([_depthw_core(d), ag(0, d * _W_U + 1, "!q")])


def _alt_core(d: int) -> str:
    """Alternate a universal band with an existential until at each level."""
    core = "q"
    for i in range(d):
        core = (ag(0, 2, eu("p", 1, 3, core)) if i % 2 == 0
                else af(1, 4, eu("p", 1, 3, core)))
    return core


def alt_sat(d: int) -> str:
    return _alt_core(d)


def alt_unsat(d: int) -> str:
    return conj([_alt_core(d), ag(0, d * 4 + 1, "!q")])


def _rnest_core(d: int) -> str:
    """Nested existential releases: the release rules, nested d deep."""
    core = "q"
    for _ in range(d):
        core = er("false", 1, 5, eu("p", 1, 3, core))
    return core


def rnest_sat(d: int) -> str:
    return _rnest_core(d)


def rnest_unsat(d: int) -> str:
    return conj([_rnest_core(d), ag(0, d * 5 + 1, "!q")])


def _mix_param(p: int) -> Tuple[int, int]:
    """Encode the (depth, clocks) grid point p = 10*d + k."""
    return p // 10, p % 10


def mix_sat(p: int) -> str:
    d, k = _mix_param(p)
    core = "q"
    for _ in range(d):
        core = ag(0, 2, eu("p", 1, 3, core))
    return conj([core] + [eu("true", i, i + 2, f"q{i}") for i in range(1, k + 1)])


def mix_unsat(p: int) -> str:
    d, k = _mix_param(p)
    core = "q"
    for _ in range(d):
        core = ag(0, 2, eu("p", 1, 3, core))
    killer = ag(0, k + 2, conj([f"!q{i}" for i in range(1, k + 1)]))
    return conj([core] + [eu("true", i, i + 2, f"q{i}") for i in range(1, k + 1)]
                + [killer])


# --- UPPAAL shapes, diagonal sweep (size and bound grow together) -----------

def _diag(b: int) -> int:
    return max(2, b)


def u1_diag(m: int) -> str:
    return ef(0, _diag(m), conj([f"p{i}" for i in range(1, m + 1)]))


def u2_diag(m: int) -> str:
    return ag(0, _diag(m), conj([f"p{i}" for i in range(1, m + 1)]))


def u3_diag(m: int) -> str:
    return af(1, _diag(m) + 1, conj([f"p{i}" for i in range(1, m + 1)]))


def u4_diag(m: int) -> str:
    payload = " | ".join(f"p{i}" for i in range(1, m + 1))
    return ag(0, "inf", f"({payload}) -> " + af(1, _diag(m) + 1, "q"))


def u5_diag(m: int) -> str:
    return ef(0, _diag(m), "true") + " & " + ag(0, "inf",
                                                conj([f"p{i}" for i in range(1, m + 1)]))


# ----------------------------------------------------------------------------
# Parameter ranges
# ----------------------------------------------------------------------------

_POW2 = lambda n: [2 ** i for i in range(n + 1)]                    # noqa: E731


def _logsweep(hi, per_decade=8):
    """Geometrically spaced integers in [1, hi], ~per_decade points per decade."""
    out, x, step = [], 1.0, 10 ** (1.0 / per_decade)
    while x <= hi:
        v = int(round(x))
        if v not in out:
            out.append(v)
        x *= step
    if hi not in out:
        out.append(hi)
    return out


_DEPTH_BIG = list(range(1, 51))                                    # d 1..50
_DEPTHW = list(range(1, 41))                                       # d 1..40
_ALT = list(range(1, 41))
_RNEST = list(range(1, 41))
_K_BIG = list(range(1, 31))                                        # k 1..30
_MIX = [10 * d + k for d in range(1, 10) for k in range(1, 10)]    # 9x9 grid
_M_BIG = _logsweep(2 ** 30, per_decade=12)
_SIZE_BIG = _logsweep(16384, per_decade=9)
_M_PAY = _logsweep(16384, per_decade=9)
_B_BIG = _logsweep(2 ** 30, per_decade=12)
_DIAG = _logsweep(4096, per_decade=10)

_MECH_D = "RQ1 nesting depth"
_MECH_K = "RQ1 simultaneous clocks"
_XD = r"nesting depth $d$"


REGISTRY: List[Variant] = [
    # ------------------------- RQ1: nesting ---------------------------------
    _mk("DEPTH", "F1 nesting depth", "DEPTH_sat", "DEPTH (SAT)",
        "d", _XD, False, SAT, depth_sat, _DEPTH_BIG,
        "Witness short-circuits the search.", _MECH_D),
    _mk("DEPTH", "F1 nesting depth", "DEPTH_unsat", "DEPTH (UNSAT)",
        "d", _XD, False, UNSAT, depth_unsat, _DEPTH_BIG,
        "Refutation must unwind every layer.", _MECH_D),

    _mk("DEPTHW", "F1b nesting, wide window", "DEPTHW_sat", "DEPTHW (SAT)",
        "d", _XD, False, SAT, depthw_sat, _DEPTHW,
        "As DEPTH but with a wider window and band.", _MECH_D),
    _mk("DEPTHW", "F1b nesting, wide window", "DEPTHW_unsat", "DEPTHW (UNSAT)",
        "d", _XD, False, UNSAT, depthw_unsat, _DEPTHW,
        "Wider windows enlarge every zone along the chain.", _MECH_D),

    _mk("ALT", "F1c alternating quantifiers", "ALT_sat", "ALT (SAT)",
        "d", _XD, False, SAT, alt_sat, _ALT,
        "Alternating AG/AF layers exercise both context and goal pursuit.",
        _MECH_D),
    _mk("ALT", "F1c alternating quantifiers", "ALT_unsat", "ALT (UNSAT)",
        "d", _XD, False, UNSAT, alt_unsat, _ALT,
        "Alternation forces the refutation across both kinds of layer.",
        _MECH_D),

    _mk("RNEST", "F1d nested releases", "RNEST_sat", "RNEST (SAT)",
        "d", _XD, False, SAT, rnest_sat, _RNEST,
        "Nested releases exercise the three-way zone split repeatedly.",
        _MECH_D),
    _mk("RNEST", "F1d nested releases", "RNEST_unsat", "RNEST (UNSAT)",
        "d", _XD, False, UNSAT, rnest_unsat, _RNEST,
        "Refutation inside nested release windows.", _MECH_D),

    # ------------------------- RQ1: clocks ----------------------------------
    _mk("OBL", "F2 simultaneous clocks", "OBL_sat", "OBL (SAT)",
        "k", r"# obligations $k$", False, SAT, obl_sat, _K_BIG,
        "A witness must meet all k windows at once.", _MECH_K),
    _mk("OBL", "F2 simultaneous clocks", "OBL_unsat", "OBL (UNSAT)",
        "k", r"# obligations $k$", False, UNSAT, obl_unsat, _K_BIG,
        "One contradiction closes every obligation.", _MECH_K),

    _mk("MIX", "F2b depth x clocks", "MIX_sat", "MIX (SAT)",
        "dk", r"grid point $10d+k$", False, SAT, mix_sat, _MIX,
        "Both handles at once: the product of nesting and clock pressure.",
        "RQ1 depth x clocks"),
    _mk("MIX", "F2b depth x clocks", "MIX_unsat", "MIX (UNSAT)",
        "dk", r"grid point $10d+k$", False, UNSAT, mix_unsat, _MIX,
        "Refutation with both handles engaged.", "RQ1 depth x clocks"),

    # ------------------------- RQ1: controls --------------------------------
    _mk("MAXCONST", "F3 max constant", "MAXCONST_sat", "MAXCONST (SAT)",
        "M", r"max constant $M$", True, SAT, maxconst_sat, _M_BIG,
        "Zones absorb the magnitude of constants.", "RQ1 constant"),
    _mk("MAXCONST", "F3 max constant", "MAXCONST_unsat", "MAXCONST (UNSAT)",
        "M", r"max constant $M$", True, UNSAT, maxconst_unsat, _M_BIG,
        "Zones absorb the magnitude of constants.", "RQ1 constant"),

    _mk("SIZE", "F4 formula size", "SIZE_sat", "SIZE (SAT)",
        "m", r"formula size $m$", True, SAT, size_sat, _SIZE_BIG,
        "Closure grows; the realised search does not.", "RQ1 size"),

    # ------------------------- RQ2: UPPAAL shapes ---------------------------
    _mk("U1", "U1 reachability (EF)", "U1_sat", "U1 size (SAT)",
        "m", r"query size $m$", True, SAT, u1_sat_size, _M_PAY,
        "Flat reachability, payload sweep.", "RQ2 flat"),
    _mk("U1", "U1 reachability (EF)", "U1_sat_b", "U1 bound (SAT)",
        "b", r"time bound $b$", True, SAT, u1_sat_bound, _B_BIG,
        "Flat reachability, bound sweep.", "RQ2 flat"),
    _mk("U1", "U1 reachability (EF)", "U1_unsat", "U1 bound (UNSAT)",
        "b", r"time bound $b$", True, UNSAT, u1_unsat_bound, _B_BIG,
        "Refuted reachability.", "RQ2 flat"),
    _mk("U1", "U1 reachability (EF)", "U1_diag", "U1 diagonal (SAT)",
        "m", r"size and bound $m$", True, SAT, u1_diag, _DIAG,
        "Both axes grown together.", "RQ2 flat"),

    _mk("U2", "U2 safety (AG)", "U2_sat", "U2 size (SAT)",
        "m", r"query size $m$", True, SAT, u2_sat_size, _M_PAY,
        "Flat safety, payload sweep.", "RQ2 flat"),
    _mk("U2", "U2 safety (AG)", "U2_sat_b", "U2 bound (SAT)",
        "b", r"time bound $b$", True, SAT, u2_sat_bound, _B_BIG,
        "Flat safety, bound sweep.", "RQ2 flat"),
    _mk("U2", "U2 safety (AG)", "U2_unsat", "U2 bound (UNSAT)",
        "b", r"time bound $b$", True, UNSAT, u2_unsat_bound, _B_BIG,
        "Refuted safety.", "RQ2 flat"),
    _mk("U2", "U2 safety (AG)", "U2_diag", "U2 diagonal (SAT)",
        "m", r"size and bound $m$", True, SAT, u2_diag, _DIAG,
        "Both axes grown together.", "RQ2 flat"),

    _mk("U3", "U3 bounded liveness (AF)", "U3_sat", "U3 size (SAT)",
        "m", r"query size $m$", True, SAT, u3_sat_size, _M_PAY,
        "Flat liveness, payload sweep.", "RQ2 flat"),
    _mk("U3", "U3 bounded liveness (AF)", "U3_sat_b", "U3 bound (SAT)",
        "b", r"time bound $b$", True, SAT, u3_sat_bound, _B_BIG,
        "Flat liveness, bound sweep.", "RQ2 flat"),
    _mk("U3", "U3 bounded liveness (AF)", "U3_unsat", "U3 bound (UNSAT)",
        "b", r"time bound $b$", True, UNSAT, u3_unsat_bound, _B_BIG,
        "Refuted liveness.", "RQ2 flat"),
    _mk("U3", "U3 bounded liveness (AF)", "U3_diag", "U3 diagonal (SAT)",
        "m", r"size and bound $m$", True, SAT, u3_diag, _DIAG,
        "Both axes grown together.", "RQ2 flat"),

    _mk("U4", "U4 leads-to (AG(p->AF q))", "U4_sat", "U4 size (SAT)",
        "m", r"query size $m$", True, SAT, u4_sat_size, _M_PAY,
        "Leads-to, payload sweep; nesting depth two.", "RQ2 flat"),
    _mk("U4", "U4 leads-to (AG(p->AF q))", "U4_sat_b", "U4 bound (SAT)",
        "b", r"time bound $b$", True, SAT, u4_sat_bound, _B_BIG,
        "Leads-to, bound sweep.", "RQ2 flat"),
    _mk("U4", "U4 leads-to (AG(p->AF q))", "U4_unsat", "U4 bound (UNSAT)",
        "b", r"time bound $b$", True, UNSAT, u4_unsat_bound, _B_BIG,
        "Refuted leads-to.", "RQ2 flat"),
    _mk("U4", "U4 leads-to (AG(p->AF q))", "U4_diag", "U4 diagonal (SAT)",
        "m", r"size and bound $m$", True, SAT, u4_diag, _DIAG,
        "Both axes grown together.", "RQ2 flat"),

    _mk("U5", "U5 E[] (EG)", "U5_sat", "U5 size (SAT)",
        "m", r"query size $m$", True, SAT, u5_sat_size, _M_PAY,
        "Possibly-always, payload sweep.", "RQ2 flat"),
    _mk("U5", "U5 E[] (EG)", "U5_diag", "U5 diagonal (SAT)",
        "m", r"size and bound $m$", True, SAT, u5_diag, _DIAG,
        "Both axes grown together.", "RQ2 flat"),
]


def families() -> Dict[str, List[Variant]]:
    out: Dict[str, List[Variant]] = {}
    for v in REGISTRY:
        out.setdefault(v.family, []).append(v)
    return out


def instances() -> List[Tuple[Variant, int, str]]:
    out: List[Tuple[Variant, int, str]] = []
    for v in REGISTRY:
        for p in v.params:
            out.append((v, p, v.gen(p)))
    return out


if __name__ == "__main__":
    ok = bad = 0
    for v, p, f in instances():
        try:
            validate(f)
            ok += 1
        except ValidationError as e:
            bad += 1
            print(f"INVALID {v.variant} {v.param_name}={p}: {e}")
    print(f"{ok} valid, {bad} invalid, {len(instances())} total")
