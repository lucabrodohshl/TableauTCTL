"""Declarative instance families for the TCTL-satisfiability evaluation.

A family is a named generator of :class:`Instance` records.  Families are pure
data: they know how to *name* and *build* a formula, never how to run it, so the
runner and the analysis can be developed and tested independently.

Three research questions are covered.

RQ1 (cost drivers)
    Vary one structural parameter implicated by the complexity bound
    ``2^{O(n)} * M^{O(n^2)}`` at a time: timed-nesting depth, number of
    simultaneously live formula-clocks, the largest integer constant ``M``, and
    propositional formula size.  Depth and clock count unavoidably co-vary the
    other two, so flat ``M``- and size-controls isolate each blow-up.

RQ2 (practicality)
    The canonical UPPAAL query shapes -- reachability, safety, bounded
    liveness, leads-to and ``E[]`` -- as one-level TCTL, swept over query size
    and time bound.

RQ3 (completeness gap)
    Formulas that are satisfiable *by construction*, so that any UNSATISFIABLE
    verdict is an incompleteness instance rather than a bug.  See
    :func:`rq3_completeness`.
"""

from dataclasses import dataclass, field
from typing import Callable, Iterator, List, Optional


# ── Instance record ─────────────────────────────────────────────────────────

@dataclass(frozen=True)
class Instance:
    """One benchmark formula together with everything the analysis needs."""

    rq: str                    # "RQ1" | "RQ2" | "RQ3"
    family: str                # family name, e.g. "depth"
    name: str                  # unique instance id
    formula: str               # concrete TCTL syntax
    params: dict               # the swept parameters, for grouping/plotting
    expected: Optional[str] = None   # "SAT" / "UNSAT" when known by construction
    witness: Optional[str] = None    # why `expected` holds; required for RQ3


# ── Formula builders ────────────────────────────────────────────────────────
# Concrete syntax follows src/lexer.cpp: atoms p, q, r, p1 ...; ! & | -> <->;
# EF/AF/EG/AG with an optional interval; E(. U[a,b] .), A(. R[a,b] .).

def iv(a: int, b: Optional[int]) -> str:
    """Interval suffix. ``b is None`` means [a,inf); ``b == a`` is punctual."""
    return f"[{a},inf)" if b is None else f"[{a},{b}]"


def ef(phi: str, a: int = 0, b: Optional[int] = None) -> str:
    return f"EF{iv(a, b)} ({phi})"


def ag(phi: str, a: int = 0, b: Optional[int] = None) -> str:
    return f"AG{iv(a, b)} ({phi})"


def af(phi: str, a: int = 0, b: Optional[int] = None) -> str:
    return f"AF{iv(a, b)} ({phi})"


def eg(phi: str, a: int = 0, b: Optional[int] = None) -> str:
    return f"EG{iv(a, b)} ({phi})"


def eu(phi: str, psi: str, a: int = 0, b: Optional[int] = None) -> str:
    return f"E(({phi}) U{iv(a, b)} ({psi}))"


def ar(phi: str, psi: str, a: int = 0, b: Optional[int] = None) -> str:
    return f"A(({phi}) R{iv(a, b)} ({psi}))"


def conj(parts: List[str]) -> str:
    return " & ".join(f"({p})" for p in parts)


# ── RQ1: cost drivers ───────────────────────────────────────────────────────

def rq1_depth(max_depth: int = 10, M: int = 4) -> Iterator[Instance]:
    """Timed-nesting depth, the primary driver.

    The SAT variant nests eventualities that a single always-true location
    satisfies; the UNSAT variant caps the same nest with a safety obligation
    that contradicts the innermost eventuality, forcing the search to exhaust
    the graph rather than stop at a witness.
    """
    for d in range(1, max_depth + 1):
        sat = "p"
        for i in range(d):
            sat = ef(sat, 1, 1 + M)
        yield Instance("RQ1", "depth", f"depth_sat_d{d}", sat,
                       {"depth": d, "M": M}, "SAT",
                       "one location with p always true and divergent time")

        unsat = conj([sat, ag("!(p)", 0, None)])
        yield Instance("RQ1", "depth", f"depth_unsat_d{d}", unsat,
                       {"depth": d, "M": M}, "UNSAT",
                       "the nest demands p somewhere; AG !p forbids it everywhere")


def rq1_clocks(max_k: int = 16, M: int = 4) -> Iterator[Instance]:
    """Simultaneously live formula-clocks = the DBM dimension."""
    for k in range(1, max_k + 1):
        parts = [ef(f"p{i}", i, i + M) for i in range(1, k + 1)]
        sat = eg(conj(parts))
        yield Instance("RQ1", "clocks", f"clocks_sat_k{k}", sat,
                       {"k": k, "M": M}, "SAT",
                       "one location with every p_i true and divergent time")

        unsat = conj([sat, ag("!(p1)", 0, None)])
        yield Instance("RQ1", "clocks", f"clocks_unsat_k{k}", unsat,
                       {"k": k, "M": M}, "UNSAT",
                       "p1 is demanded inside the nest and forbidden everywhere")


def rq1_constant(max_exp: int = 20) -> Iterator[Instance]:
    """Largest integer constant M, as a flat control: depth and clocks fixed."""
    for e in range(0, max_exp + 1):
        M = 2 ** e
        yield Instance("RQ1", "constant", f"const_sat_M{M}",
                       ef("p", M, 2 * M), {"M": M, "exp": e}, "SAT",
                       "p always true, so the window is met by waiting")
        yield Instance("RQ1", "constant", f"const_unsat_M{M}",
                       conj([ef("p", M, 2 * M), ag("!(p)", 0, None)]),
                       {"M": M, "exp": e}, "UNSAT",
                       "p demanded in the window and forbidden everywhere")


def rq1_size(max_exp: int = 10) -> Iterator[Instance]:
    """Propositional formula size, as a flat control (SAT only, benign)."""
    for e in range(1, max_exp + 1):
        n = 2 ** e
        body = conj([f"p{i}" for i in range(1, n + 1)])
        yield Instance("RQ1", "size", f"size_sat_n{n}", ef(body, 1, 5),
                       {"n": n}, "SAT", "all atoms true in the single location")


# ── RQ2: UPPAAL-shaped queries ──────────────────────────────────────────────

def _atoms(n: int) -> str:
    return conj([f"p{i}" for i in range(1, n + 1)])


def rq2_uppaal(sizes=(1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024),
               bounds=(1, 4, 16, 64, 256, 1024, 4096, 65536, 1048576)
               ) -> Iterator[Instance]:
    """The five canonical UPPAAL query shapes, as one-level TCTL.

    Size and time bound are swept separately: each sweep holds the other at its
    smallest value so the two axes stay independent.
    """
    shapes = {
        "reachability": lambda body, b: ef(body, 0, b),      # E<> body
        "safety":       lambda body, b: ag(body, 0, b),      # A[] body
        "liveness":     lambda body, b: af(body, 0, b),      # A<> body
        "leadsto":      lambda body, b: ag(f"(q) -> ({af(body, 0, b)})", 0, None),
        "epossibly":    lambda body, b: eg(body, 0, b),      # E[] body
    }
    for shape, build in shapes.items():
        for n in sizes:
            yield Instance("RQ2", shape, f"{shape}_size{n}", build(_atoms(n), 4),
                           {"axis": "size", "n": n, "bound": 4})
        for b in bounds:
            yield Instance("RQ2", shape, f"{shape}_bound{b}", build(_atoms(1), b),
                           {"axis": "bound", "n": 1, "bound": b})


# ── RQ3: the completeness gap ───────────────────────────────────────────────
#
# The procedure is sound and terminating on all of TCTL, complete over the
# non-punctual fragment, and (Corollary, depth one) complete even with punctual
# intervals when no timed modality is nested inside another.  An UNSATISFIABLE
# verdict on a formula that *is* satisfiable is therefore the one observable
# form of incompleteness, and it needs an oracle independent of the tool.
#
# The oracle here is a single witness automaton, used for every instance:
#
#     W = one location, every atom true, no invariant, one self-loop.
#
# Time diverges in W and every atom holds at every configuration, so W
# satisfies *every* formula of the negation-free fragment generated below --
# each EF/AF/EG/AG/U/R obligation is met at once and at all times, whatever the
# intervals.  Every instance is thus SAT by construction, with no appeal to the
# procedure, and any UNSAT answer is an incompleteness instance.
#
# The sweep crosses punctuality with timed-nesting depth, so the measurement
# separates the two guarantees: non-punctual instances test the completeness
# theorem, punctual depth-1 instances test the corollary, and punctual
# instances of depth >= 2 measure the remaining gap.

WITNESS_W = ("W: one location, every atom true, no invariant, one self-loop; "
             "time diverges and every atom holds at every configuration, so W "
             "satisfies every negation-free formula below")


def _nest(build, depth: int, a: int, b: int, leaf: str = "p") -> str:
    phi = leaf
    for _ in range(depth):
        phi = build(phi, a, b)
    return phi


def rq3_completeness(max_depth: int = 4, a: int = 2, width: int = 3
                     ) -> Iterator[Instance]:
    """Satisfiable-by-construction formulas, punctual vs non-punctual.

    Each shape is instantiated with a punctual window ``[a,a]`` and a
    non-punctual ``[a,a+width]`` of the same lower bound, so the pair differs in
    nothing but punctuality.
    """
    # Nesting depth in the paper's sense counts every temporal modality on a
    # path, timed or not: a leads-to AG(q -> AF_I r) is depth two.  It is the
    # depth that matters, because a fresh onset arises exactly when a modality
    # is demanded inside another's pursuit.
    per_level = {"ef_nest": 1, "ag_ef": 2, "eg_ef": 2,
                 "leadsto": 2, "until": 1, "release": 1}
    shapes = {
        "ef_nest":  lambda d, lo, hi: _nest(ef, d, lo, hi),
        "ag_ef":    lambda d, lo, hi: _nest(lambda x, l, h: ag(ef(x, l, h)), d, lo, hi),
        "eg_ef":    lambda d, lo, hi: _nest(lambda x, l, h: eg(ef(x, l, h), l, h), d, lo, hi),
        "leadsto":  lambda d, lo, hi: _nest(
            lambda x, l, h: ag(f"(q) -> ({af(x, l, h)})"), d, lo, hi),
        "until":    lambda d, lo, hi: _nest(lambda x, l, h: eu("q", x, l, h), d, lo, hi),
        "release":  lambda d, lo, hi: _nest(lambda x, l, h: ar("q", x, l, h), d, lo, hi),
    }
    for shape, build in shapes.items():
        for d in range(1, max_depth + 1):
            for kind, (lo, hi) in (("punctual", (a, a)),
                                   ("nonpunctual", (a, a + width))):
                yield Instance(
                    "RQ3", shape, f"{shape}_{kind}_d{d}", build(d, lo, hi),
                    {"level": d, "depth": d * per_level[shape],
                     "punctual": kind == "punctual",
                     "shape": shape, "lo": lo, "hi": hi},
                    "SAT", WITNESS_W)


def rq3_pinned(max_depth: int = 4, a: int = 2, width: int = 3
               ) -> Iterator[Instance]:
    """Satisfiable formulas whose witness is *forced*, not trivial.

    :func:`rq3_completeness` is satisfied by the all-atoms-true location, so its
    obligations are discharged the moment they are raised and the punctual
    machinery is never exercised.  Here each formula is conjoined with a safety
    constraint that forbids the atom before the window closes, so the only
    models are those that place the atom exactly where the nested windows pin
    it.  This is the shape the incompleteness argument is about: a persistent
    context re-demands a punctual modality at a continuum of onsets, and one
    formula-clock has to serve them all.

    Witness for depth ``d`` with window lower bound ``lo``: the atom ``p`` false
    on ``[0, d*lo)`` and true on ``[d*lo, inf)``.  A nest of ``d`` punctual
    ``EF[lo,lo]`` demands ``p`` at exactly ``d*lo``, which that model provides,
    and the guard forbids nothing it asserts.  For the persistent (``ag_ef``)
    shape the same model works, since from any configuration ``t`` the demand
    falls at ``t + lo >= lo``.
    """
    for d in range(1, max_depth + 1):
        for kind, (lo, hi) in (("punctual", (a, a)),
                               ("nonpunctual", (a, a + width))):
            pin = d * lo
            guard = ag("!(p)", 0, pin - 1) if pin >= 1 else None

            nest = _nest(ef, d, lo, hi)
            phi = conj([nest, guard]) if guard else nest
            yield Instance(
                "RQ3", "pinned_ef", f"pinned_ef_{kind}_d{d}", phi,
                {"level": d, "depth": d, "punctual": kind == "punctual",
                 "shape": "pinned_ef", "lo": lo, "hi": hi}, "SAT",
                f"p false on [0,{pin}) and true on [{pin},inf)")

            # Persistent context: AG re-demands the punctual window at every
            # onset, which is precisely where one formula-clock stops sufficing.
            persistent = _nest(lambda x, l, h: ag(ef(x, l, h)), d, lo, hi)
            phi2 = conj([persistent, ag("!(p)", 0, lo - 1)]) if lo >= 1 else persistent
            yield Instance(
                "RQ3", "pinned_ag_ef", f"pinned_ag_ef_{kind}_d{d}", phi2,
                {"level": d, "depth": 2 * d, "punctual": kind == "punctual",
                 "shape": "pinned_ag_ef", "lo": lo, "hi": hi}, "SAT",
                f"p false on [0,{lo}) and true on [{lo},inf)")


def rq3_controls(a: int = 2, width: int = 3) -> Iterator[Instance]:
    """Negative controls for RQ3.

    A zero incompleteness rate means nothing unless the same pipeline detects a
    genuine miss, so each control is UNSAT by construction: the atom is demanded
    inside a window and forbidden everywhere.  These must all come back
    UNSATISFIABLE; a SATISFIABLE verdict here would be a soundness violation,
    which the runner flags separately.
    """
    for d in range(1, 5):
        for kind, (lo, hi) in (("punctual", (a, a)),
                               ("nonpunctual", (a, a + width))):
            nest = _nest(ef, d, lo, hi)
            yield Instance(
                "RQ3", "control_unsat", f"control_{kind}_d{d}",
                conj([nest, ag("!(p)", 0, None)]),
                {"level": d, "depth": d, "punctual": kind == "punctual",
                 "shape": "control_unsat", "lo": lo, "hi": hi}, "UNSAT",
                "p is demanded inside the nest and forbidden at every time")


# ── Registry ────────────────────────────────────────────────────────────────

FAMILIES: dict = {
    "rq1_depth": rq1_depth,
    "rq1_clocks": rq1_clocks,
    "rq1_constant": rq1_constant,
    "rq1_size": rq1_size,
    "rq2_uppaal": rq2_uppaal,
    "rq3_completeness": rq3_completeness,
    "rq3_pinned": rq3_pinned,
    "rq3_controls": rq3_controls,
}


def all_instances() -> List[Instance]:
    out: List[Instance] = []
    for gen in FAMILIES.values():
        out.extend(gen())
    return out
