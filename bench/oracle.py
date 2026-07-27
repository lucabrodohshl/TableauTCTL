"""An independent satisfiability oracle for RQ3.

Deciding whether the procedure is *missing* a model needs a notion of
satisfiability that does not come from the procedure.  This module supplies one
by fixing a concrete witness structure and evaluating formulas on it exactly.

The structure
-------------
``Witness`` is a single-location timed structure: one location with a self-loop,
no invariant, time diverging, and each atom true on a set of times that is
periodic with period ``P``.  Because the location and the labelling never
change, every maximal run from a configuration carries the same atom trace, and
that trace is a function of time alone.  Consequently the path quantifiers
collapse -- ``E`` and ``A`` agree on this structure -- and TCTL over it is a
metric temporal logic over the timeline.

Truth sets are therefore finite unions of rational intervals, periodic with
period ``P``, and every operator is exact interval arithmetic:

    EF_[a,b] phi  at t  iff  some s in t+[a,b] satisfies phi
                        iff  t in { s - u : s in T(phi), u in [a,b] }

so an interval ``(lo,hi)`` of ``T(phi)`` contributes ``(lo-b, hi-a)``.  ``AG`` is
the dual, ``AF``/``EG`` coincide with ``EF``/``AG`` here, and the unbounded cases
are decided by periodicity: a periodic set recurs forever, so ``EF_[a,inf)`` is
true everywhere unless the set is empty, and ``AG_[a,inf)`` holds only if the
set is everything.

Guarantee
---------
If ``holds_at_zero(phi)`` is true then the witness satisfies ``phi``, so ``phi``
is satisfiable -- with no appeal to the procedure under test.  An UNSATISFIABLE
verdict on such a formula is therefore an incompleteness instance.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from typing import List, Optional, Sequence, Tuple

# An interval is (lo, lo_closed, hi, hi_closed) with lo <= hi over the rationals.
Ival = Tuple[F, bool, F, bool]


# ── Periodic sets of times ──────────────────────────────────────────────────

def _nonempty(iv: Ival) -> bool:
    lo, lc, hi, hc = iv
    if lo > hi:
        return False
    if lo == hi:
        return lc and hc          # a single point survives only if both closed
    return True


def _normalise(ivs: Sequence[Ival]) -> List[Ival]:
    """Sort, merge overlapping/adjacent intervals, drop empties."""
    xs = sorted((iv for iv in ivs if _nonempty(iv)), key=lambda p: (p[0], not p[1]))
    out: List[Ival] = []
    for lo, lc, hi, hc in xs:
        if not out:
            out.append((lo, lc, hi, hc))
            continue
        plo, plc, phi, phc = out[-1]
        # merge when they overlap, or touch with at least one closed endpoint
        if lo < phi or (lo == phi and (phc or lc)):
            if hi > phi or (hi == phi and hc):
                out[-1] = (plo, plc, hi, hc)
            # else fully contained: keep previous
        else:
            out.append((lo, lc, hi, hc))
    return out


@dataclass(frozen=True)
class PSet:
    """A set of times, periodic with period ``P``, given by its trace on [0,P)."""

    P: F
    ivs: Tuple[Ival, ...]

    # -- constructors -------------------------------------------------------
    @staticmethod
    def empty(P: F) -> "PSet":
        return PSet(P, ())

    @staticmethod
    def full(P: F) -> "PSet":
        return PSet(P, ((F(0), True, P, False),))

    @staticmethod
    def of(P: F, ivs: Sequence[Ival]) -> "PSet":
        return PSet(P, tuple(_normalise(_wrap(ivs, P))))

    # -- predicates ---------------------------------------------------------
    def is_empty(self) -> bool:
        return not self.ivs

    def is_full(self) -> bool:
        return self.ivs == ((F(0), True, self.P, False),) or self._covers_period()

    def _covers_period(self) -> bool:
        # the complement is empty exactly when the period is covered
        return not _complement(self).ivs

    def contains(self, t: F) -> bool:
        t = t % self.P
        for lo, lc, hi, hc in self.ivs:
            if (lo < t < hi) or (t == lo and lc) or (t == hi and hc):
                return True
        return False


def _wrap(ivs: Sequence[Ival], P: F) -> List[Ival]:
    """Fold intervals of arbitrary position into the window [0,P)."""
    out: List[Ival] = []
    for lo, lc, hi, hc in ivs:
        if hi - lo >= P:                       # covers a whole period
            return [(F(0), True, P, False)]
        lo_m = lo % P
        hi_m = lo_m + (hi - lo)
        if hi_m <= P:
            out.append((lo_m, lc, hi_m, hc))
        else:                                   # straddles the wrap point
            out.append((lo_m, lc, P, False))
            out.append((F(0), True, hi_m - P, hc))
    return out


def _complement(s: PSet) -> PSet:
    ivs = list(s.ivs)
    out: List[Ival] = []
    cur, cur_closed = F(0), True
    for lo, lc, hi, hc in ivs:
        if lo > cur or (lo == cur and cur_closed and not lc):
            out.append((cur, cur_closed, lo, not lc))
        cur, cur_closed = hi, not hc
    if cur < s.P:
        out.append((cur, cur_closed, s.P, False))
    return PSet(s.P, tuple(_normalise(out)))


def _union(a: PSet, b: PSet) -> PSet:
    return PSet(a.P, tuple(_normalise(list(a.ivs) + list(b.ivs))))


def _inter(a: PSet, b: PSet) -> PSet:
    return _complement(_union(_complement(a), _complement(b)))


def _shift_window(s: PSet, a: int, b: Optional[int]) -> PSet:
    """``EF_[a,b]``: t holds iff some point of ``s`` lies in ``t+[a,b]``.

    ``t = s - u`` with ``u`` in the closed window, so an interval ``(lo,hi)``
    contributes ``(lo-b, hi-a)``.  ``b is None`` is the unbounded window: a
    periodic set recurs forever, so the answer is everywhere or nowhere.
    """
    if b is None:
        return PSet.full(s.P) if not s.is_empty() else PSet.empty(s.P)
    out = [(lo - F(b), lc, hi - F(a), hc) for lo, lc, hi, hc in s.ivs]
    return PSet.of(s.P, out)


def _box_window(s: PSet, a: int, b: Optional[int]) -> PSet:
    """``AG_[a,b]``, the dual of :func:`_shift_window`."""
    if b is None:
        return PSet.full(s.P) if s.is_full() else PSet.empty(s.P)
    return _complement(_shift_window(_complement(s), a, b))


# ── The witness structure ───────────────────────────────────────────────────

@dataclass
class Witness:
    """One location, self-loop, divergent time; atoms true on periodic sets."""

    period: F
    atoms: dict            # name -> PSet
    label: str = ""

    def truth(self, node) -> PSet:
        """Exact truth set of a formula node (see :mod:`shapes` for the AST)."""
        kind = node[0]
        if kind == "atom":
            return self.atoms[node[1]]
        if kind == "not":
            return _complement(self.truth(node[1]))
        if kind == "and":
            return _inter(self.truth(node[1]), self.truth(node[2]))
        if kind == "or":
            return _union(self.truth(node[1]), self.truth(node[2]))
        if kind in ("EF", "AF"):          # coincide on a single timeline
            return _shift_window(self.truth(node[3]), node[1], node[2])
        if kind in ("AG", "EG"):
            return _box_window(self.truth(node[3]), node[1], node[2])
        raise ValueError(f"unknown node {kind}")

    def holds_at_zero(self, node) -> bool:
        return self.truth(node).contains(F(0))


# ── A branching witness ─────────────────────────────────────────────────────
#
# Every structure above has one location, so all runs from a configuration carry
# the same atom trace and the path quantifiers coincide: `A` is never actually
# tested.  ``BranchWitness`` fixes that with two locations.
#
#     l0 --self-loop-->        l0 --switch-->  l1 --self-loop-->
#
# From a configuration in ``l0`` the runs are parameterised by the time the
# switch is taken (or never), so at any later time ``u`` some run is still in
# ``l0`` and some has moved to ``l1``.  Hence, writing ``T0`` and ``T1`` for the
# truth sets in the two locations,
#
#     EF_I phi  at l0  =  dilate( T0(phi) UNION T1(phi) )      -- pick a run
#     AG_I phi  at l0  =  erode ( T0(phi) INTERSECT T1(phi) )  -- all runs
#
# while ``l1`` has no branching and behaves like a single timeline.  Only ``EF``
# and ``AG`` are supported: ``EG``/``AF`` at ``l0`` quantify over the switch time
# in a way that is neither a union nor an intersection, and approximating them
# would void the oracle's guarantee.

@dataclass
class BranchWitness:
    """Two locations, a nondeterministic switch; `E` and `A` genuinely differ."""

    period: F
    loc0: dict             # atom -> PSet, truth in l0
    loc1: dict             # atom -> PSet, truth in l1
    label: str = ""

    def _truth(self, node):
        """Truth sets at (l0, l1)."""
        k = node[0]
        if k == "atom":
            return self.loc0[node[1]], self.loc1[node[1]]
        if k == "not":
            a, b = self._truth(node[1])
            return _complement(a), _complement(b)
        if k == "and":
            a0, a1 = self._truth(node[1])
            b0, b1 = self._truth(node[2])
            return _inter(a0, b0), _inter(a1, b1)
        if k == "or":
            a0, a1 = self._truth(node[1])
            b0, b1 = self._truth(node[2])
            return _union(a0, b0), _union(a1, b1)
        a, b, sub = node[1], node[2], node[3]
        s0, s1 = self._truth(sub)
        if k == "EF":
            return _shift_window(_union(s0, s1), a, b), _shift_window(s1, a, b)
        if k == "AG":
            return _box_window(_inter(s0, s1), a, b), _box_window(s1, a, b)
        raise ValueError(f"{k} is not supported on a branching witness")

    def holds_at_zero(self, node) -> bool:
        return self._truth(node)[0].contains(F(0))
