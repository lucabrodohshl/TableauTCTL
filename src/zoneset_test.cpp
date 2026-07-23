// ============================================================================
// zoneset_test.cpp — behavioural tests for ZoneSet (federation of zones)
// ============================================================================
// Exposes `zoneset_run_tests()` returning the number of FAILED checks (0 = ok).
// Wired into `--selftest`; also runnable standalone.
// ============================================================================

#include "tctl/zoneset.hpp"
#include "tctl/zone.hpp"

#include <iostream>
#include <string>
#include <vector>

namespace tctl {

namespace {

int g_failures = 0;

void check(bool cond, const std::string& what) {
    if (!cond) {
        ++g_failures;
        std::cerr << "  [ZoneSet FAIL] " << what << "\n";
    }
}

// Build the single-clock (dim=2) zone { lo <= x <= hi } over clock 1.
// hi < 0 means no upper bound (x >= lo).
Zone iv(std::int32_t lo, std::int32_t hi, bool lo_strict = false, bool hi_strict = false) {
    Zone z = Zone::universe(2);
    if (lo > 0 || lo_strict) z.add_lower_bound(1, lo, lo_strict);
    if (hi >= 0) z.add_upper_bound(1, hi, hi_strict);
    return z;
}

}  // namespace

int zoneset_run_tests() {
    g_failures = 0;

    // ── construction / emptiness ────────────────────────────────────────
    check(ZoneSet::empty(2).is_empty(), "empty is empty");
    check(ZoneSet::empty(2).size() == 0, "empty has 0 members");
    check(!ZoneSet::universe(2).is_empty(), "universe is non-empty");
    check(!ZoneSet::of(iv(0, 3)).is_empty(), "of(x<=3) non-empty");
    check(ZoneSet::of(Zone::empty(2)).is_empty(), "of(empty zone) is empty");
    check(ZoneSet::empty(2).num_clocks() == 2, "num_clocks");

    // ── union of two disjoint zones ─────────────────────────────────────
    Zone le3 = iv(0, 3);          // x <= 3
    Zone ge5 = iv(5, -1);         // x >= 5
    ZoneSet U = ZoneSet::of(le3);
    U.unite(ge5).reduce();
    check(U.size() == 2, "disjoint union has 2 convex components");
    check(U.contains(le3), "U contains x<=3");
    check(U.contains(ge5), "U contains x>=5");
    check(U.contains(iv(1, 2)), "U contains x in [1,2]");
    check(!U.contains(iv(3, 5)), "U does NOT contain x in [3,5] (spans gap)");
    check(!U.contains(ZoneSet::universe(2).components().front()), "U != universe");

    // ── subset / equality ───────────────────────────────────────────────
    check(ZoneSet::of(le3).is_subset_of(U), "{x<=3} subset of U");
    check(!U.is_subset_of(ZoneSet::of(le3)), "U not subset of {x<=3}");
    check(ZoneSet::of(le3).equals(ZoneSet::of(le3)), "equality reflexive");
    check(!ZoneSet::of(le3).equals(U), "{x<=3} != U");

    // ── intersection ────────────────────────────────────────────────────
    ZoneSet I = U;                                  // {x<=3} ∪ {x>=5}
    I.intersect(iv(0, 10)).reduce();                // ∩ {x<=10} = {x<=3} ∪ {x in [5,10]}
    check(I.contains(iv(1, 2)), "intersection keeps x in [1,2]");
    check(I.contains(iv(5, 10)), "intersection keeps x in [5,10]");
    check(!I.contains(iv(20, 20)), "intersection drops x=20");

    // ── difference ──────────────────────────────────────────────────────
    ZoneSet D = ZoneSet::universe(2);
    D.subtract(ZoneSet::of(le3)).reduce();          // universe \ {x<=3} = {x>3}
    check(D.contains(iv(4, 5)), "universe \\ {x<=3} contains x in [4,5]");
    check(!D.contains(iv(1, 2)), "universe \\ {x<=3} drops x in [1,2]");

    // ── single-clock guards ─────────────────────────────────────────────
    ZoneSet C = ZoneSet::universe(2);
    C.constrain_upper(1, 5, /*strict=*/false);      // x <= 5
    check(C.contains(le3), "constrain_upper x<=5 contains x<=3");
    check(!C.contains(ge5), "constrain_upper x<=5 drops x>=5");
    ZoneSet C2 = ZoneSet::universe(2);
    C2.constrain_lower(1, 2, /*strict=*/true);       // x > 2
    check(!C2.contains(iv(0, 2)), "constrain_lower x>2 drops x in [0,2]");
    check(C2.contains(iv(3, 4)), "constrain_lower x>2 keeps x in [3,4]");

    // ── reset ───────────────────────────────────────────────────────────
    ZoneSet R = ZoneSet::of(ge5);                    // x >= 5
    R.reset(1);                                      // x := 0
    check(R.contains(Zone::zero(2)), "after reset x=0 present");
    check(!R.contains(ge5), "after reset x>=5 absent");

    // ── time-successor ──────────────────────────────────────────────────
    ZoneSet T = ZoneSet::of(Zone::zero(2));          // x = 0
    T.up();                                          // x >= 0  (= universe for 1 clock)
    check(T.contains(ge5), "up of {x=0} contains x>=5");
    check(T.contains(iv(0, 3)), "up of {x=0} contains x in [0,3]");

    // ── inverse delay (time-predecessors) ──────────────────────────────
    // down({x in [2,4]}) = { v | ∃t≥0. v+t in [2,4] } = { x <= 4 }.
    ZoneSet Dn = ZoneSet::of(iv(2, 4));
    Dn.down();
    check(Dn.contains(iv(0, 1)), "down([2,4]) contains x in [0,1] (can wait into window)");
    check(Dn.contains(iv(4, 4)), "down([2,4]) contains x=4 (already in window)");
    check(!Dn.contains(iv(5, 5)), "down([2,4]) excludes x=5 (cannot travel back in time)");

    // ── max-constant extrapolation (M=3 on clock 1) ─────────────────────
    std::vector<std::int32_t> maxb = {0, 3};
    ZoneSet E = ZoneSet::of(ge5);                    // x >= 5
    check(!E.contains(iv(4, 4)), "before extrapolation x=4 not in {x>=5}");
    E.extrapolate(maxb);                             // x>=5 relaxes to x>3
    check(E.contains(iv(4, 4)), "after extrapolation x=4 in relaxed set");
    ZoneSet E2 = E;
    E2.extrapolate(maxb);
    check(E.equals(E2), "extrapolation idempotent");

    // ── components() round-trip ─────────────────────────────────────────
    std::vector<Zone> comps = U.components();
    check(comps.size() == 2, "components() yields 2 zones");
    ZoneSet rebuilt = ZoneSet::empty(2);
    for (const Zone& z : comps) rebuilt.unite(z);
    rebuilt.reduce();
    check(rebuilt.equals(U), "rebuild from components equals U");

    return g_failures;
}

}  // namespace tctl
