// ============================================================================
// satisfaction_set.cpp — S_X(mu) satisfaction sets (ETAPS2026 §4.2, §5.1)
// ============================================================================

#include "tctl/satisfaction_set.hpp"
#include "tctl/z3_solver.hpp"

#include <algorithm>

namespace tctl {

// ── Modality / interval helpers ──────────────────────────────────────────────

bool is_modality(NodeKind k) noexcept {
    switch (k) {
        case NodeKind::EU:  case NodeKind::AU:
        case NodeKind::ER:  case NodeKind::AR:
        case NodeKind::TimedEU: case NodeKind::TimedAU:
        case NodeKind::TimedER: case NodeKind::TimedAR:
            return true;
        default:
            return false;
    }
}

namespace {

bool is_until_kind(NodeKind k) noexcept {
    return k == NodeKind::EU || k == NodeKind::AU ||
           k == NodeKind::TimedEU || k == NodeKind::TimedAU;
}

bool is_timed_kind(NodeKind k) noexcept {
    return k == NodeKind::TimedEU || k == NodeKind::TimedAU ||
           k == NodeKind::TimedER || k == NodeKind::TimedAR;
}

// The window I of a modality, decoded into DBM-friendly bounds.
struct Interval {
    std::int32_t lo        = 0;      // lower bound value
    bool         lo_strict = false;  // ( vs [
    std::int32_t hi        = 0;      // upper bound value (ignored if hi_inf)
    bool         hi_inf    = true;   // no upper bound
    bool         hi_strict = false;  // ) vs ]
};

Interval interval_of(FormulaId mu, const FormulaFactory& f) {
    const FormulaNode& n = f.node(mu);
    Interval I;
    if (!is_timed_kind(n.kind)) {
        // Untimed modality ≡ I = [0, ∞).
        I.lo = 0; I.lo_strict = false; I.hi_inf = true;
        return I;
    }
    I.lo        = static_cast<std::int32_t>(n.time_lower.value);
    I.lo_strict = n.time_lower.is_strict;
    if (n.time_upper.is_infinity) {
        I.hi_inf = true;
    } else {
        I.hi_inf    = false;
        I.hi        = static_cast<std::int32_t>(n.time_upper.value);
        I.hi_strict = n.time_upper.is_strict;
    }
    return I;
}

// Constrain x_mu ∈ I on a ZoneSet in place.
void constrain_window(ZoneSet& zs, ClockId x_mu, const Interval& I) {
    zs.constrain_lower(x_mu, I.lo, I.lo_strict);
    if (!I.hi_inf) zs.constrain_upper(x_mu, I.hi, I.hi_strict);
}

// ── DNF over {propositional leaves, modalities} ──────────────────────────────

struct Clause {
    std::vector<FormulaId> lits;  // propositional / arithmetic literals
    std::vector<FormulaId> mods;  // top-level modalities in this clause
};

std::vector<Clause> to_dnf(FormulaId id, const FormulaFactory& f) {
    const FormulaNode& n = f.node(id);
    switch (n.kind) {
        case NodeKind::True:
            return {Clause{}};             // one always-true clause
        case NodeKind::False:
            return {};                     // unsatisfiable — no clauses
        case NodeKind::And: {
            auto A = to_dnf(n.children[0], f);
            auto B = to_dnf(n.children[1], f);
            std::vector<Clause> out;
            out.reserve(A.size() * B.size());
            for (const auto& ca : A)
                for (const auto& cb : B) {
                    Clause m = ca;
                    m.lits.insert(m.lits.end(), cb.lits.begin(), cb.lits.end());
                    m.mods.insert(m.mods.end(), cb.mods.begin(), cb.mods.end());
                    out.push_back(std::move(m));
                }
            return out;
        }
        case NodeKind::Or: {
            auto A = to_dnf(n.children[0], f);
            auto B = to_dnf(n.children[1], f);
            A.insert(A.end(), B.begin(), B.end());
            return A;
        }
        default:
            if (is_modality(n.kind)) return {Clause{{}, {id}}};
            return {Clause{{id}, {}}};     // propositional / arithmetic literal
    }
}

// Project clock c out of a ZoneSet (existential quantification): after pinning a
// sub-modality clock to its onset (x=0), free it so it no longer constrains the
// ambient space — the sub-modality's window is measured on its own clock only.
void free_clock(ZoneSet& zs, ClockId c) {
    ZoneSet out = ZoneSet::empty(zs.num_clocks());
    for (Zone z : zs.components()) { z.free(c); out.unite(ZoneSet::of(z)); }
    zs = std::move(out);
}

// Joint Z3 consistency of {X_prop ∧ lits}.  UNKNOWN is treated as consistent.
bool lits_consistent(const std::vector<FormulaId>& lits, const FormulaSet& X,
                     FormulaFactory& f) {
    Z3Checker z3(f);
    for (FormulaId x : X.elements()) z3.add_state_formula(x);
    for (FormulaId l : lits)         z3.add_state_formula(l);
    return z3.check() != Z3Result::UNSAT;
}

}  // namespace

// ── assign_clocks / max constant ─────────────────────────────────────────────

namespace {
void assign_clocks_rec(FormulaId id, FormulaFactory& f, ClockMap& cmap,
                       ClockId& next) {
    const FormulaNode& n = f.node(id);
    if (is_modality(n.kind) && cmap.find(id) == cmap.end())
        cmap[id] = next++;
    for (FormulaId c : n.children)
        if (c != kInvalidId) assign_clocks_rec(c, f, cmap, next);
}

std::int32_t max_constant_impl(FormulaId id, FormulaFactory& f) {
    const FormulaNode& n = f.node(id);
    std::int32_t m = 0;
    if (is_timed_kind(n.kind)) {
        m = std::max(m, static_cast<std::int32_t>(n.time_lower.value));
        if (!n.time_upper.is_infinity)
            m = std::max(m, static_cast<std::int32_t>(n.time_upper.value));
    }
    for (FormulaId c : n.children)
        if (c != kInvalidId) m = std::max(m, max_constant_impl(c, f));
    return m;
}
}  // namespace

ClockMap assign_clocks(FormulaId root, FormulaFactory& f) {
    ClockMap cmap;
    ClockId next = 1;  // clock 0 = reference
    assign_clocks_rec(root, f, cmap, next);
    return cmap;
}

std::int32_t max_constant(FormulaId root, FormulaFactory& f) {
    return max_constant_impl(root, f);
}

// ── Task 1: leaf region + node closure ──────────────────────────────────────

ZoneSet sat_leaf(FormulaId psi, const FormulaSet& X, FormulaFactory& f,
                 std::size_t num_clocks) {
    Z3Checker z3(f);
    for (FormulaId x : X.elements()) z3.add_state_formula(x);
    bool supported = z3.add_state_formula(psi);
    if (!supported)
        return ZoneSet::empty(num_clocks);  // contains a modality → holds_region
    return z3.check() == Z3Result::SAT ? ZoneSet::universe(num_clocks)
                                       : ZoneSet::empty(num_clocks);
}

bool node_closed(const FormulaSet& gamma, FormulaFactory& f) {
    Z3Checker z3(f);
    bool any = false;
    for (FormulaId g : gamma.elements())
        if (z3.add_state_formula(g)) any = true;
    if (!any) return false;  // no propositional content to be inconsistent
    return z3.check() == Z3Result::UNSAT;
}

// ── Task 2: fixpoints ────────────────────────────────────────────────────────

namespace {

constexpr int kMaxIter = 2000;  // finite lattice after extrapolation

// Least fixpoint for E/A(phi U_I psi):  S = mu Y. B ∪ (phiR ∩ down(Y)),
// B = psiR ∩ (x_mu ∈ I).  Guarded time-predecessor (exact for convex phiR).
ZoneSet until_region(const ZoneSet& phiR, const ZoneSet& psiR, const Interval& I,
                     ClockId x_mu, const std::vector<std::int32_t>& max) {
    ZoneSet B = psiR;
    constrain_window(B, x_mu, I);

    ZoneSet S = B;
    for (int it = 0; it < kMaxIter; ++it) {
        ZoneSet prev = S;
        ZoneSet d = S;
        d.down();
        d.intersect(phiR);
        S = B;
        S.unite(d);
        S.extrapolate(max);
        S.reduce();
        if (S.equals(prev)) break;
    }
    return S;
}

// Greatest fixpoint for release, via the dual: Q(phi R_I psi) holds exactly
// where the violating until E(¬phi U_I ¬psi) does not.
ZoneSet release_region(const ZoneSet& phiR, const ZoneSet& psiR, const Interval& I,
                       ClockId x_mu, std::size_t nc,
                       const std::vector<std::int32_t>& max) {
    ZoneSet notPhi = ZoneSet::universe(nc); notPhi.subtract(phiR);
    ZoneSet notPsi = ZoneSet::universe(nc); notPsi.subtract(psiR);
    ZoneSet viol = until_region(notPhi, notPsi, I, x_mu, max);
    ZoneSet S = ZoneSet::universe(nc);
    S.subtract(viol);
    S.extrapolate(max);
    S.reduce();
    return S;
}

}  // namespace

ZoneSet holds_region(FormulaId psi, const FormulaSet& X, const ClockMap& cmap,
                     std::size_t num_clocks,
                     const std::vector<std::int32_t>& max, FormulaFactory& f) {
    std::vector<Clause> clauses = to_dnf(psi, f);
    ZoneSet result = ZoneSet::empty(num_clocks);
    for (const Clause& cl : clauses) {
        if (!lits_consistent(cl.lits, X, f)) continue;  // clause impossible
        ZoneSet region = ZoneSet::universe(num_clocks);
        for (FormulaId m : cl.mods) {
            ZoneSet mr = satisfaction_set(m, X, cmap, num_clocks, max, f);
            // Sub-modality demanded now: pin its formula-clock to 0, then project
            // it out so it does not constrain the ambient clock space.
            ClockId xm = cmap.at(m);
            mr.constrain_lower(xm, 0, false);
            mr.constrain_upper(xm, 0, false);
            free_clock(mr, xm);
            region.intersect(mr);
        }
        result.unite(region);
    }
    result.extrapolate(max);
    result.reduce();
    return result;
}

ZoneSet satisfaction_set(FormulaId mu, const FormulaSet& X, const ClockMap& cmap,
                         std::size_t num_clocks,
                         const std::vector<std::int32_t>& max, FormulaFactory& f) {
    const FormulaNode& n = f.node(mu);
    FormulaId phi = n.children[0];
    FormulaId psi = n.children[1];
    ClockId   x_mu = cmap.at(mu);
    Interval  I = interval_of(mu, f);

    ZoneSet phiR = holds_region(phi, X, cmap, num_clocks, max, f);
    ZoneSet psiR = holds_region(psi, X, cmap, num_clocks, max, f);

    if (is_until_kind(n.kind))
        return until_region(phiR, psiR, I, x_mu, max);
    return release_region(phiR, psiR, I, x_mu, num_clocks, max);
}

ZoneSet satisfaction_set(FormulaId mu, const FormulaSet& X, FormulaFactory& f,
                         ClockId* out_x_mu, std::size_t* out_num_clocks) {
    ClockMap cmap = assign_clocks(mu, f);
    const std::size_t nc = 1 + cmap.size();
    const std::int32_t M = max_constant_impl(mu, f);
    std::vector<std::int32_t> max(nc, M);
    max[0] = 0;
    if (out_x_mu)       *out_x_mu = cmap.at(mu);
    if (out_num_clocks) *out_num_clocks = nc;
    return satisfaction_set(mu, X, cmap, nc, max, f);
}

}  // namespace tctl
