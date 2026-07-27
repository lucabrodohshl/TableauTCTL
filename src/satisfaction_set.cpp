/// @file satisfaction_set.cpp
/// @brief Satisfaction sets S_X(mu), and the leaf decision procedure.
///
/// The cover rule discharges a demanded modality against its satisfaction set,
/// computed as a Knaster--Tarski fixpoint over unions of zones: least for an
/// until, greatest for a release.  This file also decides node closure, where
/// the common case is settled by a complementary-literal scan and only the rest
/// reaches the theory solver.

#include "tctl/satisfaction_set.hpp"

#include <memory>
#include <unordered_map>
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

// Constrain x_mu ∈ I on a ZoneSet in place.  Untimed modalities have no clock
// and window [0,∞), so there is nothing to constrain.
void constrain_window(ZoneSet& zs, ClockId x_mu, const Interval& I) {
    if (x_mu == kNoClock) return;
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


// ── Leaf decision procedure ─────────────────────────────────────────────────
//
// Every node the search touches is tested for closure, and every DNF clause of
// a satisfaction set is tested for consistency.  Both were answered by building
// a fresh z3::context, which allocates an ast_manager, a rewriter stack and a
// tactic parameter table -- so context *construction*, not solving, dominated
// the search.  Two changes remove it from the hot path: the common case is
// decided by a complementary-literal scan with no solver at all, and the
// remaining theory queries share one context per formula factory.

// Complementary-literal scan over a node's leaves.  A saturated node carries
// atoms, negated atoms, True/False and modalities; anything else (arithmetic,
// or a connective left unsaturated) is beyond this scan and needs the theory.
class LeafScan {
public:
    void add(FormulaId id, const FormulaFactory& f) {
        if (theory_) return;
        const FormulaNode& n = f.node(id);
        switch (n.kind) {
            case NodeKind::False: clash_ = true; return;
            case NodeKind::True:  return;
            case NodeKind::Atom:  pos_.push_back(&n.atom_name); return;
            case NodeKind::Not: {
                const FormulaNode& c = f.node(n.children[0]);
                if (c.kind == NodeKind::Atom)      neg_.push_back(&c.atom_name);
                else if (c.kind == NodeKind::True) clash_ = true;
                else if (c.kind != NodeKind::False) theory_ = true;
                return;
            }
            default:
                // A modality is discharged by the cover rule, never by a leaf
                // clash, so it neither closes the node nor needs the theory.
                if (!is_modality(n.kind)) theory_ = true;
                return;
        }
    }

    bool needs_theory() const { return theory_; }

    bool inconsistent() const {
        if (clash_) return true;
        for (const std::string* a : pos_)
            for (const std::string* b : neg_)
                if (*a == *b) return true;          // p AND NOT p
        return false;
    }

private:
    std::vector<const std::string*> pos_, neg_;
    bool clash_ = false, theory_ = false;
};

struct IdVecHash {
    std::size_t operator()(const FormulaIdVec& v) const noexcept {
        std::size_t h = 1469598103934665603ull;
        for (FormulaId id : v) { h ^= static_cast<std::size_t>(id); h *= 1099511628211ull; }
        return h;
    }
};

// One reused theory context per factory, plus memo tables for the two leaf
// predicates.  Keyed on the factory so a second Tableau run starts clean.
struct TheorySession {
    std::uint64_t owner = 0;          // FormulaFactory::serial(), never an address
    std::uint64_t epoch = 0;          // interning generation the handles belong to
    std::unique_ptr<Z3Checker> checker;
    std::unordered_map<std::uint32_t, bool> closed;        // Gamma handle -> closed
    std::unordered_map<std::uint64_t, bool> consistent;    // clause+context -> consistent
    std::uint64_t queries = 0;
};

TheorySession& session(const FormulaFactory& f) {
    // The memo tables below are keyed by pooled vectors, and the pool is itself
    // a thread-local destroyed in reverse order of construction.  Touching it
    // first makes it the OLDER thread-local, so it outlives the tables that
    // return buffers to it at thread exit.
    ptctlmc::detail::tls_dbm_pool();
    static thread_local TheorySession s;
    // Both tables are keyed by interned set handles, which a reset recycles, so
    // the epoch invalidates them just as the factory serial does.
    const std::uint64_t ep = formula_set_epoch();
    if (s.owner != f.serial() || s.epoch != ep) {
        s = TheorySession{};
        s.owner = f.serial();
        s.epoch = ep;
    }
    return s;
}

// The shared context accumulates ASTs across resets, so it is rebuilt
// periodically to keep the footprint flat on long runs.
Z3Checker& theory(const FormulaFactory& f) {
    TheorySession& s = session(f);
    ++s.queries;
    if (!s.checker || s.queries % 50000 == 0) s.checker = std::make_unique<Z3Checker>(f);
    else                                      s.checker->reset();
    return *s.checker;
}

// Joint consistency of {X_prop AND lits}.  UNKNOWN is treated as consistent.
bool lits_consistent(const std::vector<FormulaId>& lits, const FormulaSet& X,
                     FormulaFactory& f) {
    TheorySession& s = session(f);
    std::size_t lit_hash = 1469598103934665603ull;
    for (FormulaId l : lits) { lit_hash ^= static_cast<std::size_t>(l); lit_hash *= 1099511628211ull; }
    const std::uint64_t key = (static_cast<std::uint64_t>(lit_hash) << 32) ^ X.handle();
    if (auto it = s.consistent.find(key); it != s.consistent.end()) return it->second;

    LeafScan scan;
    for (FormulaId x : X.elements()) scan.add(x, f);
    for (FormulaId l : lits)         scan.add(l, f);

    bool result;
    if (!scan.needs_theory()) {
        result = !scan.inconsistent();
    } else {
        Z3Checker& z3 = theory(f);
        for (FormulaId x : X.elements()) z3.add_state_formula(x);
        for (FormulaId l : lits)         z3.add_state_formula(l);
        result = z3.check() != Z3Result::UNSAT;
    }
    session(f).consistent.emplace(key, result);
    return result;
}

}  // namespace

// ── assign_clocks / max constant ─────────────────────────────────────────────

namespace {
void assign_clocks_rec(FormulaId id, FormulaFactory& f, ClockMap& cmap,
                       ClockId& next) {
    const FormulaNode& n = f.node(id);
    // Only *timed* modalities need a formula-clock.  An untimed modality has
    // window [0,∞) and no deadline, so a clock for it would only add spurious
    // difference constraints (x_i - x_j) that fracture zones — the M^O(n^2)
    // blow-up — without ever being tested.
    if (is_timed_kind(n.kind) && cmap.find(id) == cmap.end())
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

// ── Leaf regions and node closure ───────────────────────────────────────────

ZoneSet sat_leaf(FormulaId psi, const FormulaSet& X, FormulaFactory& f,
                 std::size_t num_clocks) {
    Z3Checker& z3 = theory(f);
    for (FormulaId x : X.elements()) z3.add_state_formula(x);
    bool supported = z3.add_state_formula(psi);
    if (!supported)
        return ZoneSet::empty(num_clocks);  // contains a modality → holds_region
    return z3.check() == Z3Result::SAT ? ZoneSet::universe(num_clocks)
                                       : ZoneSet::empty(num_clocks);
}

// Fast propositional closure: a saturated node's leaves are atoms, ¬atoms,
// True/False, or arithmetic constraints.  When no arithmetic is present we can
// decide consistency by a complementary-literal scan and skip Z3 entirely —
// Z3 context construction per node is otherwise the dominant cost.
bool node_closed(const FormulaSet& gamma, FormulaFactory& f) {
    TheorySession& s = session(f);
    const std::uint32_t key = gamma.handle();
    if (auto it = s.closed.find(key); it != s.closed.end()) return it->second;

    LeafScan scan;
    for (FormulaId g : gamma.elements()) scan.add(g, f);

    bool result;
    if (!scan.needs_theory()) {
        result = scan.inconsistent();
    } else {
        Z3Checker& z3 = theory(f);
        bool any = false;
        for (FormulaId g : gamma.elements())
            if (z3.add_state_formula(g)) any = true;
        result = any && z3.check() == Z3Result::UNSAT;
    }
    session(f).closed.emplace(key, result);
    return result;
}

// ── Fixpoints ───────────────────────────────────────────────────────────────

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

namespace {
// Cache key for S_X(mu, X): mu plus the sorted context formula ids.
// (mu, X) as one word: X is interned, so its identity is already a 32-bit
// handle and the key needs no formatting.
std::uint64_t sat_key(FormulaId mu, const FormulaSet& X) {
    return (static_cast<std::uint64_t>(mu) << 32) | X.handle();
}

// holds_region threaded with the S_X cache.
ZoneSet holds_region_cached(FormulaId psi, const FormulaSet& X, const ClockMap& cmap,
                            std::size_t num_clocks,
                            const std::vector<std::int32_t>& max, FormulaFactory& f,
                            SatCache& cache) {
    std::vector<Clause> clauses = to_dnf(psi, f);
    ZoneSet result = ZoneSet::empty(num_clocks);
    for (const Clause& cl : clauses) {
        if (!lits_consistent(cl.lits, X, f)) continue;  // clause impossible
        ZoneSet region = ZoneSet::universe(num_clocks);
        for (FormulaId m : cl.mods) {
            ZoneSet mr = satisfaction_set(m, X, cmap, num_clocks, max, f, cache);
            ClockId xm = clock_of(cmap, m);
            if (xm != kNoClock) {           // timed sub-modality: onset, project out
                mr.constrain_lower(xm, 0, false);
                mr.constrain_upper(xm, 0, false);
                free_clock(mr, xm);
            }
            region.intersect(mr);
        }
        result.unite(region);
    }
    result.extrapolate(max);
    result.reduce();
    return result;
}
}  // namespace

ZoneSet holds_region(FormulaId psi, const FormulaSet& X, const ClockMap& cmap,
                     std::size_t num_clocks,
                     const std::vector<std::int32_t>& max, FormulaFactory& f) {
    SatCache cache;
    return holds_region_cached(psi, X, cmap, num_clocks, max, f, cache);
}

ZoneSet satisfaction_set(FormulaId mu, const FormulaSet& X, const ClockMap& cmap,
                         std::size_t num_clocks,
                         const std::vector<std::int32_t>& max, FormulaFactory& f,
                         SatCache& cache) {
    const std::uint64_t key = sat_key(mu, X);
    if (auto it = cache.find(key); it != cache.end()) return it->second;

    const FormulaNode& n = f.node(mu);
    FormulaId phi = n.children[0];
    FormulaId psi = n.children[1];
    ClockId   x_mu = clock_of(cmap, mu);   // kNoClock if mu is untimed
    Interval  I = interval_of(mu, f);

    ZoneSet phiR = holds_region_cached(phi, X, cmap, num_clocks, max, f, cache);
    ZoneSet psiR = holds_region_cached(psi, X, cmap, num_clocks, max, f, cache);

    ZoneSet res = is_until_kind(n.kind)
        ? until_region(phiR, psiR, I, x_mu, max)
        : release_region(phiR, psiR, I, x_mu, num_clocks, max);
    cache.emplace(key, res);
    return res;
}

ZoneSet satisfaction_set(FormulaId mu, const FormulaSet& X, const ClockMap& cmap,
                         std::size_t num_clocks,
                         const std::vector<std::int32_t>& max, FormulaFactory& f) {
    SatCache cache;
    return satisfaction_set(mu, X, cmap, num_clocks, max, f, cache);
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
