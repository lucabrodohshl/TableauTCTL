/// @file tableau.cpp
/// @brief Implementation of the TCTL satisfiability tableau (see tableau.hpp).
///
/// Contains the whole construction: saturation, the cover rule against
/// @f$S_X(\mu)@f$, the pursuit rules (U•, Rsplit, R•), the two
/// successor rules (Delay, EX), and the depth-first AND–OR search with loop
/// detection.  A candidate loop is accepting when (i) every until pursuit
/// active at its head is discharged on the segment and (ii) the loop is
/// time-progressing, which is what excludes Zeno witnesses.
///
/// Section references are to L. Brodo, G. Scalora and S. Henkler,
/// *A Tableau for TCTL*.

#include "tctl/tableau.hpp"
#include "tctl/satisfaction_set.hpp"
#include "tctl/z3_solver.hpp"
#include "tctl/zoneset.hpp"

#include "tctl/timed_automaton.hpp"

#include "ptctlmc/mindbm.hpp"

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace tctl {

namespace {

// ── Modality classification ──────────────────────────────────────────────────
bool is_until_modality(NodeKind k) noexcept {
    return k == NodeKind::EU || k == NodeKind::AU ||
           k == NodeKind::TimedEU || k == NodeKind::TimedAU;
}
bool is_universal(NodeKind k) noexcept {
    return k == NodeKind::AU || k == NodeKind::AR ||
           k == NodeKind::TimedAU || k == NodeKind::TimedAR;
}
bool is_timed(NodeKind k) noexcept {
    return k == NodeKind::TimedEU || k == NodeKind::TimedAU ||
           k == NodeKind::TimedER || k == NodeKind::TimedAR;
}

FormulaSet gamma_without(const FormulaSet& g, FormulaId drop) {
    // The source is already sorted and unique, so the result is too: build it
    // whole and intern once rather than interning after every element.
    FormulaIdVec out;
    out.reserve(g.elements().size());
    for (FormulaId id : g.elements())
        if (id != drop) out.push_back(id);
    return FormulaSet::from_sorted(out);
}

// ── Window I of a modality ───────────────────────────────────────────────────
struct Window {
    std::int32_t lo = 0; bool lo_strict = false;
    bool hi_inf = true;  std::int32_t hi = 0; bool hi_strict = false;
};
Window window_of(FormulaId mu, const FormulaFactory& f) {
    const FormulaNode& n = f.node(mu);
    Window w;
    if (!is_timed(n.kind)) { w.lo = 0; w.lo_strict = false; w.hi_inf = true; return w; }
    w.lo = static_cast<std::int32_t>(n.time_lower.value);
    w.lo_strict = n.time_lower.is_strict;
    if (n.time_upper.is_infinity) { w.hi_inf = true; }
    else { w.hi_inf = false; w.hi = static_cast<std::int32_t>(n.time_upper.value);
           w.hi_strict = n.time_upper.is_strict; }
    return w;
}

// Z ∩ (x_mu ∈ I), in place.  Untimed modalities have no clock / window [0,∞).
void constrain_in_window(Zone& z, ClockId x, const Window& w) {
    if (x == kNoClock) return;
    z.add_lower_bound(x, w.lo, w.lo_strict);
    if (!w.hi_inf) z.add_upper_bound(x, w.hi, w.hi_strict);
}
// Apply Inv(N) = AND deadlines, in place.
void apply_inv(Zone& z, const PooledVec<Deadline>& D) {
    for (const Deadline& d : D)
        z.add_upper_bound(d.x_mu, static_cast<std::int32_t>(d.bound), d.strict);
}
// Remove a deadline on clock x from D.
PooledVec<Deadline> drop_deadline(const PooledVec<Deadline>& D, ClockId x) {
    PooledVec<Deadline> out;
    for (const Deadline& d : D) if (d.x_mu != x) out.push_back(d);
    return out;
}

}  // namespace

// ── Cover rule (paper §4.2) ─────────────────────────────────────────────────

CoverResult apply_cover(const Node& n, FormulaId mu,
                        const std::map<FormulaId, ClockId>& cmap,
                        std::size_t num_clocks,
                        const std::vector<std::int32_t>& max, FormulaFactory& f,
                        SatCache& sx_cache, bool solo_launch, bool reuse_witness,
                        bool window_reuse) {
    // A persistent context such as AG μ re-demands μ at uncountably many onsets.
    // A single formula-clock x_μ serves them all (§4.2): the dense family of
    // onsets is absorbed into one finite union of zones, against which the cover
    // rule decides every demand.  So when μ is already being pursued, discharge
    // the new demand against that pursuit rather than launching a second one —
    // launching again would grow the pursuit set, and with it the node key,
    // without bound, so no two nodes would ever compare equal and the search
    // would not terminate.
    for (const Pursuit& p : n.pursuits) {
        if (p.mu == mu) {
            CoverResult only;
            only.kind = CoverResult::Kind::Cover;
            Node discharge;
            discharge.Gamma = gamma_without(n.Gamma, mu);
            discharge.X = n.X; discharge.Z = n.Z; discharge.O = n.O;
            discharge.D = n.D; discharge.pursuits = n.pursuits; discharge.phase = n.phase;
            discharge.witnessed = n.witnessed;
            // The re-demand itself is the evidence that this demand is
            // persistent.  Discharging it against the live pursuit is sound for
            // the *window*, but nothing then bounds the time to the NEXT
            // witness -- which is the rate contradiction.  Mark the pursuit so
            // its (U-stop) rolls the clock over instead of retiring it.
            const Window rw = window_of(mu, f);
            if (is_until_modality(f.node(mu).kind) && !rw.hi_inf &&
                rw.lo == 0 && !rw.lo_strict && clock_of(cmap, mu) != kNoClock) {
                for (Pursuit& q : discharge.pursuits)
                    if (q.mu == mu) q.persistent = true;
            }
            only.children.push_back(std::move(discharge));
            return only;
        }
    }

    // Likewise once mu has been witnessed on this branch: the completed pursuit
    // already realises it, and relaunching would only restart the same witness at
    // a later onset — which is what turns a persistent demand into an unbounded
    // chain of relaunches and, with it, a cycle the loop test must reject.
    if (reuse_witness && n.witnessed.contains(mu)) {
        CoverResult only;
        only.kind = CoverResult::Kind::Cover;
        Node discharge;
        discharge.Gamma = gamma_without(n.Gamma, mu);
        discharge.X = n.X; discharge.Z = n.Z; discharge.O = n.O;
        discharge.D = n.D; discharge.pursuits = n.pursuits; discharge.phase = n.phase;
        discharge.witnessed = n.witnessed;
        only.children.push_back(std::move(discharge));
        return only;
    }

    // TCTL_WINDOW_REUSE -- the "overlapping windows" side condition on (Cov),
    // evaluated and REJECTED.  **UNSOUND.**  See the note in the header.
    //
    // The idea: discharge a re-demand against a settled pursuit only when the
    // zone proves the new onset lies inside the window the earlier pursuit
    // already covered, i.e. Z |= x_mu in I.  It is strictly narrower than the
    // `witnessed` shortcut -- and still wrong, because the direction of the
    // containment is the wrong one.  The settled pursuit's witness sits at
    // x_mu = v for some v in I *already passed*; the new demand asks for a
    // witness at v' - x_mu in I with v' >= x_mu, i.e. in the window's forward
    // translate.  Knowing that the onset itself fell inside the old window says
    // nothing about the old witness lying inside the new one.
    if (window_reuse && n.witnessed.contains(mu)) {
        const ClockId xw = clock_of(cmap, mu);
        Zone probe = n.Z;
        constrain_in_window(probe, xw, window_of(mu, f));
        if (n.Z.is_subset_of(probe)) {              // Z |= x_mu in I
            CoverResult only;
            only.kind = CoverResult::Kind::Cover;
            Node discharge;
            discharge.Gamma = gamma_without(n.Gamma, mu);
            discharge.X = n.X; discharge.Z = n.Z; discharge.O = n.O;
            discharge.D = n.D; discharge.pursuits = n.pursuits;
            discharge.phase = n.phase; discharge.witnessed = n.witnessed;
            only.children.push_back(std::move(discharge));
            return only;
        }
    }

    ZoneSet SX = satisfaction_set(mu, n.X, cmap, num_clocks, max, f, sx_cache);
    const ClockId x_mu = clock_of(cmap, mu);    // kNoClock if mu is untimed

    // Onset: the launch resets x_mu, so start measuring the window now by
    // *resetting* x_mu (not intersecting with x_mu=0 — the clock may already
    // carry a value from an earlier, discharged launch of the same mu).  An
    // untimed modality has no clock, so the onset zone is just n.Z.
    Zone Zc = n.Z;
    if (x_mu != kNoClock) Zc.reset(x_mu);

    CoverResult res;
    if (Zc.is_empty()) { res.kind = CoverResult::Kind::Close; return res; }

    const NodeKind kind = f.node(mu).kind;
    const bool until_kind = is_until_modality(kind);

    Node base;
    base.Gamma = gamma_without(n.Gamma, mu);
    base.X = n.X; base.Z = n.Z; base.O = n.O; base.D = n.D;
    base.pursuits = n.pursuits; base.phase = n.phase; base.witnessed = n.witnessed;

    if (SX.contains(Zc)) {
        res.kind = CoverResult::Kind::Cover;
        Node discharge = base;
        Node launch = base;
        if (x_mu != kNoClock) {
            launch.Z.reset(x_mu);
            launch.just_reset.push_back(x_mu);
            // keep O sorted; it is written once per launch and never searched
            launch.O.emplace_back(mu, x_mu);
            std::sort(launch.O.begin(), launch.O.end());
        }
        // TCTL_SOLO_LAUNCH -- an experiment, kept as a record.  **UNSOUND.**
        //
        // The idea was that an existential modality still demanded here asks
        // for a run branching off this configuration, not for anything about
        // mu's witness run, so the launch child could drop it and let the
        // AND-sibling `discharge` build its witness separately.  That would
        // turn k demanded modalities from 2^k leaves --- one carrying k
        // formula-clocks in a single zone --- into k+1, cutting the live clock
        // count per node to one.
        //
        // It is wrong, and the reason is worth recording.  The children of the
        // (Cov) fork are not independent proofs: they describe *one*
        // configuration, whose propositional labelling has to satisfy every
        // demand at once.  The cross-product leaf is exactly what forces the
        // demands into a single node where a contradiction between them can
        // close it.  Drop it and `EG p & EG !p` reports SATISFIABLE: one branch
        // unfolds EG p and asserts p, another unfolds EG !p and asserts !p,
        // each node consistent on its own, the contradiction never met.  The
        // default rule builds the leaf carrying both pursuits, whose Gamma
        // holds p and !p together, and closes it.
        //
        // A sound version would have to check the immediate obligations of
        // every demand against the shared labelling before separating --- and
        // extracting "what does this modality require *now*" is itself an
        // unfolding, which is what launching does.  That is a change to the
        // calculus, not a filter on this rule.
        if (solo_launch) {
            FormulaIdVec keep;
            for (FormulaId id : launch.Gamma.elements()) {
                const NodeKind k2 = f.node(id).kind;
                if (!is_modality(k2) || is_universal(k2)) keep.push_back(id);
            }
            launch.Gamma = FormulaSet::from_sorted(keep);
        }
        Pursuit p; p.mu = mu; p.x_mu = x_mu;
        p.stage = Pursuit::Stage::Here; p.part = Pursuit::Part::Whole;
        p.is_until = until_kind;
        launch.pursuits.push_back(p);
        // A deadline only for a *timed* universal until (real clock + finite
        // window).  Untimed A-until has no clock and window [0,∞) → no deadline.
        // (Guard on x_mu: an untimed AU node's time_upper.is_infinity is a
        // default-constructed false, so this must not rely on it alone.)
        if (x_mu != kNoClock && is_universal(kind) && until_kind) {
            const FormulaNode& mn = f.node(mu);
            if (!mn.time_upper.is_infinity)
                launch.D.push_back(Deadline{x_mu, mn.time_upper.value,
                                            mn.time_upper.is_strict});
        }
        res.children.push_back(std::move(discharge));
        res.children.push_back(std::move(launch));
        return res;
    }

    ZoneSet inter = ZoneSet::of(Zc);
    inter.intersect(SX);
    if (inter.is_empty()) { res.kind = CoverResult::Kind::Close; return res; }

    res.kind = CoverResult::Kind::PartialCover;
    for (const Zone& comp : inter.components()) {
        Node child = base;
        child.Gamma = n.Gamma;   // keep mu, re-demand on narrowed zone
        child.Z = comp;
        res.children.push_back(std::move(child));
    }
    return res;
}

// ── Engine ───────────────────────────────────────────────────────────────────

namespace {

struct Expansion {
    enum class Kind { Closed, And, Or } kind = Kind::Closed;
    std::vector<Node> children;
};

class Engine {
public:
    static constexpr std::uint32_t kNoRegion = static_cast<std::uint32_t>(-1);

    Engine(FormulaFactory& f, FormulaId root, double timeout_s,
           bool keep_graph = false)
        : f_(f), keep_graph_(keep_graph) {
        if (timeout_s > 0) {
            deadline_ = std::chrono::steady_clock::now() +
                        std::chrono::duration_cast<std::chrono::steady_clock::duration>(
                            std::chrono::duration<double>(timeout_s));
            has_deadline_ = true;
        }
        cmap_ = assign_clocks(root, f);
        nc_ = 1 + cmap_.size();
        std::int32_t M = max_constant(root, f);
        max_.assign(nc_, M);
        max_[0] = 0;
        collect_boundaries(root, f);
        collect_clock_bounds(root, f);
        collect_lu_bounds(root, f);
        // A formula-clock is only ever compared against the endpoints of its own
        // window, so extrapolating every clock at the global maximum constant M
        // preserves distinctions no guard can observe.  Per-clock maxima are
        // sound because every guard is single-clock (§3), and they attack the
        // M^O(K^2) zone count of Lemma 1 directly.
        for (ClockId c = 1; c < nc_; ++c)
            max_[c] = clock_bounds_[c].empty() ? 0 : clock_bounds_[c].back();
        debug_ = std::getenv("TCTL_DEBUG") != nullptr;
        // Extra_LU for node identity.  MEASURED INCOMPLETE -- see the note on
        // #canon_zone.  Off by default; kept for the record and for experiments.
        extra_lu_ = std::getenv("TCTL_EXTRA_LU") != nullptr;
        solo_launch_ = std::getenv("TCTL_SOLO_LAUNCH") != nullptr;
        // Neither shortcut is in the calculus: the paper's (Cov) always yields
        // discharge + launch.  Both are engine additions and both are on by
        // default; TCTL_NO_WITNESS_REUSE removes them together, since dropping
        // the discharge shortcut while still *recording* the witness would keep
        // the set growing inside the node key and stop loops from ever closing.
        // UNSOUND, and now off by default: it discharges a re-demand against a
        // pursuit settled at an *earlier* onset, which is what made
        // `AG(AF q) & EF(AG !q)` come out SAT.  Dead-clock elimination below is
        // what makes paying for its removal affordable.  TCTL_WITNESS_REUSE
        // restores it for A/B measurement.
        reuse_witness_ = std::getenv("TCTL_WITNESS_REUSE") != nullptr;
        // The "overlapping windows" side condition, kept as a recorded
        // experiment; selecting it replaces the unconditional shortcut.
        window_reuse_ = std::getenv("TCTL_WINDOW_REUSE") != nullptr;
        if (window_reuse_) reuse_witness_ = false;
        record_witness_ = reuse_witness_ || window_reuse_;
        // Exact dead-clock elimination (see #collapse_dead_clocks).  Now on by
        // default: it is what pays for removing the witness shortcut above.
        free_dead_ = std::getenv("TCTL_NO_FREE_DEAD_CLOCKS") == nullptr;
        verify_decode_ = std::getenv("TCTL_VERIFY_DECODE") != nullptr;
        // SCC acceptance is the default: conditions (i) and (ii) of §4.3 are
        // reachability queries over the surviving subgraph, which only the
        // per-SCC elimination answers.  TCTL_LEGACY_LOOP selects the earlier
        // path-local loop test, kept for A/B comparison; it decides one
        // back-edge at a time and so rejects a node that sits on a Zeno loop
        // but reaches an accepting one by another route.
        scc_mode_ = std::getenv("TCTL_LEGACY_LOOP") == nullptr;
        words_ = (nc_ + 63) / 64;
    }

    // The only clock values where a formula's truth can flip are the integer
    // constants appearing in its intervals.  Region-splitting against just these
    // (not every integer up to M) keeps the search flat in the magnitude of M.
    void collect_boundaries(FormulaId id, FormulaFactory& f) {
        std::vector<std::int32_t> bs = {0};
        std::function<void(FormulaId)> walk = [&](FormulaId x) {
            if (x == kInvalidId) return;
            const FormulaNode& n = f.node(x);
            if (n.kind == NodeKind::TimedEU || n.kind == NodeKind::TimedAU ||
                n.kind == NodeKind::TimedER || n.kind == NodeKind::TimedAR) {
                bs.push_back(static_cast<std::int32_t>(n.time_lower.value));
                if (!n.time_upper.is_infinity)
                    bs.push_back(static_cast<std::int32_t>(n.time_upper.value));
            }
            walk(n.children[0]); walk(n.children[1]);
        };
        walk(id);
        std::sort(bs.begin(), bs.end());
        bs.erase(std::unique(bs.begin(), bs.end()), bs.end());
        bounds_ = std::move(bs);
    }

    // Per-clock truth-change points.  A formula-clock x_mu is only ever tested
    // against its *own* window I_mu — every guard the construction makes is
    // single-clock (paper §3) — so a guard on x_mu can only flip at an endpoint
    // of I_mu.  These are therefore the cell boundaries of the region walk in
    // (Delay), and splitting each clock against its own endpoints rather than
    // against every constant in the formula keeps the walk short.
    // inf I = 0 is a change point only when the endpoint is strict: x >= 0 holds
    // everywhere, whereas x > 0 separates the onset instant from the rest.
    void collect_clock_bounds(FormulaId root, FormulaFactory& f) {
        clock_bounds_.assign(nc_, {});
        std::function<void(FormulaId)> walk = [&](FormulaId x) {
            if (x == kInvalidId) return;
            const FormulaNode& n = f.node(x);
            if (is_timed(n.kind)) {
                const ClockId c = clock_of(cmap_, x);
                if (c != kNoClock && c < nc_) {
                    std::vector<std::int32_t>& bs = clock_bounds_[c];
                    const auto lo = static_cast<std::int32_t>(n.time_lower.value);
                    if (lo > 0 || n.time_lower.is_strict) bs.push_back(lo);
                    if (!n.time_upper.is_infinity)
                        bs.push_back(static_cast<std::int32_t>(n.time_upper.value));
                }
            }
            walk(n.children[0]); walk(n.children[1]);
        };
        walk(root);
        for (std::vector<std::int32_t>& bs : clock_bounds_) {
            std::sort(bs.begin(), bs.end());
            bs.erase(std::unique(bs.begin(), bs.end()), bs.end());
        }
    }

    /// Per-clock maximum lower- and upper-bound constants, for Extra_LU.
    ///
    /// A formula-clock @f$x_\mu@f$ is only ever tested against its own window
    /// @f$I_\mu@f$, so its maximum *lower*-bound constant is @f$\inf I_\mu@f$
    /// and its maximum *upper*-bound constant @f$\sup I_\mu@f$.  Extra_M has to
    /// use the larger of the two for both; separating them is what makes
    /// Extra_LU strictly coarser, and it is coarsest exactly where the window is
    /// wide.
    void collect_lu_bounds(FormulaId root, FormulaFactory& f) {
        lu_L_.assign(nc_, 0);
        lu_U_.assign(nc_, 0);
        std::function<void(FormulaId)> walk = [&](FormulaId x) {
            if (x == kInvalidId) return;
            const FormulaNode& n = f.node(x);
            if (is_timed(n.kind)) {
                const ClockId c = clock_of(cmap_, x);
                if (c != kNoClock && c < nc_) {
                    lu_L_[c] = std::max(lu_L_[c],
                                        static_cast<std::int32_t>(n.time_lower.value));
                    if (!n.time_upper.is_infinity)
                        lu_U_[c] = std::max(lu_U_[c],
                                            static_cast<std::int32_t>(n.time_upper.value));
                }
            }
            walk(n.children[0]); walk(n.children[1]);
        };
        walk(root);
        lu_L_[0] = lu_U_[0] = 0;                 // the reference clock
    }

    // Memoisation + boundary-region abstraction keep the search shallow.  The
    // process runs with an enlarged main-thread stack (set via a linker option,
    // see CMakeLists.txt) so deep-but-finite runs do not overflow — no per-check
    // thread and no artificial depth limit.
    bool decide(FormulaId root) {
        Node n;
        n.Gamma.insert(root);
        n.Z = Zone::zero(nc_);
        n.phase = Phase::Elapse;
        const bool r = scc_mode_ ? decide_scc(n) : decide_iter(n);
        if (verify_decode_) {
            std::fprintf(stderr, "decode round-trip: %llu ok, %llu mismatched\n",
                         (unsigned long long)decode_ok_,
                         (unsigned long long)decode_bad_);
        }
        return r;
    }

    std::uint64_t nodes() const { return expansions_; }
    bool budget_hit() const { return budget_hit_; }

    /// Witness automaton for the marking of the last successful decide().
    /// Only meaningful when SCC acceptance ran and the verdict was SAT.
    TimedAutomaton witness() { return extract_witness(root_id_); }
    bool can_extract() const { return scc_mode_ && root_id_ != kNoRegion; }

private:
    // ── Canonical node key ──────────────────────────────────────────────
    //
    // A key is built for every node the search touches, so building keys *is*
    // a large part of the search's cost.  Rendering one as text -- which is
    // what streaming the goal ids and the zone's pretty-printed constraints
    // into an ostringstream amounts to -- puts locale-aware integer formatting
    // and repeated string growth on the hot path, and that dominated the
    // profile.  The key is therefore a packed word vector: each section is
    // length-prefixed, so the encoding is unambiguous without separators and
    // reduces to a handful of appends.
    //
    // Everything about a node EXCEPT its zone forms the *structural* prefix.
    // Two nodes with the same structural prefix differ only in their zone, so
    // narrowing-monotonicity (paper §4.1) applies between them.
    using Key = std::vector<std::uint32_t>;

    struct KeyHash {
        std::size_t operator()(const Key& k) const noexcept {
            std::size_t h = 1469598103934665603ull;
            for (std::uint32_t w : k) {
                h ^= w;
                h *= 1099511628211ull;
            }
            return h;
        }
    };

    static void put(Key& k, std::uint32_t w) { k.push_back(w); }

    void append_struct_key(const Node& n, Key& k) const {
        // Interned sets contribute one word each rather than one per element.
        put(k, n.Gamma.handle());
        put(k, n.X.handle());
        put(k, n.witnessed.handle());

        // Pursuits and deadlines are sets, so the encoded tuples are sorted:
        // the key must not depend on the order the rules happened to append
        // them.  Fields go in as whole words rather than bit-packed --- x_mu is
        // kNoClock = 0xffffffff for an untimed modality, which no shift can
        // share a word with, and conflating two pursuits merges two nodes.
        pursuit_scratch_.clear();
        for (const Pursuit& p : n.pursuits)
            pursuit_scratch_.push_back({static_cast<std::uint32_t>(p.mu),
                                        static_cast<std::uint32_t>(p.x_mu),
                                        static_cast<std::uint32_t>(p.stage),
                                        static_cast<std::uint32_t>(p.part),
                                        static_cast<std::uint32_t>(p.is_until),
                                        static_cast<std::uint32_t>(p.persistent)});
        std::sort(pursuit_scratch_.begin(), pursuit_scratch_.end());
        put(k, static_cast<std::uint32_t>(pursuit_scratch_.size()));
        for (const auto& t : pursuit_scratch_)
            for (std::uint32_t w : t) put(k, w);

        deadline_scratch_.clear();
        for (const Deadline& d : n.D) {
            const auto b = static_cast<std::uint64_t>(d.bound);
            deadline_scratch_.push_back({static_cast<std::uint32_t>(d.x_mu),
                                         static_cast<std::uint32_t>(b >> 32),
                                         static_cast<std::uint32_t>(b),
                                         static_cast<std::uint32_t>(d.strict)});
        }
        std::sort(deadline_scratch_.begin(), deadline_scratch_.end());
        put(k, static_cast<std::uint32_t>(deadline_scratch_.size()));
        for (const auto& t : deadline_scratch_)
            for (std::uint32_t w : t) put(k, w);

        put(k, static_cast<std::uint32_t>(n.phase));
    }

    // The ~=_M-canonical zone's contribution to the key.
    //
    // Stored as HDBM's minimal graph rather than as the dense matrix: most
    // entries of a canonical DBM are implied by shortest paths through the
    // others, and a node key is retained for the whole search, so the dense
    // form is what the graph's resident size is mostly made of.  Packing is
    // deterministic and round-trips a canonical DBM exactly, so packed words
    // separate exactly the zones the matrix did -- the key stays faithful.
    // The engine still *operates* on dense zones; only the stored key is
    // minimal.
    void append_zone(const Zone& ez, Key& k) const {
        if (ez.is_empty()) { put(k, 0); return; }
        put(k, 1);
        const int dim = static_cast<int>(ez.num_clocks());
        pack_buf_.resize((ptctlmc::mindbm_bound(dim) + 3) / 4);
        pack_bits_.resize(ptctlmc::mindbm_bits2words(
            static_cast<std::uint32_t>(dim) * static_cast<std::uint32_t>(dim)));
        pack_first_.resize(static_cast<std::size_t>(dim));
        pack_next_.resize(static_cast<std::size_t>(dim));
        const std::size_t bytes =
            ptctlmc::mindbm_pack(ez.raw_data(), dim, pack_buf_.data(),
                                 pack_bits_.data(), pack_first_.data(),
                                 pack_next_.data());
        const std::size_t words = (bytes + 3) / 4;
        k.insert(k.end(), pack_buf_.begin(),
                 pack_buf_.begin() + static_cast<std::ptrdiff_t>(words));
    }


    // ── Witness extraction (paper Theorem 2) ────────────────────────────
    //
    // The marking computed by evaluate_scc is exactly the structure the
    // soundness proof reads an automaton off, so extraction is a pass over the
    // finished graph rather than a second search.  The nodes themselves were
    // released when they were expanded, but their keys were not: decode_key
    // reconstructs any node on demand.
    //
    // Locations are not single nodes.  Saturation, the cover rule, the pursuit
    // rules and (Delay) are all proof steps at *one* configuration --- (Delay)
    // in particular only advances the zone within a location --- so a location
    // is a maximal marked region that crosses no (EX) step.  Only (EX) moves
    // the model, and it fires exactly at a marked node that is saturated and
    // due a discrete step; those nodes are the region's exits, and each of
    // their marked children heads the next region.

    bool is_saturated(const Node& n) const {
        for (FormulaId id : n.Gamma.elements()) {
            const NodeKind k = f_.node(id).kind;
            if (k == NodeKind::And || k == NodeKind::Or) return false;
            if (is_modality(k)) return false;
        }
        for (const Pursuit& p : n.pursuits)
            if (p.stage == Pursuit::Stage::Here) return false;
        return true;
    }

    /// Children of @p v that the marking retains.
    std::vector<std::uint32_t> marked_children(std::uint32_t v) const {
        std::vector<std::uint32_t> out;
        if (g_[v].kind == Expansion::Kind::Or) {
            for (std::uint32_t c : g_[v].ch)
                if (g_[c].val) { out.push_back(c); break; }   // one suffices
        } else {
            for (std::uint32_t c : g_[v].ch)
                if (g_[c].val) out.push_back(c);
        }
        return out;
    }

    TimedAutomaton extract_witness(std::uint32_t root) {
        TimedAutomaton ta;
        ta.num_clocks = nc_;
        for (const auto& [mu, clk] : cmap_)
            if (clk != kNoClock && clk < nc_)
                ta.clock_names[clk] = "x_" + std::to_string(clk);

        // A location is the marked region opened by a head: the marked nodes
        // reachable from it without crossing an (EX) step.  Regions may
        // overlap, since memoisation lets one proof node serve several
        // contexts, and that is harmless -- a location is identified by its
        // head, not by the nodes it happens to share.
        std::map<std::uint32_t, std::uint32_t> region_of;      // head node -> location
        std::vector<std::uint32_t> heads;
        std::vector<std::vector<std::uint32_t>> members;
        std::vector<std::uint32_t> witness_node;   // the node a location is read off
        std::vector<std::pair<std::uint32_t, std::uint32_t>> edges;  // (loc, head)

        auto head_of = [&](std::uint32_t v) {
            auto it = region_of.find(v);
            if (it != region_of.end()) return it->second;
            const std::uint32_t r = static_cast<std::uint32_t>(heads.size());
            region_of.emplace(v, r);
            heads.push_back(v);
            members.emplace_back();
            witness_node.push_back(v);       // the head, until an exit is found
            return r;
        };

        const std::uint32_t r0 = head_of(root);
        for (std::uint32_t r = 0; r < heads.size(); ++r) {   // heads grows as we go
            std::vector<std::uint32_t> stack{heads[r]};
            std::set<std::uint32_t> seen;
            while (!stack.empty()) {
                const std::uint32_t v = stack.back();
                stack.pop_back();
                if (!seen.insert(v).second) continue;
                members[r].push_back(v);

                const Node n = decode_key(*key_of_[v]);
                if (is_saturated(n) && n.phase == Phase::Discrete) {
                    // (EX) fires here: every marked child opens a location.
                    if (witness_node[r] == heads[r]) witness_node[r] = v;
                    for (std::uint32_t c : marked_children(v))
                        edges.push_back({r, head_of(c)});
                    continue;                                // do not cross it
                }
                for (std::uint32_t c : marked_children(v)) stack.push_back(c);
            }
        }

        // ── locations ───────────────────────────────────────────────────
        for (std::uint32_t r = 0; r < heads.size(); ++r) {
            TALocation loc;
            loc.id = r;
            loc.is_initial = (r == r0);
            // A TA location carries one labelling, so it is read off a single
            // node -- the configuration at which the region takes its discrete
            // step.  The union over the region would merge the branches of a
            // (Cov) fork, each individually consistent but jointly not: one
            // branch may discharge a modality while the other pursues it into a
            // literal the first denies.
            {
                const std::uint32_t v = witness_node[r];
                const Node n = decode_key(*key_of_[v]);
                for (FormulaId id : n.Gamma.elements()) {
                    const FormulaNode& fn = f_.node(id);
                    if (fn.kind == NodeKind::Atom) loc.atoms.insert(fn.atom_name);
                    else if (fn.kind == NodeKind::Not &&
                             f_.node(fn.children[0]).kind == NodeKind::Atom)
                        loc.atoms.insert("!" + f_.node(fn.children[0]).atom_name);
                }
                // Inv(N): the deadline a universal until registered here bounds
                // how long the location may let time pass.
                for (const Deadline& d : n.D) {
                    if (d.x_mu == kNoClock || d.x_mu >= nc_) continue;
                    TAConstraint c;
                    c.clock_x = d.x_mu; c.clock_y = kReferenceClock;
                    c.bound = static_cast<std::int32_t>(d.bound);
                    c.is_strict = d.strict; c.is_upper = true;
                    loc.invariants.push_back(c);
                }
            }
            ta.locations[r] = std::move(loc);
        }
        ta.initial_location = r0;

        // ── transitions ─────────────────────────────────────────────────
        std::set<std::pair<std::uint32_t, std::uint32_t>> emitted;
        for (const auto& [from, to] : edges) {
            if (!emitted.insert({from, to}).second) continue;
            TATransition e;
            e.source = from;
            e.target = to;
            // (EX) does not advance time, so the step's zone is the target's;
            // the guard is that zone, read off as single-clock bounds.
            const Node tgt = decode_key(*key_of_[heads[to]]);
            for (ClockId c = 1; c < nc_; ++c) {
                const Bound ub = tgt.Z.get_bound(c, kReferenceClock);
                if (!ub.is_infinity()) {
                    TAConstraint g{c, kReferenceClock, ub.value, ub.is_strict, true};
                    e.guard.push_back(g);
                }
                const Bound lb = tgt.Z.get_bound(kReferenceClock, c);
                if (!lb.is_infinity() && lb.value != 0) {
                    TAConstraint g{c, kReferenceClock, -lb.value, lb.is_strict, false};
                    e.guard.push_back(g);
                }
            }
            // A launch resets its formula-clock, so the window is measured from
            // the configuration that demanded it.
            for (std::uint32_t v : members[to])
                for (ClockId c : decode_key(*key_of_[v]).just_reset)
                    if (c != kNoClock && c != kReferenceClock && c < nc_ &&
                        std::find(e.resets.begin(), e.resets.end(), c) == e.resets.end())
                        e.resets.push_back(c);
            ta.transitions.push_back(std::move(e));
        }
        return ta;
    }

    // ── Decoding a key back into its node ───────────────────────────────
    //
    // The search drops a node's payload as soon as it is expanded, keeping only
    // what acceptance needs.  Nothing is lost, though: the key is retained for
    // the whole run as the identity of the graph node, and it encodes every
    // component -- the three formula sets as interned handles, the pursuits and
    // deadlines as whole words, the phase, and the ~=_M-canonical zone as a
    // minimal graph.  Every section is length-prefixed or fixed-width, so the
    // encoding inverts, and the witness extractor can reconstruct any node it
    // needs instead of the engine holding them all.
    Node decode_key(const Key& k) const {
        Node n;
        std::size_t i = 0;
        n.Gamma     = FormulaSet::from_handle(k[i++]);
        n.X         = FormulaSet::from_handle(k[i++]);
        n.witnessed = FormulaSet::from_handle(k[i++]);

        const std::uint32_t np = k[i++];
        for (std::uint32_t t = 0; t < np; ++t) {
            Pursuit p;
            p.mu       = static_cast<FormulaId>(k[i++]);
            p.x_mu     = static_cast<ClockId>(k[i++]);
            p.stage    = static_cast<Pursuit::Stage>(k[i++]);
            p.part     = static_cast<Pursuit::Part>(k[i++]);
            p.is_until = k[i++] != 0;
            n.pursuits.push_back(p);
        }

        const std::uint32_t nd = k[i++];
        for (std::uint32_t t = 0; t < nd; ++t) {
            Deadline dl;
            dl.x_mu = static_cast<ClockId>(k[i++]);
            const std::uint64_t hi = k[i++], lo = k[i++];
            dl.bound  = static_cast<std::int64_t>((hi << 32) | lo);
            dl.strict = k[i++] != 0;
            n.D.push_back(dl);
        }

        n.phase = static_cast<Phase>(k[i++]);

        if (k[i++] == 0) {                       // the zone was empty
            n.Z = Zone::empty(nc_);
        } else {
            const void* packed = static_cast<const void*>(k.data() + i);
            std::vector<raw_t> dense(nc_ * nc_);
            ptctlmc::mindbm_unpack(packed, dense.data());
            n.Z = Zone::from_raw(nc_, dense.data());
            i += (ptctlmc::mindbm_size(packed) + 3) / 4;
        }

        // acc_key's tail: the clocks reset on the edge into this node, then the
        // until it discharges here.
        if (i < k.size()) {
            const std::uint32_t nr = k[i++];
            for (std::uint32_t t = 0; t < nr; ++t)
                n.just_reset.push_back(static_cast<ClockId>(k[i++]));
            n.discharges_until = static_cast<FormulaId>(k[i++]);
        }
        return n;
    }

    /// The zone that gives a node its identity.
    ///
    /// Extra_M by default.
    ///
    /// TCTL_EXTRA_LU selects Extra_LU instead, which is strictly coarser and
    /// does shrink the search sharply --- 77% fewer nodes at four clocks, the
    /// per-clock growth factor falling from ~35x to ~22x, enough to move the
    /// solvable frontier by one clock.  **It is nevertheless incomplete here,
    /// and must not be enabled by default.**
    ///
    /// Extra_LU is sound and complete for *reachability*: it never changes
    /// whether some run reaches a target.  The cover rule is not a reachability
    /// test.  It asks @f$Z \subseteq \Sat_X(\mu)@f$ --- a *universal* question
    /// over every valuation of the zone --- and an abstraction that enlarges Z
    /// can only make that inclusion fail.  (Cov) then degrades to (Cov*) or to
    /// a close, and witnesses are lost.  Measured: 7 of 938 satisfiable-by-
    /// construction formulas answered UNSATISFIABLE, and
    /// @f$\mathrm{EG}_{[1,5]}\mathrm{EF}_{[2,4]}\,p@f$ --- plainly satisfiable
    /// --- goes the same way.  No verdict went the other way, so the abstraction
    /// stays sound; it just stops being a decision procedure.
    ///
    /// The separate #exact_unbounded bits were needed for a different reason
    /// and remain correct: Extra_LU also erases the upper bounds acceptance
    /// condition (ii) reads, which would have admitted Zeno witnesses.
    Zone canon_zone(const Node& n) const {
        Zone z = n.Z;
        if (extra_lu_) z.extrapolate_lu(lu_L_, lu_U_);
        else           z.extrapolate(max_);
        return z;
    }

    /// Which clocks are genuinely unbounded, under the *exact* (Extra_M)
    /// abstraction.
    ///
    /// The Zeno test of condition (ii) asks whether a clock keeps a finite upper
    /// bound around a loop.  Extra_LU relaxes such bounds far more freely than
    /// Extra_M --- for a window @f$[1,5]@f$ it drops any bound above 1 --- so
    /// reading boundedness off an Extra_LU zone would call a loop capped at 3
    /// time-progressing and admit a Zeno witness.  These bits are therefore
    /// always computed from Extra_M, and they join the node key, so two nodes
    /// that a coarser zone would merge stay apart when they disagree on which
    /// clocks can still stop time.  That costs K bits, not K^2 bounds.
    void exact_unbounded(const Node& n, std::vector<char>& out) const {
        Zone z = n.Z;
        z.extrapolate(max_);
        out.assign(nc_, 0);
        for (ClockId c = 1; c < nc_; ++c)
            out[c] = z.get_bound(c, kReferenceClock).is_infinity() ? 1 : 0;
    }

    // ── Exact dead-clock elimination (TCTL_FREE_DEAD_CLOCKS) ────────────
    //
    // A formula-clock x_mu is *read* by exactly four things: the stop guard
    // Z ∩ (x_mu ∈ I) of a live pursuit of mu, the region split that guard is
    // taken in, the invariant Inv(N) of a deadline on x_mu, and the (Delay)
    // cell walk — which already restricts itself to the clocks of live pursuits
    // and deadlines.  Nothing else looks at it: S_X(nu) constrains only x_nu
    // (holds_region pins every *sub*-modality clock to its onset and projects
    // it out), and the cover rule *resets* x_mu before testing it, so whatever
    // value the clock carried into the rule is discarded.
    //
    // Hence once a pursuit of mu settles — the (U•) stop is taken, or a release
    // lapses past its window — x_mu is read by no rule until the next launch of
    // mu, and that launch resets it.  Its value between those two points is
    // unobservable, so projecting it out of the zone is an *exact* abstraction:
    // it identifies nodes that no continuation can tell apart.  This is the
    // standard active-clock reduction, and it is the same invariant
    // delay_successor() and loop condition (ii) already state in their comments
    // ("a clock with no live pursuit is never read, and is freshly reset if its
    // modality is launched again").
    //
    // Unlike the `witnessed` shortcut it discharges no obligation and drops no
    // child of (Cov): every re-demand still launches a fresh pursuit.  It only
    // stops the settled pursuit's leftover clock value from splitting nodes
    // that are otherwise identical — which is where the cost of relaunching
    // actually goes.
    void collapse_dead_clocks(Node& n) const {
        if (!free_dead_ || n.Z.is_empty()) return;
        live_scratch_.assign(nc_, 0);
        for (const Pursuit& p : n.pursuits)
            if (p.x_mu != kNoClock && p.x_mu < nc_) live_scratch_[p.x_mu] = 1;
        for (const Deadline& d : n.D)
            if (d.x_mu < nc_) live_scratch_[d.x_mu] = 1;
        for (ClockId c = 1; c < nc_; ++c)
            if (!live_scratch_[c]) n.Z.free(c);
    }

    // Full key, together with the canonical zone it was built over, so the
    // extrapolation is paid once per node rather than once per use.
    void build_key(const Node& n, Key& k, Zone& ez) const {
        k.clear();
        ez = canon_zone(n);
        append_struct_key(n, k);
        append_zone(ez, k);
        if (extra_lu_) {
            exact_unbounded(n, lu_bits_);
            std::uint32_t w = 0;
            for (ClockId c = 1; c < nc_; ++c)
                if (lu_bits_[c]) w |= (1u << (c & 31));
            put(k, w);                        // K bits, not K^2 bounds
        }
    }

    // ── Expansion (single rule) ─────────────────────────────────────────
    Expansion expand(const Node& n0) {
        // Children never inherit the transient discharge marker.
        Node n = n0;
        n.discharges_until = kInvalidId;
        if (node_closed(n.Gamma, f_) || n.Z.is_empty())
            return {Expansion::Kind::Closed, {}};

        // Saturation: (∧) then (∨).
        for (FormulaId id : n.Gamma.elements()) {
            const FormulaNode& fn = f_.node(id);
            if (fn.kind == NodeKind::And) {
                Node c = n;
                c.Gamma = gamma_without(n.Gamma, id);
                c.Gamma.insert(fn.children[0]);
                c.Gamma.insert(fn.children[1]);
                return {Expansion::Kind::And, {c}};
            }
        }
        for (FormulaId id : n.Gamma.elements()) {
            const FormulaNode& fn = f_.node(id);
            if (fn.kind == NodeKind::Or) {
                Node a = n, b = n;
                a.Gamma = gamma_without(n.Gamma, id); a.Gamma.insert(fn.children[0]);
                b.Gamma = gamma_without(n.Gamma, id); b.Gamma.insert(fn.children[1]);
                return {Expansion::Kind::Or, {a, b}};
            }
        }

        // Here-pursuit.
        for (std::size_t i = 0; i < n.pursuits.size(); ++i)
            if (n.pursuits[i].stage == Pursuit::Stage::Here)
                return unfold_pursuit(n, i);

        // Demanded modality in Gamma → cover.
        for (FormulaId id : n.Gamma.elements()) {
            if (is_modality(f_.node(id).kind)) {
                CoverResult cr = apply_cover(n, id, cmap_, nc_, max_, f_,
                                             sx_cache_, solo_launch_,
                                             reuse_witness_, window_reuse_);
                switch (cr.kind) {
                    case CoverResult::Kind::Close:
                        return {Expansion::Kind::Closed, {}};
                    case CoverResult::Kind::Cover:
                        return {Expansion::Kind::And, std::move(cr.children)};
                    case CoverResult::Kind::PartialCover:
                        return {Expansion::Kind::Or, std::move(cr.children)};
                }
            }
        }

        // Successor generation.
        return successors(n);
    }

    Expansion unfold_pursuit(const Node& n, std::size_t i) {
        const Pursuit p = n.pursuits[i];
        const FormulaNode& mn = f_.node(p.mu);
        const FormulaId phi = mn.children[0], psi = mn.children[1];
        const bool existential = !is_universal(mn.kind);
        const Window w = window_of(p.mu, f_);
        const auto defer = existential ? Pursuit::Stage::DeferEX
                                       : Pursuit::Stage::DeferAX;

        if (p.is_until) {
            // (U•): stop ⊕ go.  The stop zone Z ∩ (x_mu ∈ I) is split into
            // integer regions so the eventuality can be discharged in a
            // boundary-free cell (e.g. (1,2)) rather than a zone straddling a
            // hyperplane where a co-present formula flips.
            Expansion e; e.kind = Expansion::Kind::Or;
            Zone stopZ = n.Z;
            constrain_in_window(stopZ, p.x_mu, w);
            if (!stopZ.is_empty()) {
                for (const Zone& r : integer_regions(stopZ, p.x_mu)) {
                    Node stop = n;
                    stop.Gamma.insert(psi);
                    stop.Z = r;
                    if (p.persistent) {
                        // Persistent demand: the obligation recurs, so the
                        // pursuit is not retired.  Reset x_mu and keep the
                        // deadline, making it "time since the last witness"
                        // and capping the gap between consecutive witnesses at
                        // sup I (= sup I - inf I, as inf I = 0 here).  That cap
                        // is what the rate contradiction needs and what a
                        // single-onset clock cannot express.
                        stop.Z.reset(p.x_mu);
                        stop.just_reset.push_back(p.x_mu);
                        stop.pursuits[i].stage = Pursuit::Stage::Here;
                        stop.pursuits[i].part  = Pursuit::Part::Whole;
                    } else {
                        stop.pursuits.erase(stop.pursuits.begin() + static_cast<long>(i));
                        stop.D = drop_deadline(n.D, p.x_mu);
                    }
                    if (record_witness_) stop.witnessed.insert(p.mu);
                    stop.discharges_until = p.mu;
                    e.children.push_back(std::move(stop));
                }
            }
            Node go = n;
            go.Gamma.insert(phi);
            go.pursuits[i].stage = defer;
            e.children.push_back(std::move(go));
            return e;
        }

        // Release.
        if (p.part == Pursuit::Part::Whole) {
            // Untimed release (window [0,∞), no clock): the "before"/"after"
            // partitions are empty, so pursue only the in-window part on Z.
            if (p.x_mu == kNoClock) {
                Node in = n;
                in.pursuits[i].part = Pursuit::Part::InI;
                in.pursuits[i].stage = Pursuit::Stage::Here;
                return {Expansion::Kind::And, {in}};
            }
            // (R^split): partition Z by x_mu vs I; pursue before/in, lapse after.
            Expansion e; e.kind = Expansion::Kind::And;
            // before: x_mu ≤ lo (strict iff lo ∈ I)
            {   Node before = n; before.Z.add_upper_bound(p.x_mu, w.lo, !w.lo_strict);
                if (!before.Z.is_empty()) {
                    before.pursuits[i].part = Pursuit::Part::BeforeI;
                    before.pursuits[i].stage = Pursuit::Stage::Here;
                    e.children.push_back(before);
                }
            }
            // in: x_mu ∈ I
            {   Node in = n; constrain_in_window(in.Z, p.x_mu, w);
                if (!in.Z.is_empty()) {
                    in.pursuits[i].part = Pursuit::Part::InI;
                    in.pursuits[i].stage = Pursuit::Stage::Here;
                    e.children.push_back(in);
                }
            }
            // after: x_mu ≥ hi (strict iff hi ∈ I) → lapsed, drop pursuit
            if (!w.hi_inf) {
                Node after = n; after.Z.add_lower_bound(p.x_mu, w.hi, !w.hi_strict);
                if (!after.Z.is_empty()) {
                    if (record_witness_) after.witnessed.insert(p.mu);
                    after.pursuits.erase(after.pursuits.begin() + static_cast<long>(i));
                    e.children.push_back(after);
                }
            }
            if (e.children.empty()) return {Expansion::Kind::Closed, {}};
            return e;
        }

        if (p.part == Pursuit::Part::BeforeI) {
            // (R•_{≺I}): stop {φ} ⊕ go
            Node stop = n; stop.Gamma.insert(phi);
            stop.pursuits.erase(stop.pursuits.begin() + static_cast<long>(i));
            Node go = n; go.pursuits[i].stage = defer;
            return {Expansion::Kind::Or, {stop, go}};
        }
        // (R•_{∈I}): stop {φ,ψ} ⊕ go {ψ}
        Node stop = n; stop.Gamma.insert(phi); stop.Gamma.insert(psi);
        stop.pursuits.erase(stop.pursuits.begin() + static_cast<long>(i));
        Node go = n; go.Gamma.insert(psi); go.pursuits[i].stage = defer;
        return {Expansion::Kind::Or, {stop, go}};
    }

    // Integer-region split of a zone along ONE clock `c` (paper's Δ°/Δ^∂): the
    // sub-zones are the integer points c=k and open cells c∈(k,k+1) up to M, plus
    // c>M.  Splitting only the clock whose window boundary matters (not every
    // clock) avoids a Cartesian blow-up while still separating a boundary point
    // from the open interval where a co-present formula's truth flips.
    std::vector<Zone> integer_regions(const Zone& z, ClockId c) const {
        if (c == kNoClock) return {z};     // untimed: no boundary to split at
        std::vector<Zone> regs;
        for (std::size_t i = 0; i < bounds_.size(); ++i) {
            const std::int32_t b = bounds_[i];
            Zone pt = z;                       // c = b
            pt.add_lower_bound(c, b, false); pt.add_upper_bound(c, b, false);
            if (!pt.is_empty()) regs.push_back(std::move(pt));
            if (i + 1 < bounds_.size()) {      // c ∈ (b, next)
                Zone op = z;
                op.add_lower_bound(c, b, true);
                op.add_upper_bound(c, bounds_[i + 1], true);
                if (!op.is_empty()) regs.push_back(std::move(op));
            }
        }
        Zone hi = z;                           // c > last boundary
        hi.add_lower_bound(c, bounds_.back(), true);
        if (!hi.is_empty()) regs.push_back(std::move(hi));
        return regs;
    }

    // Lower endpoint of clock c in z:  c >= lv,  strict iff `lstrict`.
    void clk_lower(const Zone& z, ClockId c, std::int32_t& lv, bool& lstrict) const {
        const Bound lb = z.get_bound(kReferenceClock, c);   // 0 - c <= lb ⇒ c >= -lb
        if (lb.is_infinity()) { lv = 0; lstrict = false; return; }
        lv = -lb.value; lstrict = lb.is_strict;
    }
    // Does z pin c exactly on one of c's own truth-change points?
    bool at_own_bound(const Zone& z, ClockId c, std::int32_t lv, bool lstrict) const {
        if (lstrict) return false;
        const Bound ub = z.get_bound(c, kReferenceClock);   // c - 0 <= ub
        if (ub.is_infinity() || ub.is_strict || ub.value != lv) return false;
        const std::vector<std::int32_t>& bs = clock_bounds_[c];
        return std::find(bs.begin(), bs.end(), lv) != bs.end();
    }
    // c's next own change point strictly above lv, if any.
    bool next_own_bound(ClockId c, std::int32_t lv, std::int32_t& nb) const {
        for (std::int32_t b : clock_bounds_[c]) if (b > lv) { nb = b; return true; }
        return false;
    }

    // (Delay), §4.2.  Time advances one truth region at a time: first Δ°, the
    // time-successor strictly below the next integer hyperplane, then Δ^∂, that
    // hyperplane itself.  By Lemma 3 the truth of every subformula is constant
    // along an open segment that crosses no hyperplane, so a node whose zone
    // lies in one region answers each guard once and unambiguously — which is
    // what keeps [1,2) distinguishable from [1,2].
    //
    // The two steps are sequential: Δ^∂ is the delay successor *of the node Δ°
    // produced*, not a sibling of it.  They are consecutive segments of a single
    // run rather than independent conjuncts, and conjoining them would demand
    // that one run meet its obligations twice over.  An eventuality stopped in
    // the open segment would still be pending in a sibling boundary node, so
    // E(p U(1,5) q) would be rejected on the ground that x = 5 cannot meet a
    // window that has just closed at 5.
    //
    // Region-uniformity is also what keeps (Rsplit) well behaved.  With every
    // node's zone inside a single cell of each active clock, the partition of a
    // release into before/in/after has exactly one non-empty part, so a pursuit
    // travelling alongside it is never split across the parts and never has to
    // discharge separately in a segment where the release forbids its target.
    Expansion delay_successor(const Node& n) {
        Zone Zup = n.Z;
        Zup.up();
        apply_inv(Zup, n.D);
        if (Zup.is_empty()) return {Expansion::Kind::Closed, {}};

        // Only clocks a guard can still be tested against need cell-uniformity:
        // those of the active pursuits and of the deadlines in Inv(N).  A clock
        // with no live pursuit is never read, and is freshly reset if its
        // modality is launched again, so splitting on it would only add nodes.
        struct Act { ClockId c; std::int32_t lv; bool at_pt; bool has_nb; std::int32_t nb; };
        std::vector<Act> act;
        std::vector<char> seen(nc_, 0);
        auto note = [&](ClockId c) {
            if (c == kNoClock || c >= nc_ || seen[c]) return;
            seen[c] = 1;
            Act a; a.c = c; a.nb = 0;
            bool lstrict = false;
            clk_lower(n.Z, c, a.lv, lstrict);
            a.at_pt  = at_own_bound(n.Z, c, a.lv, lstrict);
            a.has_nb = next_own_bound(c, a.lv, a.nb);
            act.push_back(a);
        };
        for (const Pursuit& p : n.pursuits) note(p.x_mu);
        for (const Deadline& d : n.D)       note(d.x_mu);

        auto mk = [&](Zone z) {
            z.extrapolate(max_);
            Node d = n;
            d.Z = std::move(z);
            d.phase = Phase::Discrete;
            d.just_reset.clear();
            return d;
        };

        bool any_nb = false;
        for (const Act& a : act) if (a.has_nb) any_nb = true;

        // Δ°: every active clock strictly below its next change point, and every
        // clock sitting exactly on one pushed strictly off it.  Both constraints
        // are single-clock, so no diagonal enters the construction.  The push-off
        // matters even when no change point remains ahead: a clock resting on its
        // *last* bound still has the point and the open cell above it as two
        // distinct regions, and a zone spanning both would put (R^split) back to
        // splitting one run's future into AND-siblings.
        Zone open = Zup;
        for (const Act& a : act) {
            if (a.has_nb) open.add_upper_bound(a.c, a.nb, true);
            if (a.at_pt)  open.add_lower_bound(a.c, a.lv, true);
        }
        Zone cur = n.Z; cur.extrapolate(max_);
        if (!open.is_empty()) {
            Node d = mk(open);
            if (!(d.Z == cur)) return {Expansion::Kind::And, {d}};
            // Δ° = Z: already inside the open cell, so the next step is Δ^∂.
        }

        if (!any_nb) {
            // Past the last change point of every active clock, so no hyperplane
            // remains: (Delay) degenerates to ↑Z, a self-loop that keeps time
            // running.  It is not Zeno — every active clock is now extrapolated
            // above its maximum, hence unbounded (Lemma 4).
            if (open.is_empty()) return {Expansion::Kind::Closed, {}};
            Node d = mk(std::move(open));
            return {Expansion::Kind::And, {d}};
        }

        // Δ^∂: the run reaches the next hyperplane.  Which clocks land on a
        // change point together depends on the valuation, so this is an
        // OR-narrowing — sound by monotonicity of realisability under narrowing
        // (§4.1), the same justification (Cov*) narrows on, and complete because
        // every valuation is covered by one of the combinations.
        Zone capped = Zup;
        for (const Act& a : act) {
            if (a.has_nb) capped.add_upper_bound(a.c, a.nb, false);
            if (a.at_pt)  capped.add_lower_bound(a.c, a.lv, true);
        }
        std::vector<Act> cand;
        for (const Act& a : act) if (a.has_nb) cand.push_back(a);

        Expansion e; e.kind = Expansion::Kind::Or;
        std::function<void(std::size_t, Zone, bool)> rec =
            [&](std::size_t i, Zone z, bool any_at) {
                if (z.is_empty()) return;                      // prune early
                if (i == cand.size()) {
                    if (!any_at) return;                       // that is Δ°
                    Node d = mk(std::move(z));
                    if (!d.Z.is_empty()) e.children.push_back(std::move(d));
                    return;
                }
                const Act& a = cand[i];
                Zone at = z;                                   // c on its bound
                at.add_lower_bound(a.c, a.nb, false);
                at.add_upper_bound(a.c, a.nb, false);
                rec(i + 1, std::move(at), true);
                Zone below = std::move(z);                     // c still below it
                below.add_upper_bound(a.c, a.nb, true);
                rec(i + 1, std::move(below), any_at);
            };
        rec(0, std::move(capped), false);

        if (e.children.empty()) return {Expansion::Kind::Closed, {}};
        return e;
    }

    Expansion successors(const Node& n) {
        if (n.phase == Phase::Elapse) return delay_successor(n);
        // (EX): one child per DeferEX pursuit; DeferAX carried to all; stutter.
        PooledVec<Pursuit> ex, ax;
        for (const Pursuit& p : n.pursuits) {
            if (p.stage == Pursuit::Stage::DeferEX) ex.push_back(p);
            else if (p.stage == Pursuit::Stage::DeferAX) ax.push_back(p);
        }
        // Reviving a deferred pursuit: time has advanced (a delay just ran), so a
        // release must re-partition its window against the new zone — reset its
        // part to Whole so (R^split) re-runs (else it stays "in-window" and keeps
        // imposing ψ after x_mu has lapsed past I).
        auto revive = [](Pursuit q) {
            q.stage = Pursuit::Stage::Here;
            q.part = Pursuit::Part::Whole;
            return q;
        };
        auto make_child = [&](const Pursuit* ex_one) {
            Node c;
            c.X = n.X;
            c.Gamma = n.X;             // {ψ} ∪ X base
            c.Z = n.Z; c.O = n.O; c.D = n.D; c.phase = Phase::Elapse;
            c.witnessed = n.witnessed;
            if (ex_one) c.pursuits.push_back(revive(*ex_one));
            for (const Pursuit& q : ax) c.pursuits.push_back(revive(q));
            return c;
        };
        Expansion e; e.kind = Expansion::Kind::And;
        if (ex.empty()) {
            e.children.push_back(make_child(nullptr));       // stutter
        } else {
            for (const Pursuit& p : ex) e.children.push_back(make_child(&p));
        }
        return e;
    }

    static constexpr std::size_t kInf = static_cast<std::size_t>(-1);

    // ── Explicit-stack frame (no call recursion → no stack overflow) ────
    struct Frame {
        Node        n;
        Key         k;         // full key (struct + canonical zone)
        Expansion   e;
        std::size_t ci = 0;
        std::size_t depth = 0;
        std::size_t submin = kInf;
        bool        res = false;
        bool        expanded = false;
    };

    // ── Loop acceptance (§4.3) ──────────────────────────────────────────
    // A candidate loop N_i … N_j (equal componentwise, zones modulo ~=_M) is
    // accepting iff
    //   (i)  every until pursuit active at N_i is discharged on the segment —
    //        the (stop) branch of (U•) is taken for it at some N_k whose zone
    //        meets the window — which enforces the least-fixpoint reading of
    //        until; and
    //   (ii) the loop is time-progressing: it elapses positive time, and every
    //        clock is either reset on the segment or extrapolated above its
    //        maximum constant, hence unbounded.  This excludes Zeno cycles, a
    //        loop pinned to x < 1 on a never-reset clock elapsing only finite
    //        total time (Lemma 4).
    bool loop_accepting(const std::vector<Frame>& st, std::size_t a) const {
        const Node& rep = st[a].n;

        // ── (i) every active until discharged on the segment ──
        // A (U•) stop child records the until it settles, and the rule emits one
        // only on a zone that meets the window, so the marker witnesses exactly
        // the paper's  Z_k ∩ (x_mu ∈ I) ≠ ∅.
        for (const Pursuit& p : rep.pursuits) {
            if (!p.is_until) continue;
            bool discharged = false;
            for (std::size_t k = a; k < st.size() && !discharged; ++k)
                if (st[k].n.discharges_until == p.mu) discharged = true;
            if (discharged) continue;
            // (EX) hands each deferred pursuit to *one* successor, so an until can
            // legitimately leave this path: the obligation then rides a sibling
            // AND-branch, which the marking requires to succeed on its own.  Only
            // a pursuit present at every node of the segment is genuinely stuck.
            bool present_all = true;
            for (std::size_t k = a; k < st.size() && present_all; ++k) {
                bool has = false;
                for (const Pursuit& q : st[k].n.pursuits)
                    if (q.mu == p.mu) { has = true; break; }
                present_all = has;
            }
            if (present_all) return false;          // stuck eventuality
        }

        // ── (ii) time-progressing ──
        bool has_delay = false;
        std::vector<char> reset(nc_, 0);
        for (std::size_t k = a; k < st.size(); ++k) {
            if (st[k].n.phase == Phase::Discrete) has_delay = true;
            for (ClockId c : st[k].n.just_reset) if (c < nc_) reset[c] = 1;
        }
        if (!has_delay) return false;

        // Every clock, not just those a guard reads: the argument of Lemma 4 is
        // that a clock retaining a finite bound x <= c in the loop's zones and
        // never reset caps the total elapse at c - nu(x), so infinitely many
        // iterations converge.  That holds however the bound got there.  A clock
        // past its maximum constant has been extrapolated to no upper bound at
        // all, which is exactly the "extrapolated above M" escape.
        // The escape clause is read over the clocks that can actually cap the
        // elapse: those of the pursuits still live here and those carrying a
        // deadline in Inv(N).  A clock whose pursuit has settled is read by no
        // rule and constrains no guard, so a finite bound left on it cannot
        // converge the loop's total delay — Lemma 4's argument needs the bound
        // to be *enforced* at every node, which only a live clock's is.
        std::vector<char> capping(nc_, 0);
        for (const Pursuit& p : rep.pursuits)
            if (p.x_mu != kNoClock && p.x_mu < nc_) capping[p.x_mu] = 1;
        for (const Deadline& d : rep.D)
            if (d.x_mu < nc_) capping[d.x_mu] = 1;

        for (ClockId c = 1; c < nc_; ++c) {
            if (!capping[c] || reset[c]) continue;                             // dead, or reset
            if (rep.Z.get_bound(c, kReferenceClock).is_infinity()) continue;   // above its max
            return false;                                                     // bounded, unreset
        }
        return true;
    }

    // ── Memo over ~=_M-identical nodes (paper Thm 1) ────────────────────
    // Keyed by struct key, matched on the ~=_M-canonical zone.  Only
    // self-contained (path-independent) verdicts are cached.
    //
    // The match must be EXACT.  It is tempting to subsume by narrowing-
    // monotonicity (§4.1: realisable at Z ⇒ realisable at every ∅≠Z'⊆Z), but
    // that lemma is about realisability, which quantifies over *every* ν ∈ Z,
    // whereas a verdict this search returns does not: (Cov*) — and the Δ^∂ step
    // of (Delay) — are ⊕-narrowings, so a SAT verdict at Z certifies only *some*
    // subzone of Z.  Propagating it down to an arbitrary Z' ⊆ Z then certifies a
    // zone disjoint from the witness: it is what made Fig. 1a come out SAT, the
    // origin inheriting a verdict whose witness lived in the lapsed tail x₁ > 3.
    // The node bound of Lemma 1 counts ~=_M-distinct nodes, so exact matching is
    // also what Theorem 1's "each node is expanded at most once" assumes.
    bool memo_lookup(const Key& k, bool& out) const {
        auto it = memo_.find(k);
        if (it == memo_.end()) return false;
        out = it->second;
        return true;
    }
    void memo_store(const Key& k, bool verdict) { memo_.emplace(k, verdict); }

    void dtrace(std::size_t depth, const char* tag, const Node& n, int res) const {
        if (!debug_) return;
        std::ostringstream os;
        for (std::size_t i = 0; i < depth; ++i) os << ' ';
        os << tag;
        if (res >= 0) os << (res ? "+" : "-");
        os << " G{";
        for (FormulaId id : n.Gamma.elements()) os << f_.to_string(id) << ',';
        os << "} P{";
        for (const Pursuit& p : n.pursuits)
            os << f_.to_string(p.mu) << "/s" << int(p.stage) << "/pt" << int(p.part)
               << (p.is_until ? "U" : "R") << ' ';
        os << "} ph" << int(n.phase) << " Z=" << n.Z.to_string() << '\n';
        std::fputs(os.str().c_str(), stderr);
    }

    void push_frame(std::vector<Frame>& st, const Node& n) {
        Frame fr;
        fr.n = n;
        collapse_dead_clocks(fr.n);
        Zone ez;
        build_key(fr.n, fr.k, ez);
        st.push_back(std::move(fr));
    }

    // ════════════════════════════════════════════════════════════════════
    //  SCC acceptance (§4.3 read through §5.1)
    // ════════════════════════════════════════════════════════════════════
    //
    // §5.1 states conditions (i) and (ii) of §4.3 as *reachability queries over
    // the surviving subgraph*:
    //
    //   "...every node from which no surviving path reaches a time-progressing
    //    loop, and every node from which no surviving path takes the (stop)
    //    branch of an until pursuit active there.  The first three tests are
    //    local; the last two are reachability queries over the surviving
    //    subgraph ...  The two queries enforce conditions (ii) and (i) of §4.3
    //    respectively."
    //
    // A node therefore dies only when it can reach *no* accepting loop — never
    // because one particular back-edge happens to close a bad one.  That is the
    // whole difference from loop_accepting(), which returns a verdict on the
    // path segment and hands it back as the branch's value.  On
    // EG[1,5](EF[2,4] p) the launch child closes a Zeno loop (x1 is bounded by 5
    // and never reset) and is rejected *as a loop* — yet it also reaches the
    // accepting tail its AND-sibling exhibits, so the paper keeps it.  Nothing
    // path-local can see that: the information is simply not available at the
    // back-edge.
    //
    // The graph is built lazily, only the part the search demands, exactly as
    // the paper's memoised AND–OR graph is; Tarjan runs alongside the DFS and
    // each SCC is eliminated the moment it closes, when every child outside it
    // already carries a final value.

    // ── Acceptance-relevant node identity ───────────────────────────────
    // key() deliberately omits the two markers the loop test reads, because the
    // legacy search reads them off the frame it is standing on.  A graph keyed
    // by identity cannot: two nodes agreeing on everything else but reached one
    // *with* a launch reset and one without, or one *as* a (U•) stop and one by
    // another route, would be merged, and the merged node would report a reset
    // or a discharge that the actual cycle never performs.  That is unsound in
    // the generous direction, so the markers join the key here.  They cost
    // little: a node's children carry the same markers whatever the parent's
    // were, so the split closes again one step down.
    void acc_key(const Node& n, Key& k, Zone& ez) const {
        build_key(n, k, ez);
        scratch32_.assign(n.just_reset.begin(), n.just_reset.end());
        std::sort(scratch32_.begin(), scratch32_.end());
        scratch32_.erase(std::unique(scratch32_.begin(), scratch32_.end()),
                         scratch32_.end());
        put(k, static_cast<std::uint32_t>(scratch32_.size()));
        for (std::uint32_t c : scratch32_) put(k, c);
        put(k, static_cast<std::uint32_t>(n.discharges_until));
    }

    // ── A node of the explored AND–OR graph ─────────────────────────────
    struct GNode {
        /// The node's formulas and zone, held only until it is expanded.
        ///
        /// Behind a pointer rather than by value: a graph node lives for the
        /// whole search but its payload is wanted for one expansion, and an
        /// emptied Node still occupies four vector headers plus a zone --- some
        /// two hundred bytes of shells whose contents are already gone.  A null
        /// pointer costs eight.
        std::unique_ptr<Node>      n;
        Expansion::Kind            kind = Expansion::Kind::Closed;
        std::vector<std::uint32_t> ch;

        bool                   delayed    = false;      ///< reached by (Delay)
        FormulaId              discharges = kInvalidId; ///< (U•) stop taken here
        std::vector<FormulaId> untils;                  ///< active until pursuits

        std::uint32_t index = 0, low = 0;   ///< Tarjan
        bool visited = false, onstack = false;
        bool done = false, val = false;     ///< final once its SCC is evaluated
    };

    // Per-node clock sets live in flat bitmap arrays rather than in the node, so
    // that a graph of millions of nodes costs no per-node allocation.
    std::uint64_t* cap_of(std::uint32_t v) { return cap_.data() + std::size_t(v) * words_; }
    std::uint64_t* res_of(std::uint32_t v) { return res_.data() + std::size_t(v) * words_; }
    std::uint64_t* unb_of(std::uint32_t v) { return unb_.data() + std::size_t(v) * words_; }
    static void set_bit(std::uint64_t* m, std::size_t i) { m[i >> 6] |= 1ULL << (i & 63); }

    /// Drop what a retired node no longer needs.
    ///
    /// Only the children list: a component reads the children of its own
    /// members and never those of a node that has already retired, so once a
    /// verdict is final the list is dead weight.
    ///
    /// The until set stays.  Condition \ref M2 asks whether a surviving exit
    /// *outside* the component still carries the pursuit --- @c pursues(c,mu)
    /// on an out-of-component child --- and that child is by definition already
    /// retired, so freeing its untils would silently change the verdict.
    ///
    /// Nothing is freed when a witness is wanted, since extraction walks the
    /// retained children.
    void release_search_state(std::uint32_t v) {
        if (keep_graph_) return;
        std::vector<std::uint32_t>().swap(g_[v].ch);
    }

    // Intern a node: return its id, creating it (and its metadata) on first sight.
    std::uint32_t intern(Node&& n) {
        Key k;
        Zone ez;
        collapse_dead_clocks(n);
        acc_key(n, k, ez);
        // Self-check for the witness extractor: decoding a key and re-encoding
        // it must reproduce the key exactly, or a reconstructed node would not
        // be the node the search saw.
        if (verify_decode_) {
            Node back = decode_key(k);
            Key again; Zone tmp;
            acc_key(back, again, tmp);
            if (again != k) {
                std::fputs("decode_key round-trip MISMATCH\n", stderr);
                ++decode_bad_;
            } else {
                ++decode_ok_;
            }
        }
        if (auto it = gid_.find(k); it != gid_.end()) return it->second;

        const auto id = static_cast<std::uint32_t>(g_.size());
        // Elements of an unordered_map are reference-stable, so the graph can
        // index the keys by node id at eight bytes each rather than copying.
        const auto ins = gid_.emplace(std::move(k), id);
        key_of_.push_back(&ins.first->first);
        g_.emplace_back();
        cap_.resize(cap_.size() + words_, 0);
        res_.resize(res_.size() + words_, 0);
        unb_.resize(unb_.size() + words_, 0);

        GNode& gn = g_.back();
        gn.n          = std::make_unique<Node>(std::move(n));
        gn.delayed    = (gn.n->phase == Phase::Discrete);
        gn.discharges = gn.n->discharges_until;
        for (const Pursuit& p : gn.n->pursuits)
            if (p.is_until) gn.untils.push_back(p.mu);

        // The clocks that can cap the elapse are exactly those (Delay) reads:
        // of a live pursuit, or of a deadline in Inv(N).  A clock whose pursuit
        // has settled is read by no rule and bounds no guard, so a finite bound
        // left on it cannot converge the loop's total delay.
        std::uint64_t* cap = cap_of(id);
        for (const Pursuit& p : g_[id].n->pursuits)
            if (p.x_mu != kNoClock && p.x_mu < nc_) set_bit(cap, p.x_mu);
        for (const Deadline& d : g_[id].n->D)
            if (d.x_mu < nc_) set_bit(cap, d.x_mu);

        std::uint64_t* res = res_of(id);
        for (ClockId c : g_[id].n->just_reset)
            if (c < nc_) set_bit(res, c);

        // Boundedness is always the exact (Extra_M) one: reading it off an
        // Extra_LU zone would erase the caps condition (ii) relies on.
        std::uint64_t* unb = unb_of(id);
        if (extra_lu_) {
            exact_unbounded(*g_[id].n, lu_bits_);
            for (ClockId c = 1; c < nc_; ++c)
                if (lu_bits_[c]) set_bit(unb, c);
        } else {
            for (ClockId c = 1; c < nc_; ++c)
                if (ez.get_bound(c, kReferenceClock).is_infinity()) set_bit(unb, c);
        }

        return id;
    }

    // Expand a node in place, interning its children.  Returns false only when
    // the time budget ran out.
    bool expand_node(std::uint32_t v) {
        if ((++expansions_ & 0x1FFF) == 0 && has_deadline_ &&
            std::chrono::steady_clock::now() > deadline_) {
            budget_hit_ = true;
            return false;
        }
        Node n = std::move(*g_[v].n);
        g_[v].n.reset();                        // release: only metadata is kept
        if (node_closed(n.Gamma, f_) || n.Z.is_empty()) {
            dtrace(0, "CLOSED", n, -1);
            g_[v].kind = Expansion::Kind::Closed;
            return true;
        }
        Expansion e = expand(n);
        dtrace(0, e.kind == Expansion::Kind::And ? "AND" : "OR", n, -1);
        // intern() may reallocate g_, so collect the ids before touching g_[v].
        std::vector<std::uint32_t> kids;
        kids.reserve(e.children.size());
        for (Node& c : e.children) kids.push_back(intern(std::move(c)));
        g_[v].kind = e.kind;
        g_[v].ch   = std::move(kids);
        return true;
    }

    // ── Elimination inside one closed SCC (§5.1) ────────────────────────
    // Every child outside S already has its final value: SCCs close in reverse
    // topological order.  So the marking restricted to S is the greatest set of
    // its nodes closed under the three local tests and the two reachability
    // queries — computed the way §5.1 computes it, by deletion.
    void evaluate_scc(const std::vector<std::uint32_t>& S) {
        const std::size_t m = S.size();
        if (debug_) {
            std::ostringstream os;
            os << "SCC size=" << m << " {";
            for (std::uint32_t v : S) os << v << ' ';
            os << "}\n";
            std::fputs(os.str().c_str(), stderr);
        }
        std::unordered_map<std::uint32_t, std::size_t> pos;
        pos.reserve(m * 2);
        for (std::size_t i = 0; i < m; ++i) pos.emplace(S[i], i);
        std::vector<char> alive(m, 1);

        auto inside = [&](std::uint32_t c, std::size_t& i) {
            auto it = pos.find(c);
            if (it == pos.end()) return false;
            i = it->second;
            return true;
        };
        auto child_alive = [&](std::uint32_t c) {
            std::size_t i = 0;
            if (inside(c, i)) return alive[i] != 0;
            return g_[c].done && g_[c].val;
        };

        for (;;) {
            // ── the three local tests: closed, OR with all children gone,
            //    AND with a dead child ──
            for (bool changed = true; changed;) {
                changed = false;
                for (std::size_t i = 0; i < m; ++i) {
                    if (!alive[i]) continue;
                    const GNode& v = g_[S[i]];
                    bool ok;
                    if (v.kind == Expansion::Kind::Closed) {
                        ok = false;
                    } else if (v.kind == Expansion::Kind::And) {
                        ok = true;
                        for (std::uint32_t c : v.ch)
                            if (!child_alive(c)) { ok = false; break; }
                    } else {
                        ok = false;
                        for (std::uint32_t c : v.ch)
                            if (child_alive(c)) { ok = true; break; }
                    }
                    if (!ok) { alive[i] = 0; changed = true; }
                }
            }
            // ── the two reachability queries ──
            bool removed = query_progress(S, pos, alive);
            if (query_until(S, pos, alive)) removed = true;
            if (!removed) break;   // deleting nodes can invalidate either test
        }

        for (std::size_t i = 0; i < m; ++i) {
            g_[S[i]].done = true;
            g_[S[i]].val  = alive[i] != 0;
        }
    }

    // Reverse adjacency among the surviving nodes of S, by position.
    std::vector<std::vector<std::size_t>> reverse_edges(
            const std::vector<std::uint32_t>& S,
            const std::unordered_map<std::uint32_t, std::size_t>& pos,
            const std::vector<char>& alive) const {
        std::vector<std::vector<std::size_t>> rev(S.size());
        for (std::size_t i = 0; i < S.size(); ++i) {
            if (!alive[i]) continue;
            for (std::uint32_t c : g_[S[i]].ch) {
                auto it = pos.find(c);
                if (it == pos.end() || !alive[it->second]) continue;
                rev[it->second].push_back(i);
            }
        }
        return rev;
    }

    // Is the sub-component T time-progressing?  §4.3 (ii): it elapses positive
    // time, and every capping clock is either reset on it or extrapolated above
    // its maximum constant, hence unbounded.  A clock that keeps a finite bound
    // x <= c anywhere on the cycle and is never reset caps the total elapse at
    // c - nu(x), so infinitely many iterations converge (Lemma 4) — which is why
    // "unbounded" is read over *every* node of T, and "reset" over any.
    bool progressing(const std::vector<std::uint32_t>& S,
                     const std::vector<std::size_t>& T) {
        bool has_delay = false;
        std::vector<std::uint64_t> cap(words_, 0), res(words_, 0), unb(words_, ~0ULL);
        for (std::size_t i : T) {
            const std::uint32_t id = S[i];
            if (g_[id].delayed) has_delay = true;
            for (std::size_t w = 0; w < words_; ++w) {
                cap[w] |= cap_of(id)[w];
                res[w] |= res_of(id)[w];
                unb[w] &= unb_of(id)[w];
            }
        }
        if (!has_delay) return false;
        for (std::size_t w = 0; w < words_; ++w)
            if (cap[w] & ~res[w] & ~unb[w]) return false;
        return true;
    }

    // §5.1, condition (ii): delete every node from which no surviving path
    // reaches a time-progressing loop.  Two kinds of node reach one directly:
    // those on a time-progressing cycle inside the surviving part of S, and
    // those with a surviving child *outside* S — such a child is already marked,
    // so it reaches one itself.  Everything that reaches neither dies.
    bool query_progress(const std::vector<std::uint32_t>& S,
                        const std::unordered_map<std::uint32_t, std::size_t>& pos,
                        std::vector<char>& alive) {
        const std::size_t m = S.size();
        std::vector<char> reaches(m, 0);

        for (std::size_t i = 0; i < m; ++i) {
            if (!alive[i]) continue;
            for (std::uint32_t c : g_[S[i]].ch) {
                if (pos.count(c)) continue;
                if (g_[c].done && g_[c].val) { reaches[i] = 1; break; }
            }
        }
        for (const std::vector<std::size_t>& T : sub_sccs(S, pos, alive)) {
            bool cyclic = T.size() > 1;
            if (!cyclic)
                for (std::uint32_t c : g_[S[T[0]]].ch)
                    if (auto it = pos.find(c); it != pos.end() && it->second == T[0])
                        cyclic = true;
            if (!cyclic || !progressing(S, T)) continue;
            for (std::size_t i : T) reaches[i] = 1;
        }

        const std::vector<std::vector<std::size_t>> rev = reverse_edges(S, pos, alive);
        std::vector<std::size_t> q;
        for (std::size_t i = 0; i < m; ++i) if (alive[i] && reaches[i]) q.push_back(i);
        while (!q.empty()) {
            const std::size_t i = q.back(); q.pop_back();
            for (std::size_t j : rev[i])
                if (!reaches[j]) { reaches[j] = 1; q.push_back(j); }
        }

        bool removed = false;
        for (std::size_t i = 0; i < m; ++i)
            if (alive[i] && !reaches[i]) { alive[i] = 0; removed = true; }
        return removed;
    }

    // §5.1, condition (i): delete every node from which no surviving path takes
    // the (stop) branch of an until pursuit active there.  The path must keep
    // the pursuit alive — an until leaves a path only by being stopped or by
    // riding an (EX) AND-sibling, and in the latter case it is that sibling,
    // which the marking requires to succeed on its own, that must discharge it.
    bool query_until(const std::vector<std::uint32_t>& S,
                     const std::unordered_map<std::uint32_t, std::size_t>& pos,
                     std::vector<char>& alive) {
        const std::size_t m = S.size();
        std::vector<FormulaId> mus;
        for (std::size_t i = 0; i < m; ++i)
            if (alive[i])
                for (FormulaId mu : g_[S[i]].untils) mus.push_back(mu);
        std::sort(mus.begin(), mus.end());
        mus.erase(std::unique(mus.begin(), mus.end()), mus.end());
        if (mus.empty()) return false;

        const std::vector<std::vector<std::size_t>> rev = reverse_edges(S, pos, alive);
        auto pursues = [&](std::uint32_t id, FormulaId mu) {
            const std::vector<FormulaId>& u = g_[id].untils;
            return std::find(u.begin(), u.end(), mu) != u.end();
        };

        bool removed = false;
        for (FormulaId mu : mus) {
            std::vector<char> live(m, 0), ok(m, 0);
            for (std::size_t i = 0; i < m; ++i)
                live[i] = alive[i] && pursues(S[i], mu);

            for (std::size_t i = 0; i < m; ++i) {
                if (!live[i]) continue;
                for (std::uint32_t c : g_[S[i]].ch) {
                    const bool in_S = pos.count(c) != 0;
                    const bool ca   = in_S ? alive[pos.at(c)] != 0 : (g_[c].done && g_[c].val);
                    if (!ca) continue;
                    // the stop branch itself, or a surviving exit that carries
                    // the pursuit onward and so must discharge it in turn
                    if (g_[c].discharges == mu || (!in_S && pursues(c, mu))) {
                        ok[i] = 1;
                        break;
                    }
                }
            }
            std::vector<std::size_t> q;
            for (std::size_t i = 0; i < m; ++i) if (ok[i]) q.push_back(i);
            while (!q.empty()) {
                const std::size_t i = q.back(); q.pop_back();
                for (std::size_t j : rev[i])
                    if (live[j] && !ok[j]) { ok[j] = 1; q.push_back(j); }
            }
            for (std::size_t i = 0; i < m; ++i)
                if (live[i] && !ok[i]) { alive[i] = 0; removed = true; }
        }
        return removed;
    }

    // Tarjan over the subgraph the surviving nodes of S induce.  Eliminating a
    // node can break S apart, and a component that is no longer strongly
    // connected no longer supports the cycle its classification assumed, so the
    // decomposition is recomputed rather than inherited.
    std::vector<std::vector<std::size_t>> sub_sccs(
            const std::vector<std::uint32_t>& S,
            const std::unordered_map<std::uint32_t, std::size_t>& pos,
            const std::vector<char>& alive) const {
        const std::size_t m = S.size();
        const std::size_t kUnset = static_cast<std::size_t>(-1);
        std::vector<std::size_t> idx(m, kUnset), low(m, 0);
        std::vector<char> on(m, 0);
        std::vector<std::size_t> stk, comp;
        std::vector<std::vector<std::size_t>> out;
        std::size_t counter = 0;

        struct Fr { std::size_t v, ci; };
        std::vector<Fr> st;
        for (std::size_t s = 0; s < m; ++s) {
            if (!alive[s] || idx[s] != kUnset) continue;
            idx[s] = low[s] = counter++; on[s] = 1; comp.push_back(s);
            st.push_back({s, 0});
            while (!st.empty()) {
                const std::size_t v = st.back().v;
                const std::vector<std::uint32_t>& ch = g_[S[v]].ch;
                if (st.back().ci < ch.size()) {
                    const std::uint32_t c = ch[st.back().ci++];
                    auto it = pos.find(c);
                    if (it == pos.end() || !alive[it->second]) continue;
                    const std::size_t w = it->second;
                    if (idx[w] == kUnset) {
                        idx[w] = low[w] = counter++; on[w] = 1; comp.push_back(w);
                        st.push_back({w, 0});
                    } else if (on[w]) {
                        low[v] = std::min(low[v], idx[w]);
                    }
                    continue;
                }
                if (low[v] == idx[v]) {
                    std::vector<std::size_t> T;
                    for (;;) {
                        const std::size_t w = comp.back(); comp.pop_back();
                        on[w] = 0;
                        T.push_back(w);
                        if (w == v) break;
                    }
                    out.push_back(std::move(T));
                }
                st.pop_back();
                if (!st.empty()) low[st.back().v] = std::min(low[st.back().v], low[v]);
            }
        }
        (void)stk;
        return out;
    }

    // ── On-the-fly DFS with Tarjan; SCCs are eliminated as they close ───
    bool decide_scc(const Node& root) {
        const std::uint32_t r = intern(Node(root));
        root_id_ = r;
        struct Fr { std::uint32_t v; std::size_t ci; };
        std::vector<Fr> st;
        std::vector<std::uint32_t> tstack;
        std::uint32_t counter = 0;

        auto visit = [&](std::uint32_t v) {
            g_[v].visited = true;
            g_[v].onstack = true;
            g_[v].index = g_[v].low = counter++;
            tstack.push_back(v);
            return expand_node(v);
        };

        if (!visit(r)) return false;
        st.push_back({r, 0});

        // A child's value settles its parent when the parent is an OR and the
        // child holds, or an AND and it fails.  Acting on that is sound only
        // against a child that is already *final*: the explored subgraph is
        // closed under successors except at final nodes, and a final-true node
        // certifies (M1) and (M2) for itself, so a path that would have used a
        // skipped child either meets a final-true node -- and prefixing gives
        // the witness -- or a final-false one, which is outside the marking
        // anyway.  This is what keeps the search demand-driven: the remaining
        // children are never expanded.
        auto settles = [&](std::uint32_t parent, std::uint32_t child) {
            if (!g_[child].done) return false;
            return (g_[parent].kind == Expansion::Kind::And) ? !g_[child].val
                                                             : g_[child].val;
        };

        while (!st.empty()) {
            const std::uint32_t v = st.back().v;
            if (st.back().ci < g_[v].ch.size()) {
                const std::uint32_t w = g_[v].ch[st.back().ci++];
                if (!g_[w].visited) {
                    if (!visit(w)) return false;
                    st.push_back({w, 0});
                } else if (g_[w].onstack) {
                    g_[v].low = std::min(g_[v].low, g_[w].index);
                } else if (settles(v, w) && !tstack.empty() && tstack.back() == v) {
                    // Retire v now.  The stack-top test is what makes this safe:
                    // an earlier child may have left members of v's own SCC above
                    // v, and v cannot be lifted out from under them.
                    g_[v].done = true;
                    g_[v].val  = g_[w].val;
                    g_[v].onstack = false;
                    tstack.pop_back();
                    st.pop_back();
                    release_search_state(v);
                    continue;
                }
                continue;
            }
            if (g_[v].low == g_[v].index) {
                std::vector<std::uint32_t> S;
                for (;;) {
                    const std::uint32_t w = tstack.back(); tstack.pop_back();
                    g_[w].onstack = false;
                    S.push_back(w);
                    if (w == v) break;
                }
                evaluate_scc(S);
            }
            st.pop_back();
            // Cascade: a finished child may settle its parent, that parent its
            // own parent, and so on.
            std::uint32_t done_child = v;
            while (!st.empty()) {
                const std::uint32_t pnode = st.back().v;
                if (settles(pnode, done_child) && !tstack.empty() &&
                    tstack.back() == pnode) {
                    g_[pnode].done = true;
                    g_[pnode].val  = g_[done_child].val;
                    g_[pnode].onstack = false;
                    tstack.pop_back();
                    st.pop_back();
                    release_search_state(pnode);
                    done_child = pnode;
                    continue;
                }
                g_[pnode].low = std::min(g_[pnode].low, g_[done_child].low);
                break;
            }
        }
        return g_[r].val;
    }

    // ── Iterative on-the-fly DFS with short-circuiting + memoisation ────
    bool decide_iter(const Node& root) {
        std::vector<Frame> st;
        std::unordered_map<Key, std::size_t, KeyHash> onpath;  // key → depth
        bool pend_res = false;
        std::size_t pend_lm = kInf;

        push_frame(st, root);
        while (!st.empty()) {
            Frame& fr = st.back();
            if (!fr.expanded) {
                if ((++expansions_ & 0x1FFF) == 0 && has_deadline_ &&
                    std::chrono::steady_clock::now() > deadline_) {
                    budget_hit_ = true; return false;
                }
                // resolve without expanding: closed / loop back / memo (subsumption)
                if (node_closed(fr.n.Gamma, f_) || fr.n.Z.is_empty()) {
                    dtrace(st.size()-1, "CLOSED", fr.n, -1);
                    pend_res = false; pend_lm = kInf; st.pop_back(); continue;
                }
                if (auto it = onpath.find(fr.k); it != onpath.end()) {
                    std::size_t a = it->second;
                    const bool acc = loop_accepting(st, a);
                    dtrace(st.size()-1, "LOOP", fr.n, acc);
                    pend_res = acc; pend_lm = a; st.pop_back(); continue;
                }
                bool cached;
                if (memo_lookup(fr.k, cached)) {
                    dtrace(st.size()-1, "memo", fr.n, cached);
                    pend_res = cached; pend_lm = kInf; st.pop_back(); continue;
                }
                fr.e = expand(fr.n);
                if (fr.e.kind == Expansion::Kind::Closed) {
                    dtrace(st.size()-1, "close", fr.n, -1);
                    memo_store(fr.k, false);
                    pend_res = false; pend_lm = kInf; st.pop_back(); continue;
                }
                dtrace(st.size()-1, fr.e.kind == Expansion::Kind::And ? "AND" : "OR", fr.n, -1);
                fr.expanded = true;
                fr.ci = 0;
                fr.res = (fr.e.kind == Expansion::Kind::And);
                fr.submin = kInf;
                fr.depth = st.size() - 1;
                onpath.emplace(fr.k, fr.depth);
            } else {
                // resume: fold in the child result that just bubbled up
                fr.submin = std::min(fr.submin, pend_lm);
                const bool isAnd = (fr.e.kind == Expansion::Kind::And);
                if ((isAnd && !pend_res) || (!isAnd && pend_res)) {
                    fr.res = pend_res;
                    fr.ci = fr.e.children.size();      // short-circuit
                } else {
                    ++fr.ci;
                }
            }
            if (fr.ci < fr.e.children.size()) {
                Node child = fr.e.children[fr.ci];    // copy before push invalidates fr
                push_frame(st, child);
                continue;
            }
            // finalize
            const std::size_t d = fr.depth;
            const bool self_contained = (fr.submin >= d);
            if (self_contained) memo_store(fr.k, fr.res);
            onpath.erase(fr.k);
            pend_res = fr.res;
            pend_lm  = self_contained ? kInf : fr.submin;
            st.pop_back();
        }
        return pend_res;
    }

    FormulaFactory& f_;
    bool keep_graph_ = false;    ///< retain children/untils for witness extraction
    ClockMap cmap_;
    std::size_t nc_ = 1;
    std::vector<std::int32_t> max_;
    std::vector<std::int32_t> bounds_;   // sorted formula interval endpoints (+0)
    // per clock: the endpoints of its own modality's window — the only values at
    // which a guard on that clock can flip, hence the (Delay) cell boundaries
    std::vector<std::vector<std::int32_t>> clock_bounds_;

    // full node key → verdict; the match is exact by construction
    std::unordered_map<Key, bool, KeyHash> memo_;
    SatCache sx_cache_;                  // persistent S_X(mu,X) memo
    std::uint64_t expansions_ = 0;
    bool budget_hit_ = false;
    bool has_deadline_ = false;
    bool debug_ = false;
    bool verify_decode_ = false;
    bool extra_lu_ = false;                                ///< use Extra_LU for node identity
    bool solo_launch_ = false;                             ///< one new pursuit per launch branch
    bool reuse_witness_ = false;                           ///< discharge a re-demand against a settled pursuit -- UNSOUND, opt-in
    bool record_witness_ = false;                          ///< record settled pursuits in `witnessed`
    bool free_dead_ = true;                                ///< project out clocks no live pursuit/deadline reads
    bool window_reuse_ = false;                            ///< "overlapping windows" (Cov) side condition -- UNSOUND, recorded
    std::vector<std::int32_t> lu_L_, lu_U_;                ///< per-clock L and U
    std::uint32_t root_id_ = static_cast<std::uint32_t>(-1);
    std::uint64_t decode_ok_ = 0, decode_bad_ = 0;
    bool scc_mode_ = true;
    std::chrono::steady_clock::time_point deadline_{};

    // ── SCC acceptance state (unused under TCTL_LEGACY_LOOP) ────────────
    std::vector<GNode>                             g_;     // the explored graph
    std::unordered_map<Key, std::uint32_t, KeyHash> gid_;  // acc_key → node id
    std::vector<const Key*> key_of_;                       // node id → its key
    std::size_t words_ = 1;                                // clock-bitmap width
    // key-building scratch, reused so the hot path allocates nothing
    mutable std::vector<std::array<std::uint32_t, 6>> pursuit_scratch_;
    mutable std::vector<std::array<std::uint32_t, 4>> deadline_scratch_;
    mutable std::vector<std::uint32_t> scratch32_;
    mutable std::vector<char>          lu_bits_;
    mutable std::vector<char>          live_scratch_;   ///< clocks a live pursuit/deadline reads
    // minimal-graph packing scratch, reused so key building allocates nothing
    mutable std::vector<std::uint32_t> pack_buf_, pack_bits_;
    mutable std::vector<int>           pack_first_, pack_next_;
    std::vector<std::uint64_t> cap_, res_, unb_;           // flat per-node bitmaps
};

}  // namespace

// ── Public API ───────────────────────────────────────────────────────────────

const char* result_to_string(const Result& r) noexcept {
    switch (r.verdict) {
        case Result::Value::Satisfiable:   return "SATISFIABLE";
        case Result::Value::Unsatisfiable: return "UNSATISFIABLE";
        case Result::Value::Timeout:       return "TIMEOUT";
    }
    return "UNKNOWN";
}

std::string SearchStats::to_string() const {
    // Only counters the engine actually maintains are reported: printing a
    // field that is always zero reads as a measurement rather than as an
    // absent one.
    std::ostringstream os;
    os << "nodes=" << nodes_created;
    if (distinct_zones)    os << " distinct_zones=" << distinct_zones;
    if (loop_checks)       os << " loop_checks=" << loop_checks;
    if (peak_memory_bytes) os << " peak_mem_kb=" << (peak_memory_bytes + 1023) / 1024;
    return os.str();
}

Tableau::Tableau(FormulaFactory& factory) : factory_(factory) {}

Result Tableau::check(FormulaId normalized_formula) {
    stats_.reset();
    const auto t0 = std::chrono::steady_clock::now();

    Engine engine(factory_, normalized_formula,
                  static_cast<double>(timeout_.count()), extract_witness_);
    bool sat = engine.decide(normalized_formula);

    has_witness_ = false;
    if (sat && extract_witness_ && engine.can_extract()) {
        witness_ = engine.witness();
        has_witness_ = true;
    }

    Result::Value verdict;
    if (engine.budget_hit())      verdict = Result::Value::Timeout;
    else if (sat)                 verdict = Result::Value::Satisfiable;
    else                          verdict = Result::Value::Unsatisfiable;

    stats_.nodes_created = engine.nodes();

    const auto t1 = std::chrono::steady_clock::now();
    return Result(verdict, std::chrono::duration<double>(t1 - t0).count());
}

}  // namespace tctl
