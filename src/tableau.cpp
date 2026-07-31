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


// num_clocks/max/sx_cache fed the satisfaction-set side condition, which (Cov)
// does not have.  They are kept so the call sites need not change.
CoverResult apply_cover(const Node& n, FormulaId mu, bool ag_context_,
                        const std::map<FormulaId, ClockId>& cmap,
                        [[maybe_unused]] std::size_t num_clocks,
                        [[maybe_unused]] const std::vector<std::int32_t>& max,
                        FormulaFactory& f,
                        [[maybe_unused]] SatCache& sx_cache) {
    // A persistent context such as AG μ re-demands μ at uncountably many onsets.
    // A single formula-clock x_μ serves them all (§4.2): the dense family of
    // onsets is absorbed into one finite union of zones, against which the cover
    // rule decides every demand.  So when μ is already being pursued, discharge
    // the new demand against that pursuit rather than launching a second one —
    // launching again would grow the pursuit set, and with it the node key,
    // without bound, so no two nodes would ever compare equal and the search
    // would not terminate.
    // A re-demand may be discharged against the running pursuit only when the
    // running obligation covers the new one.  Unbounded windows nest -- a later
    // witness serves every earlier onset -- so there the discharge (the early
    // return below) is sound.  A bounded universal until is rolled instead
    // (persistent flag below).  Every other bounded pursuit -- an existential
    // until, a release of either quantifier -- falls through to a full (Cov):
    // the relaunch resets x_mu and pursues the new onset, while the discharge
    // child of that (Cov) carries the running pursuit onward.
    const NodeKind mk0 = f.node(mu).kind;
    const Window mw0 = window_of(mu, f);
    const bool recover_redemand =
        clock_of(cmap, mu) != kNoClock && !mw0.hi_inf &&
        !(is_until_modality(mk0) && is_universal(mk0));
    // (Absorb).  The paper states this rule for an until: a re-demand whose
    // window is unbounded is discharged against the running pursuit, because the
    // pursuits still to be launched witness psi at unboundedly large times and an
    // absorbed onset needs only one psi past a finite point.
    //
    // Here it also takes an unbounded *release*, which the paper leaves to a
    // relaunch.  That is an optimisation, sound for the easier reason: a release
    // demands psi throughout its window, so a later onset asks for it on a
    // sub-interval of the running pursuit's and is already implied.  Measured:
    // restricting this to untils keeps every verdict and the whole suite, and
    // costs a couple of extra nodes per nested release (AG(AG p): 23 vs 21).
    for (const Pursuit& p : n.pursuits) {
        if (p.mu == mu && !recover_redemand) {
            CoverResult only;
            only.kind = CoverResult::Kind::Cover;
            Node discharge;
            discharge.Gamma = gamma_without(n.Gamma, mu);
            discharge.X = n.X; discharge.Z = n.Z; discharge.O = n.O;
            discharge.D = n.D; discharge.pursuits = n.pursuits; discharge.phase = n.phase;
            // The re-demand itself is the evidence that this demand is
            // persistent.  Discharging it against the live pursuit is sound for
            // the *window*, but nothing then bounds the time to the NEXT
            // witness -- which is the rate contradiction.  Mark the pursuit so
            // its (U-stop) rolls the clock over instead of retiring it.
            // Universal only.  An existential until under a persistent context
            // has no recurrence rate: distinct onsets may be witnessed by
            // distinct branching runs, so capping the gap between consecutive
            // witnesses on one run over-constrains it (measured: it turns
            // AG(EF[1,3](AG(EF[4,6](AG(EF[7,9]p))))) UNSAT, which is SAT).
            const Window rw = window_of(mu, f);
            if (is_until_modality(f.node(mu).kind) && is_universal(f.node(mu).kind) &&
                !rw.hi_inf && clock_of(cmap, mu) != kNoClock) {
                for (Pursuit& q : discharge.pursuits)
                    if (q.mu == mu) q.persistent = true;
            }
            only.children.push_back(std::move(discharge));
            return only;
        }
    }

    // (Cov) for a safety context, under TCTL_AG_CONTEXT.
    //
    // A universal release whose left argument is bot and whose window is the
    // whole timeline is AG psi, and nothing about it is ever decided: bot never
    // releases the obligation, the window never closes, and (R-unf) takes the
    // same branch at every step for ever.  It is a pursuit only because release
    // is uniformly handled as one, and it costs a live pursuit per nesting
    // level -- on a tower of AG(EF ...) the pursuit vector then ranges over the
    // product of a per-level state that has one reachable value.
    //
    // Its fixpoint law is AG psi = psi & AX AG psi, and the calculus already
    // carries "holds at every successor" in the context X.  So the launch adds
    // psi to the goals and mu to X, and no pursuit is created: the successor
    // rule re-imposes mu at each successor, which is the same obligation with
    // none of the state.
    if (ag_context_ && !is_until_modality(f.node(mu).kind) &&
        is_universal(f.node(mu).kind)) {
        const Window w = window_of(mu, f);
        const FormulaNode& mn = f.node(mu);
        const bool whole_line = w.lo == 0 && !w.lo_strict && w.hi_inf;
        const bool never_released =
            mn.children[0] != kInvalidId &&
            f.node(mn.children[0]).kind == NodeKind::False;
        if (whole_line && never_released) {
            CoverResult only;
            only.kind = CoverResult::Kind::Cover;
            Node ctxc;
            ctxc.Gamma = gamma_without(n.Gamma, mu);
            ctxc.Gamma.insert(mn.children[1]);          // psi holds here
            ctxc.X = n.X; ctxc.X.insert(mu);            // and at every successor
            ctxc.Z = n.Z; ctxc.O = n.O; ctxc.D = n.D;
            ctxc.pursuits = n.pursuits; ctxc.phase = n.phase;
            only.children.push_back(std::move(ctxc));
            return only;
        }
    }

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
    base.pursuits = n.pursuits; base.phase = n.phase;

    // (Cov) is unconditional (paper §4.2): a demanded mu forks into a discharge
    // and a launch, full stop.  There is no satisfaction-set side condition --
    // the `S_X(mu) contains Z' gate, and the PartialCover narrowing it fell back
    // on, are left over from the pre-cover-rule construction.  Node::X is never
    // populated, so S_X was computed against an empty context, the gate always
    // held and the narrowing never fired.  Removing both is behaviour-preserving.
    {
        res.kind = CoverResult::Kind::Cover;
        Node discharge = base;
        Node launch = base;
        if (x_mu != kNoClock) {
            launch.Z.reset(x_mu);
            launch.just_reset.push_back(x_mu);
            bool haveO = false;
            for (const auto& e : launch.O)
                if (e.first == mu) { haveO = true; break; }
            if (!haveO) {
                // keep O sorted; it is written once per launch and never searched
                launch.O.emplace_back(mu, x_mu);
                std::sort(launch.O.begin(), launch.O.end());
            }
        }
        Pursuit p; p.mu = mu; p.x_mu = x_mu;
        p.stage = Pursuit::Stage::Here; p.part = Pursuit::Part::Whole;
        p.is_until = until_kind;
        // A relaunch (E re-demand) replaces the live pursuit rather than
        // appending a second one: one clock, one pursuit per modality.
        bool replaced = false;
        for (Pursuit& q : launch.pursuits)
            if (q.mu == mu) { q = p; replaced = true; break; }
        if (!replaced) launch.pursuits.push_back(p);
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
        root_formula_ = root;
        cmap_ = assign_clocks(root, f);
        nc_ = 1 + cmap_.size();
        std::int32_t M = max_constant(root, f);
        max_.assign(nc_, M);
        max_[0] = 0;
        collect_boundaries(root, f);
        collect_clock_bounds(root, f);
        // A formula-clock is only ever compared against the endpoints of its own
        // window, so extrapolating every clock at the global maximum constant M
        // preserves distinctions no guard can observe.  Per-clock maxima are
        // sound because every guard is single-clock (§3), and they attack the
        // M^O(K^2) zone count of Lemma 1 directly.  The maximum is read off the
        // clock's *own* constants, before the shifts added below, which only
        // refine where time is split and never widen what a guard can see.
        for (ClockId c = 1; c < nc_; ++c)
            max_[c] = clock_bounds_[c].empty() ? 0 : clock_bounds_[c].back();
        add_onset_shifts(root, f);
        collect_top_ags(root, f);
        number_atoms(root, f);
        debug_ = std::getenv("TCTL_DEBUG") != nullptr;
        words_ = (nc_ + 63) / 64;
    }

    /// Split points a clock needs so that *onsets* stay distinguishable.
    ///
    /// A clock's own constants are where its guards flip, but not where the
    /// demands it carries flip.  Under a context banning p over [c,d], an onset
    /// at time t demands p somewhere in [t+a, t+b], and that demand is
    /// unsatisfiable exactly for t in [c-a, d-b].  Splitting the context clock
    /// only at c and d leaves that interval inside a cell that also holds
    /// satisfiable onsets, and the cell's launch succeeds on one of those: on
    /// AG(EF[3,4] p) & AG[4,5] !p the bad onset is the single point t=1, no cell
    /// isolates it, and the search reports SAT for an unsatisfiable formula.
    ///
    /// So an enclosing modality's clock is split, in addition, at its own
    /// endpoints shifted by those of each modality nested inside it.  The shifts
    /// are read off nesting pairs rather than off all pairs of constants: a
    /// clock gains at most two split points per modality below it, and none of
    /// them depends on the magnitude of a constant, which is what keeps the
    /// search flat in M.
    void add_onset_shifts(FormulaId root, FormulaFactory& f) {
        // Every timed modality of the formula, with its window.
        struct Mod { FormulaId id; std::int32_t a, b; bool binf; };
        std::vector<Mod> mods;
        std::function<void(FormulaId)> walk = [&](FormulaId x) {
            if (x == kInvalidId) return;
            const FormulaNode& n = f.node(x);
            if (is_timed(n.kind))
                mods.push_back({x, static_cast<std::int32_t>(n.time_lower.value),
                                n.time_upper.is_infinity ? 0
                                    : static_cast<std::int32_t>(n.time_upper.value),
                                n.time_upper.is_infinity});
            walk(n.children[0]); walk(n.children[1]);
        };
        walk(root);

        // The two are related by being live together, not by nesting: in
        // AG[c,d] !p & AG(EF[a,b] p) the ban and the demand are conjuncts.  So
        // every modality's clock takes the shifts of every other's window.
        for (const Mod& rho : mods) {
            const ClockId ec = clock_of(cmap_, rho.id);
            if (ec == kNoClock || ec >= nc_ || clock_bounds_[ec].empty()) continue;
            std::vector<std::int32_t>& bs = clock_bounds_[ec];
            for (const Mod& mu : mods) {
                if (mu.id == rho.id) continue;
                const std::int32_t lo = rho.a - mu.a;
                if (lo > 0 && lo < max_[ec]) bs.push_back(lo);
                if (!rho.binf && !mu.binf) {
                    const std::int32_t hi = rho.b - mu.b;
                    if (hi > 0 && hi < max_[ec]) bs.push_back(hi);
                }
            }
        }
        for (std::vector<std::int32_t>& bs : clock_bounds_) {
            std::sort(bs.begin(), bs.end());
            bs.erase(std::unique(bs.begin(), bs.end()), bs.end());
        }
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

    // Memoisation + boundary-region abstraction keep the search shallow.  The
    // process runs with an enlarged main-thread stack (set via a linker option,
    // see CMakeLists.txt) so deep-but-finite runs do not overflow — no per-check
    // thread and no artificial depth limit.
    bool decide(FormulaId root) {

        Node n;
        n.Gamma.insert(root);
        n.Z = Zone::zero(nc_);
        n.phase = Phase::Elapse;
        return decide_scc(n);
    }

    std::uint64_t nodes() const { return expansions_ + sub_nodes_; }
    bool budget_hit() const { return budget_hit_; }

    /// Witness automaton for the marking of the last successful decide().
    /// Only meaningful when SCC acceptance ran and the verdict was SAT.
    TimedAutomaton witness() { return extract_witness(root_id_); }

    /// Turn the optional optimisations on or off as a set.  Environment
    /// variables still act as per-feature overrides, so a single optimisation
    /// can be isolated for a measurement without rebuilding.
    void apply_version(bool v2) {
        if (std::getenv("TCTL_COMPONENTS") == nullptr)    decomp_ = v2;
        if (std::getenv("TCTL_SUBSUME_GOALS") == nullptr) subsume_goals_ = v2;
    }
    bool can_extract() const { return root_id_ != kNoRegion; }

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
                                        static_cast<std::uint32_t>(p.persistent),
                                        static_cast<std::uint32_t>(p.rolled)});
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
    // ── Interned zones ──────────────────────────────────────────────────
    //
    // A node's key used to carry the packed zone itself, so the same zone was
    // minimal-graph reduced and copied once per node that reached it.  It is
    // reached many times: on a 16-window instance 787453 packs produced 131427
    // distinct zones, a factor of six, and on a nested tower the factor is
    // eleven.  Zones are therefore interned, and the key carries a four-byte id.
    // Two things follow.  Reduction runs once per distinct zone rather than once
    // per node, and the keys shrink from a few hundred words to one, which is
    // what the node table hashes and stores on every lookup.
    //
    // In front of the pool sits a direct-mapped cache on the *raw* matrix, since
    // the pool can only be consulted with a packed zone and packing is the cost
    // being avoided.  A hit is verified by comparing the raw entries, so the
    // cache never decides an identity it has not checked; it is bounded, so a
    // long run cannot spend the memory that holding every raw matrix would.
    std::uint32_t zone_id(const Zone& ez) const {
        const int dim = static_cast<int>(ez.num_clocks());
        const raw_t* raw = ez.raw_data();
        const std::size_t n = static_cast<std::size_t>(dim) * dim;

        // Two entries per round.  The hash only buckets the cache; a collision
        // costs a miss, never a wrong answer, because the line is confirmed by
        // comparing the raw entries below.  Exactness lives in the pool, which
        // is keyed on the packed bytes.
        std::uint64_t h = 1469598103934665603ull;
        {
            const auto* w = reinterpret_cast<const std::uint64_t*>(raw);
            const std::size_t nw = n / 2;
            for (std::size_t i = 0; i < nw; ++i) {
                h = (h ^ w[i]) * 1099511628211ull;
            }
            if (n & 1) h = (h ^ static_cast<std::uint64_t>(
                                static_cast<std::uint32_t>(raw[n - 1]))) *
                           1099511628211ull;
        }
        const std::size_t slot = h & (kZoneCacheSlots - 1);
        ZoneCacheLine& line = zcache_[slot];
        if (line.id != kNoRegion && line.raw.size() == n &&
            std::equal(line.raw.begin(), line.raw.end(), raw))
            return line.id;

        pack_buf_.resize((ptctlmc::mindbm_bound(dim) + 3) / 4);
        pack_bits_.resize(ptctlmc::mindbm_bits2words(
            static_cast<std::uint32_t>(dim) * static_cast<std::uint32_t>(dim)));
        pack_first_.resize(static_cast<std::size_t>(dim));
        pack_next_.resize(static_cast<std::size_t>(dim));
        // The packer writes whole records but not whole words: with 16-bit
        // bounds and an odd constraint count the last half-word is never
        // written, and it sits *inside* the length the packer reports.  The
        // buffer is reused, so that half-word carries whatever the previous zone
        // left there, and the same zone then encodes differently depending on
        // what was packed before it -- which showed up as the node count moving
        // when an unrelated cache changed how often the packer ran.  Clearing
        // the whole buffer makes the encoding a function of the zone alone.
        std::memset(pack_buf_.data(), 0, pack_buf_.size() * sizeof(std::uint32_t));
        const std::size_t bytes =
            ptctlmc::mindbm_pack(raw, dim, pack_buf_.data(), pack_bits_.data(),
                                 pack_first_.data(), pack_next_.data());
        const std::size_t words = (bytes + 3) / 4;
        // mindbm_pack writes `bytes`, not whole words, and the buffer is reused
        // across calls, so the tail of the last word still holds whatever a
        // previous, larger zone left there.  That tail used to travel into the
        // node key, where it split one zone into several keys depending on what
        // had been packed before it, and the search then rebuilt the same node
        // more than once.  Zeroing it makes the encoding a function of the zone
        // alone.
        std::memset(reinterpret_cast<char*>(pack_buf_.data()) + bytes, 0,
                    words * sizeof(std::uint32_t) - bytes);

        std::string packed(reinterpret_cast<const char*>(pack_buf_.data()),
                           words * sizeof(std::uint32_t));
        auto it = zids_.find(packed);
        std::uint32_t id;
        if (it != zids_.end()) {
            id = it->second;
        } else {
            id = static_cast<std::uint32_t>(zpool_.size());
            zpool_.emplace_back(pack_buf_.begin(),
                                pack_buf_.begin() + static_cast<std::ptrdiff_t>(words));
            zids_.emplace(std::move(packed), id);
        }
        line.id = id;
        line.raw.assign(raw, raw + n);
        return id;
    }

    void append_zone(const Zone& ez, Key& k) const {
        if (ez.is_empty()) { put(k, 0); return; }
        put(k, 1);
        put(k, zone_id(ez));
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

    // ── Scheduling the marking (§5, "from a marking to an automaton") ────────
    //
    // (M2) promises, for each until pursuit active at a node, *some* path of the
    // marking that stops it.  Different pursuits want different paths, and a run
    // of the extracted automaton commits to one branch per (OR) node, so a fixed
    // choice per node serves one pursuit and starves the rest: on AG(EF p & EF q)
    // taking the first accepted child everywhere defers both eventualities for
    // ever, and the automaton labels no location with p or q at all.
    //
    // So the automaton is built over pairs (node, pursuit currently served).  At
    // an (OR) node the child taken is the one that moves closest to a stop for
    // that pursuit, and once the stop is taken the schedule turns round-robin to
    // the next pursuit pending there.  The memory is one FormulaId, so the
    // locations stay finite: at most one per node per active pursuit.

    static constexpr std::uint32_t kFar = 0xFFFFFFFFu;   ///< no stop reachable

    /// Distance, over accepted edges, from each node to a stop for @p mu.
    ///
    /// An (OR) node needs one child that reaches the stop, since the run picks
    /// the child; an (AND) node needs every child that still carries the pursuit
    /// to reach it, since the run may take any of them.  Children that do not
    /// carry @p mu impose nothing: under E the residual travels to a single
    /// successor, and the siblings are free of it.
    std::vector<std::uint32_t> stop_distance(FormulaId mu) const {
        const std::size_t m = g_.size();
        std::vector<std::uint32_t> d(m, kFar);
        auto carries = [&](std::uint32_t v) {
            const std::vector<FormulaId>& u = g_[v].untils;
            return std::find(u.begin(), u.end(), mu) != u.end();
        };
        // Relaxation rather than a plain BFS: the max at (AND) nodes is not a
        // shortest-path step, but both operators are monotone and the values
        // only fall, so iterating to a fixpoint terminates.
        for (bool changed = true; changed;) {
            changed = false;
            for (std::uint32_t v = 0; v < m; ++v) {
                if (!g_[v].done || !g_[v].val || !carries(v)) continue;
                std::uint32_t nd = kFar;
                for (std::uint32_t c : g_[v].ch)
                    if (c != v && g_[c].val && g_[c].discharges == mu) { nd = 0; break; }
                if (nd != 0) {
                    const bool orn = g_[v].kind == Expansion::Kind::Or;
                    bool any = false;
                    std::uint32_t acc = orn ? kFar : 0;
                    for (std::uint32_t c : g_[v].ch) {
                        if (c == v || !g_[c].val || !carries(c)) continue;
                        any = true;
                        const std::uint32_t dc = d[c] == kFar ? kFar : d[c] + 1;
                        acc = orn ? std::min(acc, dc) : std::max(acc, dc);
                    }
                    nd = any ? acc : kFar;
                }
                if (nd < d[v]) { d[v] = nd; changed = true; }
            }
        }
        return d;
    }

    /// The pursuit the schedule serves at @p v, given the one it served before.
    ///
    /// Keeps @p cur while it is still pending, and otherwise takes the next
    /// pending pursuit cyclically after it, so no pursuit is passed over twice.
    /// kInvalidId means nothing is pending and any accepted child will do.
    FormulaId next_obligation(std::uint32_t v, FormulaId cur) const {
        std::vector<FormulaId> u = g_[v].untils;
        std::sort(u.begin(), u.end());
        u.erase(std::unique(u.begin(), u.end()), u.end());
        if (u.empty()) return kInvalidId;
        if (std::find(u.begin(), u.end(), cur) != u.end()) return cur;
        if (cur == kInvalidId) return u.front();
        auto it = std::upper_bound(u.begin(), u.end(), cur);
        return it == u.end() ? u.front() : *it;
    }

    /// The accepted children the schedule takes at @p v while serving @p mu,
    /// each paired with the pursuit to serve after the step.
    ///
    /// With no until pending (@p mu == kInvalidId) the obligation served is
    /// \ref{M1}'s divergence: head for a saturated node, whose (Delay)/(EX)
    /// step becomes an edge of the automaton.  Leaving this case to "any
    /// accepted child" lets the pick loop through expansion-only nodes for
    /// ever, a region with no successor step, i.e. a location whose invariant
    /// blocks time with no edge out — a timelock.
    std::vector<std::pair<std::uint32_t, FormulaId>>
    scheduled_children(std::uint32_t v, FormulaId mu) const {
        std::vector<std::pair<std::uint32_t, FormulaId>> out;
        auto after = [&](std::uint32_t c) {
            // The stop discharges the pursuit, so the next node serves another.
            return g_[c].discharges == mu ? kInvalidId : mu;
        };
        if (g_[v].kind == Expansion::Kind::Or) {
            // A node that is its own child -- (U*-stop) re-applied where its
            // goal, reset and deadline are all already in force -- offers a
            // self-loop that elapses no time and discharges nothing new.  Its
            // own discharge marker describes the edge that *entered* it, so
            // without this the loop below reads it as a free stop and takes the
            // loop for ever, leaving a location with no successor step at all.
            bool other = false;
            for (std::uint32_t c : g_[v].ch) if (c != v && g_[c].val) other = true;
            std::uint32_t best = kNoRegion, bestd = kFar;
            for (std::uint32_t c : g_[v].ch) {
                if (!g_[c].val || (other && c == v)) continue;
                std::uint32_t dc = 0;
                if (mu != kInvalidId && g_[c].discharges != mu) {
                    auto it = wdist_.find(mu);
                    const std::uint32_t dd = it == wdist_.end() ? kFar : it->second[c];
                    dc = dd == kFar ? kFar : dd + 1;
                } else if (mu == kInvalidId) {
                    dc = c < sdist_.size() ? sdist_[c] : kFar;
                }
                if (best == kNoRegion || dc < bestd) { best = c; bestd = dc; }
                if (bestd == 0) break;
            }
            if (best != kNoRegion) out.push_back({best, after(best)});
        } else {
            for (std::uint32_t c : g_[v].ch)
                if (g_[c].val) out.push_back({c, after(c)});
        }
        return out;
    }

    /// Distance, over accepted edges, from each accepted node to a saturated
    /// one — the divergence metric of the schedule.  OR takes the best child,
    /// AND the worst, since a run may be sent down any retained branch.
    std::vector<std::uint32_t> saturated_distance() {
        const std::size_t m = g_.size();
        std::vector<std::uint32_t> d(m, kFar);
        for (std::uint32_t v = 0; v < m; ++v)
            if (g_[v].done && g_[v].val &&
                is_saturated(decode_key(*key_of_[v]))) d[v] = 0;
        for (bool changed = true; changed;) {
            changed = false;
            for (std::uint32_t v = 0; v < m; ++v) {
                if (!g_[v].done || !g_[v].val || d[v] == 0) continue;
                const bool orn = g_[v].kind == Expansion::Kind::Or;
                bool any = false;
                std::uint32_t acc = orn ? kFar : 0;
                for (std::uint32_t c : g_[v].ch) {
                    if (c == v || !g_[c].val) continue;
                    any = true;
                    const std::uint32_t dc = d[c] == kFar ? kFar : d[c] + 1;
                    acc = orn ? std::min(acc, dc) : std::max(acc, dc);
                }
                const std::uint32_t nd = any ? acc : kFar;
                if (nd < d[v]) { d[v] = nd; changed = true; }
            }
        }
        return d;
    }

    TimedAutomaton extract_witness(std::uint32_t root) {
        TimedAutomaton ta;
        ta.num_clocks = nc_;
        for (const auto& [mu, clk] : cmap_)
            if (clk != kNoClock && clk < nc_)
                ta.clock_names[clk] = "x_" + std::to_string(clk);

        // The schedule needs, per pursuit, how far each node is from stopping it.
        wdist_.clear();
        for (std::uint32_t v = 0; v < g_.size(); ++v)
            if (g_[v].done && g_[v].val)
                for (FormulaId mu : g_[v].untils)
                    if (!wdist_.count(mu)) wdist_.emplace(mu, stop_distance(mu));
        sdist_ = saturated_distance();

        // A location is the marked region opened by a head: the marked nodes
        // reachable from it without crossing an (EX) step.  A head is a node
        // paired with the pursuit the schedule is serving on arrival, so one
        // proof node reached while serving two different pursuits opens two
        // locations, which is what keeps each of them from starving.
        using Head = std::pair<std::uint32_t, FormulaId>;
        std::map<Head, std::uint32_t> region_of;                // head -> location
        std::vector<Head> heads;
        std::vector<std::vector<std::uint32_t>> members;
        std::vector<std::uint32_t> witness_node;   // the node a location is read off
        std::vector<std::pair<std::uint32_t, std::uint32_t>> edges;  // (loc, loc)

        auto head_of = [&](std::uint32_t v, FormulaId mu) {
            const Head h{v, next_obligation(v, mu)};
            auto it = region_of.find(h);
            if (it != region_of.end()) return it->second;
            const std::uint32_t r = static_cast<std::uint32_t>(heads.size());
            region_of.emplace(h, r);
            heads.push_back(h);
            members.emplace_back();
            witness_node.push_back(v);       // the head, until an exit is found
            return r;
        };

        const std::uint32_t r0 = head_of(root, kInvalidId);
        for (std::uint32_t r = 0; r < heads.size(); ++r) {   // heads grows as we go
            std::vector<Head> stack{heads[r]};
            std::set<Head> seen;
            while (!stack.empty()) {
                const auto [v, mu0] = stack.back();
                stack.pop_back();
                if (!seen.insert({v, mu0}).second) continue;
                members[r].push_back(v);
                // The pursuit served here, which the arriving one settles unless
                // it has since been discharged.
                const FormulaId mu = next_obligation(v, mu0);

                const Node n = decode_key(*key_of_[v]);
                // (R^split) is conjunctive but partitions the *zone*, so its
                // children describe disjoint sets of valuations rather than one
                // configuration.  Folding them into a single region would union
                // labels that never hold together (measured: one instance in
                // 4166 asserted r and !r at the same location).  Any expansion
                // step that hands its children different zones is therefore a
                // cut, exactly as a successor step is.
                bool partitions = false;
                if (!is_saturated(n) && g_[v].kind == Expansion::Kind::And) {
                    const Zone* first = nullptr;
                    Node prev;
                    for (std::uint32_t c : g_[v].ch) {
                        if (!g_[c].val) continue;
                        Node cn = decode_key(*key_of_[c]);
                        if (!first) { prev = std::move(cn); first = &prev.Z; }
                        else if (!(cn.Z == *first)) { partitions = true; break; }
                    }
                }
                if (is_saturated(n) || partitions) {
                    // A successor rule fires here, \ruleref{Delay} in the elapse
                    // phase and (EX) in the discrete one, and both leave the
                    // configuration this location stands for.  Cutting at (EX)
                    // alone would let a region span a delay and so merge two
                    // configurations whose labels disagree: on AG EF p the
                    // region would hold a node with p and a node without.
                    if (witness_node[r] == heads[r].first) witness_node[r] = v;
                    for (const auto& [c, nmu] : scheduled_children(v, mu))
                        edges.push_back({r, head_of(c, nmu)});
                    continue;                                // do not cross it
                }
                for (const auto& [c, nmu] : scheduled_children(v, mu))
                    stack.push_back({c, nmu});
            }
        }

        // ── locations ───────────────────────────────────────────────────
        for (std::uint32_t r = 0; r < heads.size(); ++r) {
            TALocation loc;
            loc.id = r;
            loc.is_initial = (r == r0);
            // The region is now one configuration: no rule inside it elapses
            // time or takes an edge, the (Cov) fork and the saturation rules are
            // conjunctive, and the schedule has already resolved the (OR) nodes.
            // So every member asserts what holds here, and the location carries
            // the union of their literals rather than one member's.
            std::map<ClockId, Deadline> inv;
            for (std::uint32_t v : members[r]) {
                const Node n = decode_key(*key_of_[v]);
                for (FormulaId id : n.Gamma.elements()) {
                    const FormulaNode& fn = f_.node(id);
                    if (fn.kind == NodeKind::Atom) loc.atoms.insert(fn.atom_name);
                    else if (fn.kind == NodeKind::Not &&
                             f_.node(fn.children[0]).kind == NodeKind::Atom)
                        loc.atoms.insert("!" + f_.node(fn.children[0]).atom_name);
                }
                // Inv(N): the deadline a universal until registered here bounds
                // how long the location may let time pass.  A launch inside the
                // region installs its own, so the tightest per clock is kept.
                for (const Deadline& d : n.D) {
                    if (d.x_mu == kNoClock || d.x_mu >= nc_) continue;
                    auto it = inv.find(d.x_mu);
                    if (it == inv.end() || d.bound < it->second.bound ||
                        (d.bound == it->second.bound && d.strict && !it->second.strict))
                        inv[d.x_mu] = d;
                }
            }
            for (const auto& [x, d] : inv) {
                TAConstraint c;
                c.clock_x = x; c.clock_y = kReferenceClock;
                c.bound = static_cast<std::int32_t>(d.bound);
                c.is_strict = d.strict; c.is_upper = true;
                loc.invariants.push_back(c);
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
            const Node tgt = decode_key(*key_of_[heads[to].first]);
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

        const std::uint32_t np = k[i++];
        for (std::uint32_t t = 0; t < np; ++t) {
            Pursuit p;
            p.mu       = static_cast<FormulaId>(k[i++]);
            p.x_mu     = static_cast<ClockId>(k[i++]);
            p.stage      = static_cast<Pursuit::Stage>(k[i++]);
            p.part       = static_cast<Pursuit::Part>(k[i++]);
            p.is_until   = k[i++] != 0;
            p.persistent = k[i++] != 0;
            p.rolled     = k[i++] != 0;
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
            const void* packed = static_cast<const void*>(zpool_[k[i++]].data());
            std::vector<raw_t> dense(nc_ * nc_);
            ptctlmc::mindbm_unpack(packed, dense.data());
            n.Z = Zone::from_raw(nc_, dense.data());
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
    Zone canon_zone(const Node& n) const {
        Zone z = n.Z;
        z.extrapolate(max_);
        return z;
    }


    // ── Exact dead-clock elimination ────────────────────────────────────
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
    // It discharges no obligation and drops no
    // child of (Cov): every re-demand still launches a fresh pursuit.  It only
    // stops the settled pursuit's leftover clock value from splitting nodes
    // that are otherwise identical — which is where the cost of relaunching
    // actually goes.
    // ── Goal subsumption ────────────────────────────────────────────────
    //
    // Two goals of Gamma can imply a third, and carrying the consequence as
    // well as its cause splits nodes that stand for the same demand.
    //
    // A release asserts its right argument here.  For Q(phi R_I psi) with
    // 0 in I, the semantics quantifies over the positions whose time lies in I,
    // and psi may only be excused at a position by a phi strictly before it;
    // position 0 has none before it, so psi holds at this configuration
    // outright.  Both quantifiers give it: under A every run has psi here, and
    // under E the witnessing run has psi here, which is this configuration
    // either way.  So psi in Gamma beside such a release is redundant, and the
    // release's own unfolding puts it back before any time elapses.
    //
    // A disjunction is implied by any of its disjuncts.  Where one is already a
    // goal, the disjunction says nothing further, and dropping it spares the
    // search the (Disj) branch it would otherwise take.
    //
    // Neither rule discards an obligation, so neither can turn an unsatisfiable
    // node satisfiable; both merge nodes that differ only in how much of what
    // they demand is spelled out.
    void subsume_goals(Node& n) const {
        if (!subsume_goals_) return;
        const FormulaIdVec& g = n.Gamma.elements();
        if (g.size() < 2) return;
        // One pass collects what the goals imply, a second drops it.  The
        // quadratic version of this scan cost about what it saved on formulas
        // that carry no redundancy at all, which is most of them.
        implied_.clear();
        for (FormulaId id : g) {
            const FormulaNode& o = f_.node(id);
            if (o.kind == NodeKind::Or) {
                if (n.Gamma.contains(o.children[0]) ||
                    n.Gamma.contains(o.children[1]))
                    implied_.push_back(id);              // a disjunct holds
            } else if (is_modality(o.kind) && !is_until_modality(o.kind)) {
                const Window w = window_of(id, f_);
                if (w.lo == 0 && !w.lo_strict && o.children[1] != kInvalidId)
                    implied_.push_back(o.children[1]);   // the release asserts it
            }
        }
        if (implied_.empty()) return;
        std::sort(implied_.begin(), implied_.end());
        implied_.erase(std::unique(implied_.begin(), implied_.end()),
                       implied_.end());

        FormulaIdVec keep;
        keep.reserve(g.size());
        for (FormulaId id : g) {
            // Never drop a literal.  Closure is decided on Gamma_prop, so a
            // literal removed here is a literal the contradiction test cannot
            // see, and the release that implies it only puts it back at the
            // next expansion -- by which time the complementary literal may
            // have been consumed.  Measured: without this guard
            // EG(AF p & AG !p) is reported SAT.
            const FormulaNode& idn = f_.node(id);
            const bool lit = idn.kind == NodeKind::Atom ||
                             (idn.kind == NodeKind::Not &&
                              f_.node(idn.children[0]).kind == NodeKind::Atom);
            if (lit || !std::binary_search(implied_.begin(), implied_.end(), id))
                keep.push_back(id);
        }
        if (keep.size() != g.size()) n.Gamma = FormulaSet::from_sorted(keep);
    }

    void collapse_dead_clocks(Node& n) const {
        if (n.Z.is_empty()) return;
        live_scratch_.assign(nc_, 0);
        for (const Pursuit& p : n.pursuits)
            if (p.x_mu != kNoClock && p.x_mu < nc_) live_scratch_[p.x_mu] = 1;
        for (const Deadline& d : n.D)
            if (d.x_mu < nc_) live_scratch_[d.x_mu] = 1;
        dead_scratch_.assign(nc_, 0);
        bool any = false;
        for (ClockId c = 1; c < nc_; ++c)
            if (!live_scratch_[c]) { dead_scratch_[c] = 1; any = true; }
        if (any) n.Z.free_many(dead_scratch_);
    }

    // Full key, together with the canonical zone it was built over, so the
    // extrapolation is paid once per node rather than once per use.
    void build_key(const Node& n, Key& k, Zone& ez) const {
        k.clear();
        ez = canon_zone(n);
        append_struct_key(n, k);
        append_zone(ez, k);
    }

    /// The guard a pursuit is tested against.  Before any rollover that is the
    /// modality's own window I; after one, x_mu measures time since the last
    /// witness, so the guard is the *recurrence* window [0, sup I - inf I].
    Window pursuit_window(const Pursuit& p) const {
        Window w = window_of(p.mu, f_);
        if (!p.rolled || w.hi_inf) return w;
        Window r;
        r.lo = 0; r.lo_strict = false;
        r.hi_inf = false; r.hi = w.hi - w.lo;
        r.hi_strict = w.hi_strict || w.lo_strict;
        return r;
    }

    /// Trace one node to stderr under TCTL_DEBUG.
    void dtrace(std::size_t depth, const char* tag, const Node& n, int res) const {
        if (!debug_) return;
        std::ostringstream os;
        os << '#' << depth << ' ' << tag;
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
                CoverResult cr = apply_cover(n, id, ag_context_for(id), cmap_,
                                             nc_, max_, f_, sx_cache_);
                switch (cr.kind) {
                    case CoverResult::Kind::Close:
                        return {Expansion::Kind::Closed, {}};
                    case CoverResult::Kind::Cover:
                        return {Expansion::Kind::And, std::move(cr.children)};
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
        const Window w = pursuit_window(p);
        const auto defer = existential ? Pursuit::Stage::DeferEX
                                       : Pursuit::Stage::DeferAX;

        if (p.is_until) {
            // A bounded window the whole zone has already passed refutes the
            // branch: no run from this pursuit's onset can witness psi any
            // more, so the node closes rather than defers.  (An A-until never
            // gets here -- its deadline emptied the zone first.)  Without this
            // the pursuit rides above M, where extrapolation erases its onset
            // diagonals and merges it with an accepted twin from a branch
            // whose onsets were all witnessable; query_until then counts that
            // twin as the exit that "discharges it in turn".
            if (!w.hi_inf && p.x_mu != kNoClock) {
                Zone can = n.Z;
                can.add_upper_bound(p.x_mu, w.hi, w.hi_strict);
                if (can.is_empty()) return {Expansion::Kind::Closed, {}};
            }
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
                        stop.pursuits[i].rolled = true;
                        // Retune the cap to the recurrence bound sup I - inf I:
                        // the launch deadline was sup I, measured from an onset,
                        // and x_mu now measures from the last witness.
                        const Window ow = window_of(p.mu, f_);
                        if (!ow.hi_inf) {
                            stop.D = drop_deadline(n.D, p.x_mu);
                            stop.D.push_back(Deadline{p.x_mu, ow.hi - ow.lo,
                                                      ow.hi_strict || ow.lo_strict});
                            std::sort(stop.D.begin(), stop.D.end());
                        }
                    } else {
                        stop.pursuits.erase(stop.pursuits.begin() + static_cast<long>(i));
                        stop.D = drop_deadline(n.D, p.x_mu);
                    }
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
            // An untimed release has no clock, so (R^split)'s before- and
        // after-window parts are empty and the whole-zone stage exists only to
        // be rewritten into the in-window one on the very next step.  Reviving
        // straight into that stage costs nothing and removes a state per live
        // release: on a tower of AG(EF ...) every level carries one, so the
        // node's pursuit vector was ranging over 2^depth combinations that
        // differ in a field with one reachable value.
        // Whole is the pre-split state of a release pursuit, and (R^split)
        // partitions the zone into the parts before, inside and after the
        // window.  When the zone already lies wholly in one of them the split
        // has exactly one non-empty child, carrying the same zone and differing
        // only in this field -- so the Whole node and its single child are two
        // nodes for one configuration.  Reviving straight into the part the
        // zone determines removes the first of them.  The clockless case is
        // where the window is the whole timeline and the answer is always InI.
        auto revive = [&](Pursuit q) {
            q.stage = Pursuit::Stage::Here;
            q.part = Pursuit::Part::Whole;
            if (q.is_until) return q;
            if (q.x_mu == kNoClock) { q.part = Pursuit::Part::InI; return q; }
            const Window w = window_of(q.mu, f_);
            Zone before = n.Z; before.add_upper_bound(q.x_mu, w.lo, !w.lo_strict);
            Zone in = n.Z; constrain_in_window(in, q.x_mu, w);
            Zone after = n.Z;
            if (!w.hi_inf) after.add_lower_bound(q.x_mu, w.hi, !w.hi_strict);
            else after = Zone::empty(nc_);
            const int parts = (!before.is_empty()) + (!in.is_empty()) +
                              (!after.is_empty());
            if (parts == 1) {
                if (!before.is_empty())  q.part = Pursuit::Part::BeforeI;
                else if (!in.is_empty()) q.part = Pursuit::Part::InI;
                // wholly after the window: the obligation has lapsed, and
                // (R^split) would drop the pursuit -- leave Whole so it does.
            }
            return q;
        };
        auto make_child = [&](const Pursuit* ex_one) {
            Node c;
            c.X = n.X;
            c.Gamma = n.X;             // {ψ} ∪ X base
            c.Z = n.Z; c.O = n.O; c.D = n.D; c.phase = Phase::Elapse;
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


    // ── Explicit-stack frame (no call recursion → no stack overflow) ────

    // because one particular back-edge happens to close a bad one.  That is the
    // whole difference from a path-local loop test, which returns a verdict on the
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
        // Only a *live* clock's reset is worth recording.  \ref M1 asks that
        // every clock on a cycle be reset on it or extrapolated above M, and a
        // clock no pursuit and no deadline reads has just been freed out of the
        // zone by collapse_dead_clocks, so it is unbounded and meets the second
        // disjunct whatever the cycle does.  Recording its reset therefore
        // splits nodes that no acceptance test can tell apart.
        scratch32_.clear();
        for (ClockId c : n.just_reset)
            if (c < nc_ && (c >= live_scratch_.size() || live_scratch_[c]))
                scratch32_.push_back(c);
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

    // ── Dynamic component decomposition ─────────────────────────────────
    //
    // A node's goals, context and pursuits often fall into groups that mention
    // disjoint atoms.  Two such groups have disjoint formula-clocks as well,
    // since a clock belongs to the modality that owns it, and a node over their
    // union is realisable exactly when each group is (see doc_2, Theorem 1):
    // one direction projects the model onto a group's atoms, which the other
    // group's formulas never mention, and the other takes the product of the
    // two models, where delays synchronise, discrete edges interleave, and the
    // labellings union without conflict.
    //
    // Deciding the groups separately replaces a product of state spaces by
    // their sum.  A conjunction of k independent bounded eventualities has 2^k
    // combinations of which are still outstanding, and the undecomposed search
    // visits all of them.
    //
    // Two conditions have to hold, and the second is the one that is easy to
    // miss.  The atoms must be disjoint, and the *zone* must be a product of
    // its projections: a reset can leave a finite difference constraint
    // x - y < c between clocks of different groups, and then the groups are
    // coupled through time and may not be split.

    /// The atoms a formula mentions, as a bitmask over the input's atoms.
    ///
    /// The partition test compares every pair of a node's items, so the atom
    /// sets are compared once per pair per node.  As sets of strings that is
    /// three nested loops with a string compare at the bottom, and it cost
    /// about a third of the run on formulas that never split at all.  One bit
    /// per atom turns the whole test into a bitwise and.  Inputs with more
    /// atoms than a word simply do not decompose.
    std::uint64_t atoms_of(FormulaId id) const {
        // Formula ids are dense, so the memo is an array, not a map.  This is
        // read several times per item at every node whose shape is new, and a
        // red-black tree lookup per read was the last thing left in the cost of
        // asking a node that never decomposes whether it decomposes.
        const std::size_t k = static_cast<std::size_t>(id);
        if (k < atom_memo_.size() && atom_memo_ok_[k]) return atom_memo_[k];
        std::uint64_t out = 0;
        if (id != kInvalidId) {
            const FormulaNode& n = f_.node(id);
            if (n.kind == NodeKind::Atom || n.kind == NodeKind::IntVar) {
                auto ai = atom_bit_.find(n.atom_name);
                if (ai != atom_bit_.end()) out |= 1ull << ai->second;
            }
            for (int c = 0; c < 2; ++c)
                if (n.children[c] != kInvalidId) out |= atoms_of(n.children[c]);
        }
        if (k >= atom_memo_.size()) {
            atom_memo_.resize(k + 64, 0);
            atom_memo_ok_.resize(k + 64, 0);
        }
        atom_memo_[k] = out;
        atom_memo_ok_[k] = 1;
        return out;
    }

    /// Number the input's atoms, up to one word of them.
    void number_atoms(FormulaId root, FormulaFactory& f) {
        std::set<std::string> names;
        std::function<void(FormulaId)> walk = [&](FormulaId x) {
            if (x == kInvalidId) return;
            const FormulaNode& n = f.node(x);
            if (n.kind == NodeKind::Atom || n.kind == NodeKind::IntVar)
                names.insert(n.atom_name);
            walk(n.children[0]); walk(n.children[1]);
        };
        walk(root);
        if (names.size() > 64) { decomp_ = false; return; }
        std::size_t i = 0;
        for (const std::string& a : names) atom_bit_[a] = i++;
    }

    /// The formula-clocks of every timed modality inside a formula.
    const std::vector<ClockId>& clocks_of(FormulaId id) const {
        auto it = clock_memo_.find(id);
        if (it != clock_memo_.end()) return it->second;   // rarer: kept a map
        std::vector<ClockId> out;
        if (id != kInvalidId) {
            const FormulaNode& n = f_.node(id);
            const ClockId c = clock_of(cmap_, id);
            if (c != kNoClock) out.push_back(c);
            for (int k = 0; k < 2; ++k)
                if (n.children[k] != kInvalidId)
                    for (ClockId d : clocks_of(n.children[k])) out.push_back(d);
            std::sort(out.begin(), out.end());
            out.erase(std::unique(out.begin(), out.end()), out.end());
        }
        return clock_memo_.emplace(id, std::move(out)).first->second;
    }

    /// Split @p n into atom-disjoint components; empty if it does not split.
    std::vector<Node> components(const Node& n) const {
        // Items: the goals, the context entries, and the pursuits.  A pursuit
        // travels with the item that owns its modality.
        // The three working vectors are members, not locals: components() runs
        // once per node visit, and three heap allocations per node was most of
        // what the test cost on formulas that never decompose.
        std::vector<Item>& items = items_;
        items.clear();
        for (FormulaId id : n.Gamma.elements()) items.push_back({id, false});
        for (FormulaId id : n.X.elements())     items.push_back({id, true});
        std::vector<FormulaId>& pmu = pmu_;
        pmu.clear();
        for (const Pursuit& p : n.pursuits) pmu.push_back(p.mu);
        if (items.size() + pmu.size() < 2) return {};

        // Whether a node splits depends only on which formulas it carries, not
        // on its zone, so a shape that did not split never will.  Shapes repeat
        // heavily -- a nested tower has roughly half as many shapes as nodes --
        // and without this the union-find below runs again at each of them,
        // which is pure loss on any formula that never decomposes.
        // The signature is computed before the memo can be consulted, so it is
        // paid at every node, not only at new shapes.  Combining the ids
        // commutatively removes the sort the ordered version needed: each id is
        // mixed on its own and the mixes are xor-ed, which is O(m) and needs no
        // buffer.  A collision can only make two shapes look alike and so skip
        // a split that was available, which costs an optimisation and never a
        // verdict.
        std::uint64_t sig = 0;
        {
            auto mix = [](std::uint64_t x) {
                x += 0x9e3779b97f4a7c15ull;
                x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ull;
                x = (x ^ (x >> 27)) * 0x94d049bb133111ebull;
                return x ^ (x >> 31);
            };
            for (const Item& it : items) sig ^= mix(static_cast<std::uint64_t>(it.id));
            for (FormulaId mu : pmu)
                sig ^= mix(static_cast<std::uint64_t>(mu) | (1ull << 40));
            if (nosplit_.count(sig)) return {};
        }
        auto remember_nosplit = [&] { nosplit_.insert(sig); };

        std::vector<std::uint64_t>& at = at_;
        at.clear();
        at.reserve(items.size() + pmu.size());
        for (const Item& it : items) at.push_back(atoms_of(it.id));
        for (FormulaId mu : pmu)     at.push_back(atoms_of(mu));
        const std::size_t m = at.size();

        std::vector<std::size_t> up(m);
        for (std::size_t i = 0; i < m; ++i) up[i] = i;
        std::function<std::size_t(std::size_t)> find = [&](std::size_t x) {
            while (up[x] != x) { up[x] = up[up[x]]; x = up[x]; }
            return x;
        };
        // Union through an atom->item index rather than over item pairs.  Two
        // items are joined exactly when some atom occurs in both, so walking
        // each item's set bits and joining it to the first item seen carrying
        // that bit computes the same partition in O(m * atoms-per-item) instead
        // of O(m^2).  It matters because this runs at every node whose shape is
        // new, and on the formulas that never decompose -- one shared atom
        // across k conjuncts, or a chain of overlapping ones -- the quadratic
        // version was the whole cost of asking.
        std::array<std::size_t, 64> first_with;
        first_with.fill(m);
        std::size_t first_empty = m;
        for (std::size_t i = 0; i < m; ++i) {
            std::uint64_t bits = at[i];
            if (bits == 0) {                    // symbol-free items group together
                if (first_empty == m) first_empty = i;
                else up[find(i)] = find(first_empty);
                continue;
            }
            while (bits) {
                const int b = __builtin_ctzll(bits);
                bits &= bits - 1;
                if (first_with[b] == m) first_with[b] = i;
                else up[find(i)] = find(first_with[b]);
            }
        }
        std::map<std::size_t, std::vector<std::size_t>> grp;
        for (std::size_t i = 0; i < m; ++i) grp[find(i)].push_back(i);
        if (grp.size() < 2) { remember_nosplit(); return {}; }
        // A component that mentions no atom at all (a bare true or false) is not
        // worth splitting off: it decides nothing the enclosing node did not
        // already decide, and it is the degenerate case in which the split is
        // all cost.  Fold every such item into the first real component.
        {
            std::size_t host = grp.size();
            for (auto& kv : grp) {
                bool has_atom = false;
                for (std::size_t i : kv.second) if (at[i] != 0) has_atom = true;
                if (has_atom) { host = kv.first; break; }
            }
            if (host == grp.size()) { remember_nosplit(); return {}; }
            std::vector<std::size_t> orphans;
            for (auto it = grp.begin(); it != grp.end(); ) {
                bool has_atom = false;
                for (std::size_t i : it->second) if (at[i] != 0) has_atom = true;
                if (!has_atom) {
                    orphans.insert(orphans.end(), it->second.begin(), it->second.end());
                    it = grp.erase(it);
                } else ++it;
            }
            grp[host].insert(grp[host].end(), orphans.begin(), orphans.end());
            if (grp.size() < 2) { remember_nosplit(); return {}; }
        }

        // Clocks per group.  Ownership is read off the *formulas*, not only off
        // the live pursuits: a modality that is still a goal already owns its
        // formula-clock, and that clock may already carry a value from an
        // earlier launch.  Attributing it to no group at all would free it from
        // every component's zone, which loses the very constraint that
        // distinguishes one onset from another and reports SAT for a formula
        // that has none.
        std::vector<std::vector<unsigned char>> owns;
        for (auto& kv : grp) {
            std::vector<unsigned char> o(nc_, 0);
            for (std::size_t i : kv.second) {
                if (i >= items.size()) {
                    const ClockId c = n.pursuits[i - items.size()].x_mu;
                    if (c != kNoClock && c < nc_) o[c] = 1;
                } else {
                    for (ClockId c : clocks_of(items[i].id))
                        if (c < nc_) o[c] = 1;
                }
            }
            owns.push_back(std::move(o));
        }
        // Every clock must belong to exactly one group, or the split would
        // silently drop one.
        for (ClockId c = 1; c < nc_; ++c) {
            int cnt = 0;
            for (const auto& o : owns) cnt += o[c] ? 1 : 0;
            if (cnt > 1) return {};
            // Measured over every family of both suites, this second test never
            // fires: collapse_dead_clocks has already freed anything no pursuit
            // and no deadline reads, so a clock still constrained here is live
            // and therefore owned. It is kept as a guard, not as a heuristic.
            if (cnt == 0 && !n.Z.get_bound(c, kReferenceClock).is_infinity())
                return {};        // constrained but unowned: do not split
        }
        // No zone-product condition.  A cross-group difference constraint does
        // not have to be refused: component i is asked to be realisable over
        // the *projection* of Z onto its own clocks, and the two directions of
        // the theorem both survive.  Forwards, a valuation of the projection
        // extends to one of Z, and component i's formulas read only its own
        // clocks, so they hold of the restriction.  Backwards, Z is contained
        // in the intersection of the projections, so a product model realising
        // each component over its projection realises the node over Z a
        // fortiori.  The condition was sufficient, not necessary, and dropping
        // it is what lets a node split after a reset has related two groups'
        // clocks.  (Guarded, so it can be put back for an A/B run.)
        if (std::getenv("TCTL_ZONE_PRODUCT"))
            for (ClockId a = 1; a < nc_; ++a)
                for (ClockId b = 1; b < nc_; ++b) {
                    if (a == b) continue;
                    std::size_t ga = owns.size(), gb = owns.size();
                    for (std::size_t g = 0; g < owns.size(); ++g) {
                        if (owns[g][a]) ga = g;
                        if (owns[g][b]) gb = g;
                    }
                    if (ga == owns.size() || gb == owns.size() || ga == gb) continue;
                    if (!n.Z.get_bound(a, b).is_infinity()) return {};
                }

        std::vector<Node> out;
        std::size_t gi = 0;
        for (auto& kv : grp) {
            Node c;
            c.Z = n.Z; c.O = n.O; c.D = n.D; c.phase = n.phase;
            FormulaIdVec gam, ctx;
            for (std::size_t i : kv.second) {
                if (i < items.size()) {
                    (items[i].in_ctx ? ctx : gam).push_back(items[i].id);
                } else {
                    c.pursuits.push_back(n.pursuits[i - items.size()]);
                }
            }
            std::sort(gam.begin(), gam.end()); std::sort(ctx.begin(), ctx.end());
            c.Gamma = FormulaSet::from_sorted(gam);
            c.X     = FormulaSet::from_sorted(ctx);
            // Free the clocks this group does not own, and drop their deadlines:
            // they belong to the other groups and constrain nothing here.
            std::vector<unsigned char> dead(nc_, 0);
            bool any = false;
            for (ClockId cl = 1; cl < nc_; ++cl)
                if (!owns[gi][cl]) { dead[cl] = 1; any = true; }
            if (any && !c.Z.is_empty()) c.Z.free_many(dead);
            PooledVec<Deadline> keepD;
            for (const Deadline& d : c.D)
                if (d.x_mu < nc_ && owns[gi][d.x_mu]) keepD.push_back(d);
            c.D = keepD;
            out.push_back(std::move(c));
            ++gi;
        }
        return out;
    }

    /// Decide @p n by components, caching each.  Returns -1 if it does not split.
    int decide_by_components(const Node& n) {
        if (!decomp_ || decomp_depth_ > kMaxDecompDepth) return -1;
        std::vector<Node> cs = components(n);
        if (cs.empty()) return -1;
        if (debug_) {
            std::ostringstream os;
            os << "SPLIT " << cs.size() << " comps from G{";
            for (FormulaId id : n.Gamma.elements()) os << f_.to_string(id) << ',';
            os << "} X{";
            for (FormulaId id : n.X.elements()) os << f_.to_string(id) << ',';
            os << "} P{";
            for (const Pursuit& q : n.pursuits) os << f_.to_string(q.mu) << ',';
            os << "}\n";
            for (const Node& c : cs) {
                os << "   comp G{";
                for (FormulaId id : c.Gamma.elements()) os << f_.to_string(id) << ',';
                os << "} X{";
                for (FormulaId id : c.X.elements()) os << f_.to_string(id) << ',';
                os << "} P{";
                for (const Pursuit& q : c.pursuits) os << f_.to_string(q.mu) << ',';
                os << "}\n";
            }
            std::fputs(os.str().c_str(), stderr);
        }
        for (Node& c : cs) {
            Key k; Zone ez;
            acc_key(c, k, ez);
            auto it = decomp_cache_->find(k);
            bool ok;
            if (it != decomp_cache_->end()) {
                ok = it->second;
            } else {
                Engine sub(f_, root_formula_, 0.0, false);
                sub.decomp_depth_ = decomp_depth_ + 1;
                sub.decomp_cache_ = decomp_cache_;
                sub.decomp_ = decomp_;
                ok = sub.decide_scc(c);
                sub_nodes_ += sub.nodes();
                decomp_cache_->emplace(std::move(k), ok);
            }
            if (!ok) return 0;
        }
        return 1;
    }

    std::uint32_t intern(Node&& n) {
        // The key is built into a member buffer, not a fresh vector: intern runs
        // once per child of every expansion and the key is a few hundred words,
        // so a local would be a malloc/free pair per call on the hottest path.
        // Only a miss moves it into the table, and the buffer is then re-grown
        // on the next call rather than reused.
        Key& k = intern_key_;
        k.clear();
        Zone ez;
        subsume_goals(n);
        collapse_dead_clocks(n);
        acc_key(n, k, ez);
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

        std::uint64_t* unb = unb_of(id);
        for (ClockId c = 1; c < nc_; ++c)
            if (ez.get_bound(c, kReferenceClock).is_infinity()) set_bit(unb, c);

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
            dtrace(v, "CLOSED", n, -1);
            g_[v].kind = Expansion::Kind::Closed;
            return true;
        }
        Expansion e = expand(n);
        dtrace(v, e.kind == Expansion::Kind::And ? "AND" : "OR", n, -1);
        // intern() may reallocate g_, so collect the ids before touching g_[v].
        std::vector<std::uint32_t> kids;
        kids.reserve(e.children.size());
        for (Node& c : e.children) kids.push_back(intern(std::move(c)));
        if (debug_) {                       // temporary: edge dump for figures
            std::ostringstream os;
            os << "EDGE " << v << " ["
               << (e.kind == Expansion::Kind::And ? "AND" : "OR") << "]";
            for (std::uint32_t k : kids) os << ' ' << k;
            os << '\n';
            std::fputs(os.str().c_str(), stderr);
        }
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
            if (debug_) {
                std::ostringstream os;
                os << "VAL " << S[i] << '=' << (alive[i] ? 1 : 0) << '\n';
                std::fputs(os.str().c_str(), stderr);
            }
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

        // A node whose residual splits into atom-disjoint components is decided
        // by deciding them, and never expanded: its verdict is the conjunction
        // of theirs.  It becomes a settled leaf of this search, exactly like a
        // node whose SCC has already closed.
        auto try_split = [&](std::uint32_t v) {
            if (!decomp_ || !g_[v].n) return false;
            const int r = decide_by_components(*g_[v].n);
            if (r < 0) return false;
            g_[v].visited = true;
            g_[v].done = true;
            g_[v].val = r != 0;
            g_[v].kind = Expansion::Kind::Closed;
            g_[v].n.reset();
            return true;
        };

        auto visit = [&](std::uint32_t v) {
            g_[v].visited = true;
            g_[v].onstack = true;
            g_[v].index = g_[v].low = counter++;
            tstack.push_back(v);
            return expand_node(v);
        };

        if (!try_split(r)) {
            if (!visit(r)) return false;
            st.push_back({r, 0});
        } else {
            return g_[r].val;
        }

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
            // A witness needs the alternatives.  The schedule picks, at an (OR)
            // node, the child that moves towards stopping the pursuit it is
            // serving, and it can only pick among children the search evaluated;
            // short-circuiting leaves the stop branch unvisited and hence
            // unmarked, so the schedule would have nothing to choose but the
            // deferral.  The verdict is unaffected either way.
            if (keep_graph_) return false;
            if (!g_[child].done) return false;
            return (g_[parent].kind == Expansion::Kind::And) ? !g_[child].val
                                                             : g_[child].val;
        };

        while (!st.empty()) {
            const std::uint32_t v = st.back().v;
            if (st.back().ci < g_[v].ch.size()) {
                const std::uint32_t w = g_[v].ch[st.back().ci++];
                if (!g_[w].visited) {
                    if (!try_split(w)) {
                        if (!visit(w)) return false;
                        st.push_back({w, 0});
                    }
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


    FormulaFactory& f_;
    bool keep_graph_ = false;    ///< retain children/untils for witness extraction
    /// Per-pursuit distance to a stop, built by the witness extractor.
    std::unordered_map<FormulaId, std::vector<std::uint32_t>> wdist_;
    /// Distance to the next saturated node, the schedule's divergence metric.
    std::vector<std::uint32_t> sdist_;
    /// The interned zone pool and the raw-matrix cache in front of it.
    static constexpr std::size_t kZoneCacheSlots = 1u << 12;   // 4k lines, ~5 MB
    struct ZoneCacheLine { std::uint32_t id = kNoRegion; std::vector<raw_t> raw; };
    mutable std::vector<std::vector<std::uint32_t>> zpool_;
    mutable std::unordered_map<std::string, std::uint32_t> zids_;
    mutable std::vector<ZoneCacheLine> zcache_{kZoneCacheSlots};
    /// Drop goals implied by other goals (releases' psi, implied disjunctions).
    bool subsume_goals_ = std::getenv("TCTL_SUBSUME_GOALS") != nullptr;
    mutable FormulaIdVec implied_;
    // Component decomposition.
    static constexpr int kMaxDecompDepth = 12;
    bool decomp_ = std::getenv("TCTL_COMPONENTS") != nullptr;
    int decomp_depth_ = 0;
    std::uint64_t sub_nodes_ = 0;
    FormulaId root_formula_ = kInvalidId;
    std::shared_ptr<std::unordered_map<Key, bool, KeyHash>> decomp_cache_ =
        std::make_shared<std::unordered_map<Key, bool, KeyHash>>();
    mutable std::vector<std::uint64_t> atom_memo_;
    mutable std::vector<unsigned char> atom_memo_ok_;
    std::map<std::string, std::size_t> atom_bit_;
    mutable std::map<FormulaId, std::vector<ClockId>> clock_memo_;
    struct Item { FormulaId id; bool in_ctx; };
    mutable std::vector<Item> items_;
    mutable std::vector<FormulaId> pmu_;
    mutable std::vector<std::uint64_t> at_;
    mutable std::vector<FormulaId> sigbuf_;
    mutable std::unordered_set<std::uint64_t> nosplit_;
    /// Treat AG psi as a context formula rather than a release pursuit.
    /// TCTL_AG_CONTEXT=all   every AG;
    ///                =top   only AGs not nested under another modality.
    /// The two differ because the encoding trades a live pursuit for context
    /// churn: side-by-side AGs each shed a pursuit and win, while an AG nested
    /// inside another modality is re-demanded through the context at every
    /// successor and loses.  Which effect dominates is a property of where the
    /// AG sits, so it is decided per modality, statically.
    int ag_mode_ = ag_mode_from_env();
    static int ag_mode_from_env() {
        const char* v = std::getenv("TCTL_AG_CONTEXT");
        if (!v) return 0;
        if (std::strcmp(v, "top") == 0) return 2;
        if (std::strcmp(v, "smart") == 0) return 3;
        return 1;
    }
    std::set<FormulaId> ag_top_;      ///< AGs under no other modality
    std::set<FormulaId> ag_free_;     ///< AGs under no *until* modality
    bool ag_context_for(FormulaId mu) const {
        if (ag_mode_ == 0) return false;
        if (ag_mode_ == 1) return true;
        if (ag_mode_ == 2) return ag_top_.count(mu) != 0;
        return ag_free_.count(mu) != 0;
    }
    void collect_top_ags(FormulaId root, FormulaFactory& f) {
        std::function<void(FormulaId, bool)> walk = [&](FormulaId x, bool under) {
            if (x == kInvalidId) return;
            const FormulaNode& n = f.node(x);
            const bool modal = is_modality(n.kind);
            if (modal && !under) ag_top_.insert(x);
            walk(n.children[0], under || modal);
            walk(n.children[1], under || modal);
        };
        walk(root, false);
        // The regression the "all" mode shows on towers comes from an AG that
        // sits inside an *until*: that until is re-launched at every onset, and
        // re-demanding the AG through the context at each one churns more than
        // the single pursuit record it replaced.  An AG under other AGs has no
        // such onsets above it and keeps the win, so the test is on enclosing
        // untils rather than on enclosing modalities.
        std::function<void(FormulaId, bool)> walk2 = [&](FormulaId x, bool underU) {
            if (x == kInvalidId) return;
            const FormulaNode& n = f.node(x);
            const bool modal = is_modality(n.kind);
            if (modal && !underU) ag_free_.insert(x);
            const bool u = underU || (modal && is_until_modality(n.kind));
            walk2(n.children[0], u);
            walk2(n.children[1], u);
        };
        walk2(root, false);
    }
    mutable std::vector<unsigned char> dead_scratch_;
    /// Scratch for intern()'s key, to keep the hot path allocation-free.
    Key intern_key_;

    ClockMap cmap_;
    std::size_t nc_ = 1;
    std::vector<std::int32_t> max_;
    std::vector<std::int32_t> bounds_;   // sorted formula interval endpoints (+0)
    // per clock: the endpoints of its own modality's window — the only values at
    // which a guard on that clock can flip, hence the (Delay) cell boundaries
    std::vector<std::vector<std::int32_t>> clock_bounds_;

    // full node key → verdict; the match is exact by construction
    SatCache sx_cache_;                  // persistent S_X(mu,X) memo
    std::uint64_t expansions_ = 0;
    bool budget_hit_ = false;
    bool has_deadline_ = false;
    bool debug_ = false;
    std::uint32_t root_id_ = static_cast<std::uint32_t>(-1);
    std::chrono::steady_clock::time_point deadline_{};

    // ── SCC acceptance state (unused under TCTL_LEGACY_LOOP) ────────────
    std::vector<GNode>                             g_;     // the explored graph
    std::unordered_map<Key, std::uint32_t, KeyHash> gid_;  // acc_key → node id
    std::vector<const Key*> key_of_;                       // node id → its key
    std::size_t words_ = 1;                                // clock-bitmap width
    // key-building scratch, reused so the hot path allocates nothing
    mutable std::vector<std::array<std::uint32_t, 7>> pursuit_scratch_;
    mutable std::vector<std::array<std::uint32_t, 4>> deadline_scratch_;
    mutable std::vector<std::uint32_t> scratch32_;
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

// ── Conjunctive decomposition ───────────────────────────────────────────────
//
// Split a top-level conjunction into groups of conjuncts that share atoms.  Two
// groups mention disjoint atoms, hence disjoint formula-clocks, and a node over
// their union is realisable exactly when each group is.
//
// One direction projects a model onto a group's atoms, which the other group's
// formulas do not mention.  The other takes the product of the two models:
// delays synchronise, discrete edges interleave, and the labellings union
// without conflict because the atoms are disjoint.  An E-goal of one group is
// witnessed by lifting its own run against any run of the other, and an A-goal
// holds because every run of the product projects to a run of the group's own
// model.  Both models being non-blocking, so is the product.
//
// Without this the search enumerates the product of the groups' states: a
// conjunction of k independent bounded eventualities has 2^k combinations of
// which are still outstanding, and the tableau visits all of them.
static void split_conjuncts(FormulaId f, const FormulaFactory& fac,
                            std::vector<FormulaId>& out) {
    const FormulaNode& n = fac.node(f);
    if (n.kind == NodeKind::And) {
        split_conjuncts(n.children[0], fac, out);
        split_conjuncts(n.children[1], fac, out);
    } else {
        out.push_back(f);
    }
}

// The symbols two conjuncts can share.  Atomic propositions are the obvious
// ones, but a data variable couples its constraints just as tightly: {x > 3}
// and {x < 2} mention no proposition at all, and treating them as independent
// makes an unsatisfiable conjunction satisfiable, one group at a time.
static void atoms_of(FormulaId f, const FormulaFactory& fac,
                     std::set<std::string>& out) {
    if (f == kInvalidId) return;
    const FormulaNode& n = fac.node(f);
    if (n.kind == NodeKind::Atom || n.kind == NodeKind::IntVar)
        out.insert(n.atom_name);
    atoms_of(n.children[0], fac, out);
    atoms_of(n.children[1], fac, out);
}

/// Groups of conjuncts closed under sharing an atom; empty if there is only one.
static std::vector<std::vector<FormulaId>>
decompose(FormulaId f, const FormulaFactory& fac) {
    std::vector<FormulaId> parts;
    split_conjuncts(f, fac, parts);
    if (parts.size() < 2) return {};

    std::vector<std::set<std::string>> at(parts.size());
    for (std::size_t i = 0; i < parts.size(); ++i) atoms_of(parts[i], fac, at[i]);

    std::vector<std::size_t> up(parts.size());
    for (std::size_t i = 0; i < up.size(); ++i) up[i] = i;
    std::function<std::size_t(std::size_t)> find = [&](std::size_t x) {
        while (up[x] != x) { up[x] = up[up[x]]; x = up[x]; }
        return x;
    };
    for (std::size_t i = 0; i < parts.size(); ++i)
        for (std::size_t j = i + 1; j < parts.size(); ++j) {
            bool share = false;
            for (const std::string& a : at[i])
                if (at[j].count(a)) { share = true; break; }
            if (share) up[find(i)] = find(j);
        }

    // A conjunct mentioning no symbol at all (a bare constant, or a constraint
    // over nothing) is folded into the first real group rather than split off.
    std::size_t host = parts.size();
    for (std::size_t i = 0; i < parts.size(); ++i)
        if (!at[i].empty()) { host = find(i); break; }
    if (host == parts.size()) return {};
    for (std::size_t i = 0; i < parts.size(); ++i)
        if (at[i].empty()) up[find(i)] = host;

    std::map<std::size_t, std::vector<FormulaId>> groups;
    for (std::size_t i = 0; i < parts.size(); ++i) groups[find(i)].push_back(parts[i]);
    if (groups.size() < 2) return {};
    std::vector<std::vector<FormulaId>> out;
    for (auto& kv : groups) out.push_back(std::move(kv.second));
    return out;
}

Result Tableau::check(FormulaId normalized_formula) {
    stats_.reset();
    const auto t0 = std::chrono::steady_clock::now();

    // Decomposition changes what a witness would be (the product of the groups'
    // automata), so it is skipped when one is wanted.
    // Decomposition changes what a witness is (the product of the components'
    // automata) and the extractor does not build products, so both forms stand
    // down when one is asked for.
    const bool v2 = version_ == Version::V2 && !extract_witness_;
    const bool split_root = (decompose_ || v2) && !extract_witness_;
    if (split_root) {
        const auto groups = decompose(normalized_formula, factory_);
        if (!groups.empty()) {
            std::uint64_t total = 0;
            bool timeout = false;
            for (const auto& g : groups) {
                FormulaId conj = g[0];
                for (std::size_t i = 1; i < g.size(); ++i)
                    conj = factory_.make_and(conj, g[i]);
                Engine sub(factory_, conj,
                           static_cast<double>(timeout_.count()), false);
                sub.apply_version(v2);
                const bool ok = sub.decide(conj);
                total += sub.nodes();
                if (sub.budget_hit()) { timeout = true; break; }
                if (!ok) {                       // one group fails, all fails
                    stats_.nodes_created = total;
                    const auto te = std::chrono::steady_clock::now();
                    return Result(Result::Value::Unsatisfiable,
                                  std::chrono::duration<double>(te - t0).count());
                }
            }
            stats_.nodes_created = total;
            has_witness_ = false;
            const auto te = std::chrono::steady_clock::now();
            return Result(timeout ? Result::Value::Timeout
                                  : Result::Value::Satisfiable,
                          std::chrono::duration<double>(te - t0).count());
        }
    }

    Engine engine(factory_, normalized_formula,
                  static_cast<double>(timeout_.count()), extract_witness_);
    engine.apply_version(v2);
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
