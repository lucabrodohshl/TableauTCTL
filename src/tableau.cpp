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
#include <cstring>
#include <deque>
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
                        const std::map<FormulaId, ClockId>& ymap,
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
    // A re-demand is folded into the running pursuit exactly when the modality
    // is universal.  Every run must comply with every onset, so one pursuit can
    // serve them all.  An existential modality is never absorbed: distinct
    // onsets may be witnessed by distinct runs, so a recurring demand launches a
    // fresh pursuit on the launch branch while the running one rides the
    // discharge branch, and the launch drops the deferred pursuits so only one
    // is ever live per modality.
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
        if (p.mu == mu && is_universal(mk0)) {
            CoverResult only;
            only.kind = CoverResult::Kind::Cover;
            Node discharge;
            discharge.Gamma = gamma_without(n.Gamma, mu);
            discharge.X = n.X; discharge.Z = n.Z;
            discharge.D = n.D; discharge.pursuits = n.pursuits; discharge.inv = n.inv;
            discharge.interval_witness = n.interval_witness;
            // This demand is the newest onset the pursuit owes an answer to.
            if (p.y_mu != kNoClock) {
                discharge.Z.reset(p.y_mu);
                discharge.just_reset.push_back(p.y_mu);
            }
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
            if (clock_of(cmap, mu) != kNoClock) {
                for (Pursuit& q : discharge.pursuits) {
                    if (q.mu != mu) continue;
                    if (is_until_modality(mk0)) {
                        // A recurrence, not a deadline: witnesses at most
                        // sup I - inf I apart answer every onset carried in.
                        if (!rw.hi_inf) q.persistent = true;
                    } else {
                        // A release merges exactly: while nothing has released
                        // it, the onsets in [t0,t] demand psi over the union of
                        // their windows, which is [t0 + inf I, inf).
                        q.persistent = true;
                    }
                }
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
            ctxc.Z = n.Z; ctxc.D = n.D;
            ctxc.pursuits = n.pursuits; ctxc.inv = n.inv;
            ctxc.interval_witness = n.interval_witness;
            only.children.push_back(std::move(ctxc));
            return only;
        }
    }

    const ClockId x_mu = clock_of(cmap, mu);    // kNoClock if mu is untimed
    const ClockId y_mu = clock_of(ymap, mu);    // kNoClock unless mu is universal

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
    base.X = n.X; base.Z = n.Z; base.D = n.D;
    base.pursuits = n.pursuits; base.inv = n.inv;
    base.interval_witness = n.interval_witness;

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
            // The launch is itself an onset, so y_mu starts here too.
            if (y_mu != kNoClock) {
                launch.Z.reset(y_mu);
                launch.just_reset.push_back(y_mu);
            }
        }
        // A release launched at an *interval witness* (the abutting stop of
        // §4.2, whose zone is a crossing with extent rather than an instant)
        // whose window opens at 0 bans within the very crossing that asserts
        // it: a position later in the cell lies inside the window of one
        // earlier in it.  So its body is asserted here rather than deferred.
        // A window opening at 1 or later acts only beyond the cell and defers
        // as usual.
        // Strictness at 0 makes no difference: what matters is that the window
        // contains arbitrarily small positive offsets, so a position later in
        // the crossing lies inside the window of one earlier in it.  A ban like
        // AG(0,1] !q therefore bans within the cell that asserts q, which is
        // what closes the abutting child on a rate contradiction.
        if (n.interval_witness && !until_kind) {
            const Window lw = window_of(mu, f);
            if (lw.lo == 0) launch.Gamma.insert(f.node(mu).children[1]);
        }

        Pursuit p; p.mu = mu; p.x_mu = x_mu; p.y_mu = y_mu;
        p.stage = Pursuit::Stage::Here;
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
        // y_mu numbers after every x_mu, so a clock index still identifies its
        // map by range and the two never collide.
        ymap_ = assign_onset_clocks(root, f,
                                    static_cast<ClockId>(1 + cmap_.size()));
        nc_ = 1 + cmap_.size() + ymap_.size();
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
        // An onset clock is tested only against its own modality's endpoints:
        // y_mu >= inf I lets a persistent until stop, y_mu > sup I lets a
        // persistent release lapse.  Those two are its cut points and sup I its
        // maximum, so it is as flat in M as x_mu is.
        for (const auto& [mu, y] : ymap_) {
            const FormulaNode& mn = f.node(mu);
            clock_bounds_[y].push_back(
                static_cast<std::int32_t>(mn.time_lower.value));
            if (!mn.time_upper.is_infinity)
                clock_bounds_[y].push_back(
                    static_cast<std::int32_t>(mn.time_upper.value));
            std::sort(clock_bounds_[y].begin(), clock_bounds_[y].end());
            clock_bounds_[y].erase(
                std::unique(clock_bounds_[y].begin(), clock_bounds_[y].end()),
                clock_bounds_[y].end());
        }
        for (ClockId c = 1; c < nc_; ++c)
            max_[c] = clock_bounds_[c].empty() ? 0 : clock_bounds_[c].back();
        add_onset_shifts(root, f);
        collect_top_ags(root, f);
        number_atoms(root, f);
        debug_ = std::getenv("TCTL_DEBUG") != nullptr;
        words_ = (nc_ + 63) / 64;
        rw32_  = (nc_ + 31) / 32;
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
        struct Mod { FormulaId id; std::int32_t a, b; bool binf; bool rel; };
        std::vector<Mod> mods;
        std::function<void(FormulaId)> walk = [&](FormulaId x) {
            if (x == kInvalidId) return;
            const FormulaNode& n = f.node(x);
            if (is_timed(n.kind))
                mods.push_back({x, static_cast<std::int32_t>(n.time_lower.value),
                                n.time_upper.is_infinity ? 0
                                    : static_cast<std::int32_t>(n.time_upper.value),
                                n.time_upper.is_infinity,
                                !is_until_modality(n.kind)});
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
            auto cut = [&](std::int32_t v) {
                if (v > 0 && v < max_[ec]) bs.push_back(v);
            };
            for (const Mod& mu : mods) {
                if (mu.id == rho.id) continue;
                // Which shifts isolate the doomed onsets depends on what the
                // demanded modality owes.  An until needs one witness inside
                // its window, so it is doomed only where the window is wholly
                // *contained* in the ban: t in [c-a, d-b].  A release obliges
                // its body at *every* position of its window, so a single
                // banned instant suffices and it is doomed wherever the window
                // merely *overlaps* the ban: t in [c-b, d-a].  Cutting with the
                // wrong family leaves the doomed onsets inside a cell that also
                // holds servable ones -- on AG(EG[2,4] p) & AG[6,7] !p, whose
                // onsets in [2,5] are all doomed, the containment shifts cut
                // that clock at 3 and 4 and never at 2 or 5, and it came back
                // SAT.  Two cuts per pair either way, so the count, and with it
                // M-independence, is unchanged.
                cut(rho.a - mu.a);
                if (!rho.binf && !mu.binf) cut(rho.b - mu.b);
                // A release is doomed where its window merely *overlaps* the
                // ban, t in [c-b, d-a], not where it is contained in it -- it
                // obliges its body at every position, so one banned instant
                // suffices.  Adding those two cuts (rho.a-mu.b, rho.b-mu.a when
                // mu is a release) does isolate the doomed onsets of
                // AG(EG[2,4] p) & AG[6,7] !p at 2 and 5, but measured it does
                // not change that verdict and it costs the M-independence of
                // the constant-free family, so the laundering there is not the
                // cell granularity.  Left out; see the note in tableau.hpp.
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
        n.inv = Inv::Unset;
        return decide_scc(n);
    }

    std::uint64_t nodes() const { return expansions_ + sub_nodes_; }
    std::uint64_t straddles() const { return straddle_; }
    bool budget_hit() const { return budget_hit_; }

    /// Witness automaton for the marking of the last successful decide().
    /// Only meaningful when SCC acceptance ran and the verdict was SAT.
    TimedAutomaton witness() { return extract_witness(root_id_); }

    /// Turn the optional optimisations on or off as a set.  Environment
    /// variables still act as per-feature overrides, so a single optimisation
    /// can be isolated for a measurement without rebuilding.
    void apply_version(bool v2) {
        // This branch is v1.  The optional optimisations stay off whatever the
        // caller or the environment asks for; v2 lives on the 'v2' branch.
        (void)v2;
        decomp_ = false;
        subsume_goals_ = false;
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

    static std::uint64_t key_hash(const std::uint32_t* p, std::size_t n) {
        std::uint64_t h = 1469598103934665603ull;
        for (std::size_t i = 0; i < n; ++i) { h ^= p[i]; h *= 1099511628211ull; }
        return h;
    }
    /// The stored key of @p v.  Invalidated by the next intern(), so read it
    /// out before interning anything else.
    const std::uint32_t* key_at(std::uint32_t v) const {
        const std::uint32_t off = koff_[v];
        return kblocks_[off >> kBlkShift].get() + (off & kBlkMask);
    }
    /// Copy @p n words into the arena and return their global offset.  A key is
    /// never split across blocks, so key_at() can hand back a plain pointer and
    /// klookup() can memcmp against it.
    std::uint32_t karena_put(const std::uint32_t* p, std::uint32_t n) {
        if (kfill_ + n > kBlkWords) {
            const std::uint32_t need = n > kBlkWords ? n : kBlkWords;
            kblocks_.push_back(std::make_unique<std::uint32_t[]>(need));
            kfill_ = 0;
        }
        const auto blk = static_cast<std::uint32_t>(kblocks_.size() - 1);
        const std::uint32_t off = (blk << kBlkShift) | kfill_;
        std::memcpy(kblocks_.back().get() + kfill_, p, n * sizeof(std::uint32_t));
        kfill_ += n;
        return off;
    }
    void ktab_grow() {
        const std::size_t ns = ktab_.empty() ? 1024 : ktab_.size() * 2;
        std::vector<std::uint32_t> t(ns, 0);
        const std::size_t mask = ns - 1;
        for (std::uint32_t e : ktab_) {
            if (!e) continue;
            std::size_t s = static_cast<std::size_t>(khash_[e - 1]) & mask;
            while (t[s]) s = (s + 1) & mask;
            t[s] = e;
        }
        ktab_.swap(t);
        kmask_ = mask;
    }
    /// Find the key @p p, or report where to put it.  Linear probing: the table
    /// holds node ids, so a probe is one contiguous read, and the payload lives
    /// in the arena rather than behind a pointer per entry.
    std::uint32_t klookup(const std::uint32_t* p, std::size_t n,
                          std::uint64_t h, std::size_t& slot) {
        if (ktab_.empty()) ktab_grow();
        slot = static_cast<std::size_t>(h) & kmask_;
        while (ktab_[slot]) {
            const std::uint32_t id = ktab_[slot] - 1;
            if (khash_[id] == h && klen_[id] == n &&
                std::memcmp(key_at(id), p, n * sizeof(std::uint32_t)) == 0)
                return id;
            slot = (slot + 1) & kmask_;
        }
        return kNoRegion;
    }

    // A pursuit costs three key words rather than eight: the modality, its two
    // clocks packed 16:16 (kNoClock as 0xFFFF, so no real clock id collides),
    // and its flags as a bitfield.  The key is built once per interned node and
    // stored for the life of the search, so its width is the dominant
    // per-node memory cost.  Packing preserves injectivity, so sorting the
    // packed tuples still yields one canonical encoding per set.
    /// Both clocks and all five flags of a pursuit in one word: 12 bits each
    /// for x_mu and y_mu (0xFFF standing for kNoClock, which no real clock id
    /// can reach -- the tableau uses at most 2n+1 of them) and five flag bits.
    static std::uint32_t pack_pursuit(const Pursuit& p) {
        const std::uint32_t xs = (p.x_mu == kNoClock) ? 0xFFFu : (p.x_mu & 0xFFFu);
        const std::uint32_t ys = (p.y_mu == kNoClock) ? 0xFFFu : (p.y_mu & 0xFFFu);
        return (xs << 20) | (ys << 8) |
               static_cast<std::uint32_t>(p.stage) |
               (static_cast<std::uint32_t>(p.is_until)   << 2) |
               (static_cast<std::uint32_t>(p.persistent) << 3) |
               (static_cast<std::uint32_t>(p.rolled)     << 4);
    }
    static void unpack_pursuit(std::uint32_t w, Pursuit& p) {
        const std::uint32_t xs = (w >> 20) & 0xFFFu, ys = (w >> 8) & 0xFFFu;
        p.x_mu       = (xs == 0xFFFu) ? kNoClock : static_cast<ClockId>(xs);
        p.y_mu       = (ys == 0xFFFu) ? kNoClock : static_cast<ClockId>(ys);
        p.stage      = static_cast<Pursuit::Stage>(w & 3u);
        p.is_until   = ((w >> 2) & 1u) != 0;
        p.persistent = ((w >> 3) & 1u) != 0;
        p.rolled     = ((w >> 4) & 1u) != 0;
    }

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
                                        pack_pursuit(p)});
        std::sort(pursuit_scratch_.begin(), pursuit_scratch_.end());
        put(k, static_cast<std::uint32_t>(pursuit_scratch_.size()));
        for (const auto& t : pursuit_scratch_)
            for (std::uint32_t w : t) put(k, w);

        deadline_scratch_.clear();
        for (const Deadline& d : n.D)
            deadline_scratch_.push_back(
                {(static_cast<std::uint32_t>(d.x_mu) << 1) |
                     static_cast<std::uint32_t>(d.strict),
                 static_cast<std::uint32_t>(static_cast<std::int32_t>(d.bound))});
        std::sort(deadline_scratch_.begin(), deadline_scratch_.end());
        put(k, static_cast<std::uint32_t>(deadline_scratch_.size()));
        for (const auto& t : deadline_scratch_)
            for (std::uint32_t w : t) put(k, w);

        put(k, static_cast<std::uint32_t>(n.inv) |
               (static_cast<std::uint32_t>(n.interval_witness) << 4) |
               (static_cast<std::uint32_t>(n.delayed_here) << 5));
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
            for (std::uint32_t c : ch_of(v))
                if (g_[c].val) { out.push_back(c); break; }   // one suffices
        } else {
            for (std::uint32_t c : ch_of(v))
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
            const Span u = us_of(v);
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
                for (std::uint32_t c : ch_of(v))
                    if (c != v && g_[c].val && g_[c].discharges == mu) { nd = 0; break; }
                if (nd != 0) {
                    const bool orn = g_[v].kind == Expansion::Kind::Or;
                    bool any = false;
                    std::uint32_t acc = orn ? kFar : 0;
                    for (std::uint32_t c : ch_of(v)) {
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
        std::vector<FormulaId> u(us_of(v).begin(), us_of(v).end());
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
            for (std::uint32_t c : ch_of(v)) if (c != v && g_[c].val) other = true;
            std::uint32_t best = kNoRegion, bestd = kFar;
            for (std::uint32_t c : ch_of(v)) {
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
            for (std::uint32_t c : ch_of(v))
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
                is_saturated(decode_node(v))) d[v] = 0;
        for (bool changed = true; changed;) {
            changed = false;
            for (std::uint32_t v = 0; v < m; ++v) {
                if (!g_[v].done || !g_[v].val || d[v] == 0) continue;
                const bool orn = g_[v].kind == Expansion::Kind::Or;
                bool any = false;
                std::uint32_t acc = orn ? kFar : 0;
                for (std::uint32_t c : ch_of(v)) {
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
                for (FormulaId mu : us_of(v))
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

                const Node n = decode_node(v);
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
                    for (std::uint32_t c : ch_of(v)) {
                        if (!g_[c].val) continue;
                        Node cn = decode_node(c);
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
                const Node n = decode_node(v);
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
            const Node tgt = decode_node(heads[to].first);
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
                for (ClockId c : decode_node(v).just_reset)
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
    /// Rebuild the node @p v from its stored key.
    Node decode_node(std::uint32_t v) const {
        return decode_key(key_at(v), klen_[v]);
    }
    Node decode_key(const std::uint32_t* k, std::size_t klen) const {
        Node n;
        std::size_t i = 0;
        n.Gamma     = FormulaSet::from_handle(k[i++]);
        n.X         = FormulaSet::from_handle(k[i++]);

        const std::uint32_t np = k[i++];
        for (std::uint32_t t = 0; t < np; ++t) {
            Pursuit p;
            p.mu = static_cast<FormulaId>(k[i++]);
            unpack_pursuit(k[i++], p);
            n.pursuits.push_back(p);
        }

        const std::uint32_t nd = k[i++];
        for (std::uint32_t t = 0; t < nd; ++t) {
            Deadline dl;
            const std::uint32_t w = k[i++];
            dl.x_mu   = static_cast<ClockId>(w >> 1);
            dl.strict = (w & 1u) != 0;
            dl.bound  = static_cast<std::int64_t>(static_cast<std::int32_t>(k[i++]));
            n.D.push_back(dl);
        }

        const std::uint32_t iw = k[i++];
        n.inv = static_cast<Inv>(iw & 0xFu);
        n.interval_witness = ((iw >> 4) & 1u) != 0;
        n.delayed_here     = ((iw >> 5) & 1u) != 0;

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
        if (i < klen) {
            for (std::size_t w = 0; w < rw32_; ++w) {
                std::uint32_t bits = k[i++];
                while (bits) {
                    const std::uint32_t b = static_cast<std::uint32_t>(
                        __builtin_ctz(bits));
                    n.just_reset.push_back(
                        static_cast<ClockId>(w * 32 + b));
                    bits &= bits - 1;
                }
            }
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
        for (const Pursuit& p : n.pursuits) {
            if (p.x_mu != kNoClock && p.x_mu < nc_) live_scratch_[p.x_mu] = 1;
            // The onset clock is read as much as the window clock, but only
            // once the pursuit is *persistent*: (Ustopdrop) ends a recurrence
            // on y_mu >= a ∧ y_mu > 0, and a persistent release lapses on
            // y_mu > b.  Freeing it outright left both guards testing an
            // unconstrained clock, which no zone entails, so no recurrence
            // could ever end.  Keeping it always is the other extreme: an
            // ordinary pursuit never reads y_mu, and (Abs) *resets* it at the
            // very step that makes the pursuit persistent, so whatever it held
            // before is discarded anyway.  Carrying it regardless only splits
            // zones on a value no rule looks at -- and zone variety, not goal
            // variety, is what the graph size is made of.
            // ... and only where some rule can actually read it: (Ustopdrop)
            // for an until, the persistent (Rlapse) for a release with a finite
            // window.  An *unbounded* persistent release -- an untimed AG, the
            // commonest pursuit there is -- never lapses on y_mu and never
            // stops, so its onset clock is pure zone-splitting: it carries a
            // value no guard reads, and every distinct value it takes is a
            // distinct zone and hence a distinct node.
            if (p.persistent && p.y_mu != kNoClock && p.y_mu < nc_ &&
                (p.is_until || !window_of(p.mu, f_).hi_inf))
                live_scratch_[p.y_mu] = 1;
        }
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
        // A persistent release runs to infinity from its first onset: the
        // windows of the onsets absorbed into it union to [inf I, inf).
        if (p.persistent && !p.is_until) { w.hi_inf = true; w.hi_strict = false; return w; }
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
            os << f_.to_string(p.mu) << "/s" << int(p.stage)
               << (p.is_until ? "U" : "R")
               << (p.persistent ? "*" : "") << (p.rolled ? "@" : "")
               << "/x" << int(p.x_mu) << "/y" << int(p.y_mu) << ' ';
        os << "} inv" << int(n.inv) << " Z=" << n.Z.to_string() << '\n';
        std::fputs(os.str().c_str(), stderr);
    }

    // ── Expansion (single rule) ─────────────────────────────────────────
    Expansion expand(const Node& n0) {
        // Children never inherit the transient discharge marker.
        Node n = n0;
        n.discharges_until = kInvalidId;
        if (node_closed(n.Gamma, f_) || n.Z.is_empty())
            return {Expansion::Kind::Closed, {}};

        // A node carrying a pursuit of an until whose window it has passed is
        // closed (§4.1): that pursuit has no witness left to find.  A rolled
        // pursuit is exempt — its window is the recurrence [0, b-a] and the
        // cell just past it is where (Ustopabut) fires, the rolled deadline
        // being what stops the zone one cell later.
        for (const Pursuit& p : n.pursuits) {
            if (!p.is_until || p.rolled) continue;
            if (past_window(n.Z, p.x_mu, pursuit_window(p)))
                return {Expansion::Kind::Closed, {}};
        }

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

        // (Rlapse), §4.2.  A release pursuit the zone has outlived is
        // discharged: it was met by being survived.  Ordered before (Abs) so a
        // lapsed pursuit never absorbs a fresh demand into an obligation that
        // no longer exists.
        for (std::size_t i = 0; i < n.pursuits.size(); ++i) {
            const Pursuit& p = n.pursuits[i];
            if (p.is_until || p.stage != Pursuit::Stage::Here) continue;
            if (!lapsed(n.Z, p)) continue;
            Node c = n;
            c.pursuits.erase(c.pursuits.begin() + static_cast<long>(i));
            free_pursuit_clocks(c.Z, p);
            c.D = drop_deadline(n.D, p.x_mu);
            c.discharges_until = p.mu;
            return {Expansion::Kind::And, {std::move(c)}};
        }

        // (Abs) then (Cov): a demanded modality folds into a running universal
        // pursuit if there is one, and otherwise forks into discharge ⊕ launch.
        // Both live in apply_cover, which tries them in that order.  Ordered
        // before the unfolding rules so a modality and its own pursuit never
        // sit in Γ together unhandled.
        for (FormulaId id : n.Gamma.elements()) {
            if (!is_modality(f_.node(id).kind)) continue;
            CoverResult cr = apply_cover(n, id, ag_context_for(id), cmap_, ymap_,
                                         nc_, max_, f_, sx_cache_);
            switch (cr.kind) {
                case CoverResult::Kind::Close:
                    return {Expansion::Kind::Closed, {}};
                case CoverResult::Kind::Cover:
                    return {Expansion::Kind::And, onset_cells(id, std::move(cr.children))};
            }
        }

        // (Uunf), (Uunfcarry), (Runf): unfold a pursuit standing at this node.
        for (std::size_t i = 0; i < n.pursuits.size(); ++i)
            if (n.pursuits[i].stage == Pursuit::Stage::Here)
                return unfold_pursuit(n, i);

        // (Dinv): the node is saturated; fix the invariant its location carries.
        if (n.inv == Inv::Unset) return choose_invariant(n);

        // (Delay) and (EX) together, conjunctively.
        return successors(n);
    }

    /// Partition the (launch) child of an existential timed until into the
    /// integer cells of every other live clock.
    ///
    /// The launch resets @f$x_\mu@f$, so the age of the onset it starts from is
    /// read off the *other* clocks as @f$x_c - x_\mu = x_c@f$.  One launch zone
    /// therefore stands for a whole family of onsets, and the (Uunf) branching
    /// below it may narrow away not only witness *times* but whole *onsets*: the
    /// accepting stop child keeps the onsets it can serve, and the doomed ones
    /// survive only in closed siblings, so a demand that no run can meet is
    /// never seen.  On AG(EF[3,4] p) & AG[4,5] !p the doomed onset is the single
    /// point t = 1, and without this split the offset to the ban's clock stays
    /// the loose x_c - x_mu ∈ [0,∞) and the formula comes back SAT.
    ///
    /// Splitting conjunctively makes onset-dropping impossible: a doomed cell is
    /// a child in its own right and closes.  The constraints are single-clock —
    /// the launch has just zeroed @f$x_\mu@f$ — so no difference constraint
    /// enters the DBM, the construction stays diagonal-free, and Extra_M applies
    /// unchanged.  (Do not switch to Extra_LU: it is coarser and is tuned to
    /// preserve reachability, an existential property, whereas realisability of
    /// a node is universal over its zone.)
    std::vector<Node> onset_cells(FormulaId mu, std::vector<Node>&& kids) {
        // Existential modalities only: a universal one is absorbed rather than
        // relaunched, so its onsets are already merged by (Abs).  Both the
        // until and the release need it — the release perhaps more, since
        // nothing plays (M2)'s role for it, so a doomed onset left inside a
        // cell with servable ones is never refuted by any other means.
        const NodeKind k = f_.node(mu).kind;
        if (!onset_cells_ ||
            (k != NodeKind::TimedEU && k != NodeKind::TimedER) || kids.size() != 2)
            return std::move(kids);
        const ClockId x_mu = clock_of(cmap_, mu);
        if (x_mu == kNoClock) return std::move(kids);

        Node launch = std::move(kids[1]);
        // Live clocks other than x_mu: those a rule can still read.  A clock no
        // pursuit and no deadline reads has been freed out of the zone and
        // carries no onset information, so splitting on it only adds nodes.
        std::vector<ClockId> others;
        for (const Pursuit& p : launch.pursuits) {
            for (ClockId c : {p.x_mu, p.y_mu})
                if (c != kNoClock && c < nc_ && c != x_mu &&
                    std::find(others.begin(), others.end(), c) == others.end() &&
                    !clock_bounds_[c].empty())
                    others.push_back(c);
        }
        if (others.empty()) { kids[1] = std::move(launch); return std::move(kids); }

        std::vector<Node> out;
        out.push_back(std::move(kids[0]));                    // discharge
        std::function<void(std::size_t, Zone)> rec =
            [&](std::size_t i, Zone z) {
                if (z.is_empty()) return;
                if (i == others.size()) {
                    Node c = launch;
                    c.Z = std::move(z);
                    out.push_back(std::move(c));
                    return;
                }
                for (Zone& r : clock_cells(z, others[i])) rec(i + 1, std::move(r));
            };
        rec(0, launch.Z);
        if (debug_)
            std::fprintf(stderr, "CELLS mu=%s others=%zu -> %zu cells\n",
                         f_.to_string(mu).c_str(), others.size(), out.size() - 1);
        // Never drop the launch.  If the partition yielded nothing the launch
        // zone is unrealisable, and the obligation must then *close* its branch
        // — returning the discharge alone would discard the demand instead, and
        // (Cov) is conjunctive precisely so that cannot happen.
        if (out.size() == 1) out.push_back(std::move(launch));
        return out;
    }

    /// The integer cells of @p z along one clock: each of that clock's own
    /// change points, and each open interval between consecutive ones.
    std::vector<Zone> clock_cells(const Zone& z, ClockId c) const {
        const std::vector<std::int32_t>& bs = clock_bounds_[c];
        std::vector<Zone> out;
        // Below the first change point.  No guard on c flips there, so it is one
        // region — and it must be emitted, or the cells fail to cover the line:
        // a clock at 1 whose own bounds are {4,5} would otherwise land in no
        // cell at all and the whole partition would come back empty.
        if (bs.front() > 0) {
            Zone lo = z;
            lo.add_upper_bound(c, bs.front(), true);
            if (!lo.is_empty()) out.push_back(std::move(lo));
        }
        for (std::size_t i = 0; i < bs.size(); ++i) {
            Zone pt = z;                                      // c = bs[i]
            pt.add_lower_bound(c, bs[i], false);
            pt.add_upper_bound(c, bs[i], false);
            if (!pt.is_empty()) out.push_back(std::move(pt));
            if (i + 1 < bs.size()) {                          // c ∈ (bs[i], bs[i+1])
                Zone op = z;
                op.add_lower_bound(c, bs[i], true);
                op.add_upper_bound(c, bs[i + 1], true);
                if (!op.is_empty()) out.push_back(std::move(op));
            }
        }
        Zone hi = z;                                          // c > last
        hi.add_lower_bound(c, bs.back(), true);
        if (!hi.is_empty()) out.push_back(std::move(hi));
        return out;
    }

    // ── Zone predicates the side conditions read ────────────────────────
    //
    // Every side condition of §4.2 is an *entailment* Z ⊨ …, not a narrowing:
    // it asks whether the whole zone satisfies the guard, and leaves the zone
    // alone.  By Lemma 1(i) a zone keeps each clock at an integer or strictly
    // between two consecutive ones and every window endpoint is an integer, so
    // the zone always lies wholly inside a window or wholly outside it and the
    // question has an answer.  The tests below do not rely on that: each
    // intersects with the guard and asks whether the zone survived unchanged,
    // which is exact containment either way.

    /// @f$Z \models x \in I@f$.
    bool zone_in_window(const Zone& z, ClockId x, const Window& w) const {
        if (x == kNoClock) return true;          // untimed: I is the whole line
        Zone t = z;
        constrain_in_window(t, x, w);
        return !t.is_empty() && t == z;
    }

    /// @f$Z \models x > \sup I@f$ — the window is wholly behind the zone.
    bool past_window(const Zone& z, ClockId x, const Window& w) const {
        if (x == kNoClock || w.hi_inf) return false;
        Zone t = z;                              // the complement of "beyond"
        t.add_upper_bound(x, w.hi, w.hi_strict);
        return t.is_empty();
    }

    /// Does @p z contain a valuation inside @p w?  (Used by the re-imposition
    /// clause of (Delay), which asks whether the child's cell *meets* a window,
    /// not whether it lies inside one.)
    bool window_meets(const Zone& z, ClockId x, const Window& w) const {
        if (x == kNoClock) return true;
        Zone t = z;
        constrain_in_window(t, x, w);
        return !t.is_empty();
    }

    /// @f$Z \models y_\mu \geq a \wedge y_\mu > 0@f$: no onset has been raised
    /// since @f$a@f$ before now, so a witness here answers every onset the
    /// pursuit still owes and it may end.  The @f$y_\mu > 0@f$ conjunct is what
    /// adds, at @f$a = 0@f$, that none was raised at this very node.
    bool onsets_ceased(const Zone& z, ClockId y, std::int32_t a) const {
        if (y == kNoClock) return false;
        Zone t = z;
        t.add_lower_bound(y, a, false);
        t.add_lower_bound(y, 0, true);
        return !t.is_empty() && t == z;
    }

    /// Is @p z the cell abutting @f$\sup I@f$ from above, i.e.
    /// @f$x \in (\sup I, \sup I + 1)@f$?
    bool abutting_cell(const Zone& z, ClockId x, const Window& w) const {
        if (x == kNoClock || w.hi_inf) return false;
        Zone t = z;
        t.add_lower_bound(x, w.hi, true);
        t.add_upper_bound(x, w.hi + 1, true);
        return !t.is_empty() && t == z;
    }

    /// (Rlapse)'s guard: @f$Z \models x_\mu > \sup I@f$, or the pursuit is
    /// persistent and @f$Z \models y_\mu > b@f$.  A persistent release has had
    /// its window rewritten to @f$[a,\infty)@f$ and so can never pass it; what
    /// ends it is its last onset outliving the *original* window.
    bool lapsed(const Zone& z, const Pursuit& p) const {
        if (past_window(z, p.x_mu, pursuit_window(p))) return true;
        const Window ow = window_of(p.mu, f_);
        if (p.persistent && p.y_mu != kNoClock && !ow.hi_inf) {
            Zone t = z;
            t.add_upper_bound(p.y_mu, ow.hi, ow.hi_strict);
            if (t.is_empty()) return true;
        }
        return false;
    }

    /// @f$Z \backslash x_\mu y_\mu@f$: a stopped pursuit frees its clocks.
    void free_pursuit_clocks(Zone& z, const Pursuit& p) const {
        if (p.x_mu != kNoClock && p.x_mu < nc_) z.free(p.x_mu);
        if (p.y_mu != kNoClock && p.y_mu < nc_) z.free(p.y_mu);
    }

    /// A member of @f$\Gamma_{\mathsf{prop}}@f$: an atom or a negated atom.
    bool is_literal(FormulaId id) const {
        const FormulaNode& fn = f_.node(id);
        if (fn.kind == NodeKind::Atom) return true;
        return fn.kind == NodeKind::Not &&
               f_.node(fn.children[0]).kind == NodeKind::Atom;
    }

    /// @f$\Deadline^{\ast}@f$: @f$\Deadline@f$ with @f$x_\mu@f$'s deadline
    /// replaced by the *rolled* deadline.
    ///
    /// The paper (§4.2) makes it the strict @f$x_\mu < (b-a)+1@f$, one cell wide
    /// of the closed bound, and that width is what (Ustopabut) needs: under the
    /// closed @f$x_\mu \leq b-a@f$, @f$\uparrow\! Z \cap Inv_D@f$ never reaches
    /// the abutting cell, so the abutting stop could never fire and the rule
    /// would be dead.  @c TCTL_ROLLED_DEADLINE=closed selects the closed bound
    /// instead, for measuring exactly that.
    PooledVec<Deadline> rolled_deadline(const PooledVec<Deadline>& D, ClockId x,
                                        const Window& ow) const {
        PooledVec<Deadline> out = drop_deadline(D, x);
        if (x == kNoClock || ow.hi_inf) return out;
        const std::int32_t span = ow.hi - ow.lo;
        if (rolled_strict_) out.push_back(Deadline{x, span + 1, true});
        else                out.push_back(Deadline{x, span, false});
        std::sort(out.begin(), out.end());
        return out;
    }

    // ── (Uunf), (Uunfcarry), (Runf) ─────────────────────────────────────
    Expansion unfold_pursuit(const Node& n, std::size_t i) {
        const Pursuit p = n.pursuits[i];
        const FormulaNode& mn = f_.node(p.mu);
        const FormulaId phi = mn.children[0], psi = mn.children[1];
        const bool existential = !is_universal(mn.kind);
        const auto defer = existential ? Pursuit::Stage::DeferEX
                                       : Pursuit::Stage::DeferAX;
        const Window w  = pursuit_window(p);     // the window still to be met
        const Window ow = window_of(p.mu, f_);   // the modality's own I
        const bool in_window = zone_in_window(n.Z, p.x_mu, w);
        const auto drop_at = [&](Node& c) {
            c.pursuits.erase(c.pursuits.begin() + static_cast<long>(i));
        };

        Expansion e;
        e.kind = Expansion::Kind::Or;

        // (Runf).  Θ = {φ₂} iff Z ⊨ x_μ ∈ I: inside the window the pursuit
        // asserts its body, before it asserts nothing.  Either way it is
        // released by φ₁ or deferred, exactly as an until is.
        if (!p.is_until) {
            Node stop = n;                                    // (Rstop)
            stop.Gamma.insert(phi);
            if (in_window) stop.Gamma.insert(psi);
            drop_at(stop);
            free_pursuit_clocks(stop.Z, p);
            stop.discharges_until = p.mu;
            e.children.push_back(std::move(stop));

            Node go = n;                                      // (Rgo)
            if (in_window) go.Gamma.insert(psi);
            go.pursuits[i].stage = defer;
            e.children.push_back(std::move(go));
            return e;
        }

        // (Uunf).  Stop because φ₂ holds now and the window is open, or go on
        // because φ₁ holds now and the witness is later.
        if (!p.persistent) {
            if (in_window) {
                Node stop = n;                                // (Ustop)
                stop.Gamma.insert(psi);
                drop_at(stop);
                free_pursuit_clocks(stop.Z, p);
                stop.D = drop_deadline(n.D, p.x_mu);
                stop.discharges_until = p.mu;
                e.children.push_back(std::move(stop));
            }
            Node go = n;                                      // (Ugo)
            go.Gamma.insert(phi);
            go.pursuits[i].stage = defer;
            e.children.push_back(std::move(go));
            return e;
        }

        // (Uunfcarry).  A stop also asserts φ₁ when a > 0: an onset s with
        // w - s < a is not answered at w, so φ₁ is still owed there.
        const bool theta_a = ow.lo > 0;
        if (in_window) {
            // (Ustopcarry): continue the recurrence.  Re-zero x_μ, rewrite the
            // window to [0, b-a] and cap the next witness there.
            Node c = n;
            c.Gamma.insert(psi);
            if (theta_a) c.Gamma.insert(phi);
            c.Z.reset(p.x_mu);
            c.just_reset.push_back(p.x_mu);
            c.pursuits[i].rolled = true;
            c.pursuits[i].stage  = Pursuit::Stage::Here;
            c.D = rolled_deadline(n.D, p.x_mu, ow);
            c.discharges_until = p.mu;
            e.children.push_back(std::move(c));

            // (Ustopdrop): a recurrence that never ended would be wrong.  The
            // pursuit may end at a witness exactly when no onset has been
            // raised since a before it.
            if (onsets_ceased(n.Z, p.y_mu, ow.lo)) {
                Node d = n;
                d.Gamma.insert(psi);
                if (theta_a) d.Gamma.insert(phi);
                drop_at(d);
                free_pursuit_clocks(d.Z, p);
                d.D = drop_deadline(n.D, p.x_mu);
                d.discharges_until = p.mu;
                e.children.push_back(std::move(d));
            }
        }

        // (Ustopabut): the stop whose witness is an interval rather than an
        // instant.  A model may serve the onsets owed after a stop at w by
        // satisfying φ₂ throughout an interval beginning just past w + (b-a),
        // open at it; no single instant at or before w + (b-a) carries one.
        // The abutting stop asserts φ₁ and φ₂ together over its whole cell.
        if (p.rolled && abutting_cell(n.Z, p.x_mu, w)) {
            Node c = n;
            c.Gamma.insert(phi);
            c.Gamma.insert(psi);
            c.Z.reset(p.x_mu);
            c.just_reset.push_back(p.x_mu);
            c.pursuits[i].stage = Pursuit::Stage::Here;
            c.D = rolled_deadline(n.D, p.x_mu, ow);
            c.interval_witness = true;
            c.discharges_until = p.mu;
            // The witness is an interval, so a release whose window contains
            // arbitrarily small positive offsets obliges its body across this
            // whole cell, not merely at its far end: a position later in the
            // crossing lies inside the window of one earlier in it.  A ban
            // re-imposed by the delay is already launched and deferred by the
            // time this stop fires — saturation precedes unfolding — so binding
            // it at launch (apply_cover) does not reach it, and it has to be
            // bound here.  This is what closes the abutting child on a rate
            // contradiction.
            for (const Pursuit& s : c.pursuits) {
                if (s.is_until) continue;
                if (window_of(s.mu, f_).lo != 0) continue;
                c.Gamma.insert(f_.node(s.mu).children[1]);
            }
            e.children.push_back(std::move(c));
        }

        Node go = n;                                          // (Ugocarry)
        go.Gamma.insert(phi);
        go.pursuits[i].stage = defer;
        e.children.push_back(std::move(go));
        return e;
    }

    // ── (Dinv) ──────────────────────────────────────────────────────────

    /// An active clock, with the next hyperplane (Dinv) may put in front of it.
    struct Act {
        ClockId      c;
        std::int32_t lv;      ///< the clock's integer lower bound in Z
        bool         at_pt;   ///< Z pins c exactly on one of its own change points
        bool         has_nb;  ///< a change point remains above lv
        std::int32_t nb;      ///< the next one
    };

    /// The active clocks of @p n and their next hyperplanes.
    ///
    /// Active means a clock a guard can still be tested against: those of the
    /// live pursuits and of the deadlines in @f$Inv_D(N)@f$.  A clock with no
    /// live pursuit is never read and is freshly reset if its modality is
    /// launched again, so bounding it would only add nodes.
    ///
    /// The hyperplane is the clock's next *own change point* — an endpoint of
    /// its modality's window, or one of the nesting shifts of
    /// add_onset_shifts() — and not simply the next integer.  Only at those
    /// values can a guard on the clock, or a demand it carries, flip; a cut
    /// anywhere else splits a cell whose every position answers every guard
    /// alike, and produces two nodes where the calculus needs one.  Taking the
    /// next integer instead makes the graph scale with @f$M@f$: on the
    /// constant-free onset family that is 1.19M nodes at @f$M=64@f$ against
    /// 6980 at @f$M=4@f$, for the same proof.
    std::vector<Act> active_clocks(const Node& n) const {
        std::vector<Act> out;
        std::vector<char> seen(nc_, 0);
        auto note = [&](ClockId c) {
            if (c == kNoClock || c >= nc_ || seen[c]) return;
            seen[c] = 1;
            Act a; a.c = c; a.nb = 0;
            bool lstrict = false;
            clk_lower(n.Z, c, a.lv, lstrict);
            a.at_pt  = at_own_bound(n.Z, c, a.lv, lstrict);
            a.has_nb = next_own_bound(c, a.lv, a.nb);
            out.push_back(a);
        };
        for (const Pursuit& p : n.pursuits) { note(p.x_mu); note(p.y_mu); }
        for (const Deadline& d : n.D) note(d.x_mu);
        return out;
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

    // Lower endpoint of clock c in z:  c >= lv,  strict iff `lstrict`.  A zone
    // keeps each clock at an integer or strictly inside a unit cell, so the next
    // hyperplane above it is lv + 1 in both cases.
    void clk_lower(const Zone& z, ClockId c, std::int32_t& lv, bool& lstrict) const {
        const Bound lb = z.get_bound(kReferenceClock, c);   // 0 - c <= lb ⇒ c >= -lb
        if (lb.is_infinity()) { lv = 0; lstrict = false; return; }
        lv = -lb.value; lstrict = lb.is_strict;
    }

    /// (Dinv).  The location may be occupied strictly below the next hyperplane
    /// or up to and including it; the two are alternatives, so the rule is
    /// disjunctive.  The choice matters because a witness may have to be
    /// produced at a specific instant: below k a pursuit of E(p U[1,2) q) with
    /// x_μ ∈ (1,2) can still stop, while at k = 2 its window has closed.
    Expansion choose_invariant(const Node& n) {
        bool any_nb = false, any_pt = false;
        for (const Act& a : active_clocks(n)) {
            if (a.has_nb) any_nb = true;
            // Only a point on a clock an *until* pursuit reads can be the
            // instant a witness has to be produced at; a release wants its body
            // over an interval, and a deadline clock only bounds the elapse.
            if (!a.at_pt) continue;
            for (const Pursuit& p : n.pursuits)
                if (p.is_until && p.x_mu == a.c) { any_pt = true; break; }
        }
        // The candidates, in order.  Stay -- the run leaves this location at
        // once -- is only available where the zone pins an active clock on one
        // of its own change points, so that the invariant it stands for has an
        // integer bound; and only an until pursuit can be obliged to act at one
        // exact instant, a release wanting its body over an interval.
        Inv cand[3];
        std::size_t nc = 0;
        if (any_pt) cand[nc++] = Inv::Stay;
        if (any_nb) cand[nc++] = Inv::Below;
        cand[nc++] = Inv::Upto;

        // Two branches that leave the same parts behind are the same choice
        // written twice: the (EX) children do not depend on the invariant, so
        // the expansions below them are identical and only the recorded Inv
        // differs.  That happens constantly -- Upto collapses onto Below the
        // moment a deadline empties the boundary part, and Below onto Stay
        // whenever the open part is the zone itself -- and each duplicate is a
        // whole subtree explored twice.  Deciding it here costs one delay_parts
        // per candidate, which the child would have computed anyway.
        Expansion e;
        e.kind = Expansion::Kind::Or;
        std::vector<std::vector<Zone>> seen;
        seen.reserve(nc);
        for (std::size_t i = 0; i < nc; ++i) {
            Node t = n;
            t.inv = cand[i];
            std::vector<Zone> parts = delay_parts(t);
            bool dup = false;
            for (const std::vector<Zone>& q : seen) {
                if (q.size() != parts.size()) continue;
                bool same = true;
                for (std::size_t j = 0; j < parts.size(); ++j)
                    if (!(q[j] == parts[j])) { same = false; break; }
                if (same) { dup = true; break; }
            }
            if (dup) continue;
            seen.push_back(std::move(parts));
            e.children.push_back(std::move(t));
        }
        if (e.children.size() == 1) e.kind = Expansion::Kind::And;
        return e;
    }

    // ── (Delay) ─────────────────────────────────────────────────────────

    /// The non-empty parts of @f$\uparrow\! Z \cap Inv \cap Inv_D(N)@f$.
    ///
    /// Time advances one truth region at a time: by Lemma 1(i) the truth of
    /// every subformula is constant along a segment that crosses no integer
    /// hyperplane, so a node whose zone lies in one region answers each guard
    /// once and unambiguously — which is what keeps [1,2) distinguishable from
    /// [1,2].  The parts are therefore the open cell below the hyperplanes and,
    /// when the invariant admits it, the boundary regions on them.  They are
    /// returned together because (Delay) is conjunctive: all of them are
    /// reachable by elapsing time, and a witness must admit every elapse its
    /// invariant permits.  The zero-elapse part is dropped, both delay children
    /// elapsing positive time.
    std::vector<Zone> delay_parts(const Node& n) const {
        // The location is occupied only at this instant, so it permits no
        // elapse and has no (Delay)-children — its expansion is its (EX)
        // children alone.
        if (n.inv == Inv::Stay) return {};
        const std::vector<Act> act = active_clocks(n);
        const bool upto = (n.inv == Inv::Upto);
        bool any_nb = false;
        for (const Act& a : act) if (a.has_nb) any_nb = true;

        Zone Zup = n.Z;
        Zup.up();
        apply_inv(Zup, n.D);                       // Inv_D(N)
        if (Zup.is_empty()) return {};

        Zone cur = n.Z;
        cur.extrapolate(max_);

        // Is the zone a single point in every active clock?  Then, and only
        // then, does a part equal to it stand for zero elapse.
        bool at_point = true;
        for (const Act& a : act) if (!a.at_pt) { at_point = false; break; }

        std::vector<Zone> parts;
        auto emit = [&](Zone z) {
            if (z.is_empty()) return;
            z.extrapolate(max_);
            // "Both delay children elapse positive time" (§4.2) drops the
            // zero-elapse part.  A part equal to the current zone is zero-elapse
            // only when that zone is a *point*: inside an open cell time passes
            // with the zone unchanged, so the part is a genuine delay and must
            // be emitted, as a self-loop.  Dropping it left a node inside a cell
            // with no (Delay) child at all, so a run could sit there for ever
            // through (EX) steps alone with no delay edge for (M1) to see, and
            // the stall was accepted.  Emitted, the self-loop is a delay whose
            // cycle bounds a clock it never resets, so (M1) rejects it — which
            // is what refutes AG(EG[2,4] p) & AG[6,7] !p, whose doomed onsets
            // survived by stalling just below the cell where they close.
            if (z == cur && at_point) return;
            for (const Zone& q : parts) if (q == z) return;
            parts.push_back(std::move(z));
        };

        // Δ°, the part below the hyperplanes: every active clock strictly below
        // its next change point, and every clock sitting exactly on one pushed
        // strictly off it.  Both constraints are single-clock, so no diagonal
        // enters the construction.  The push-off is what keeps a boundary point
        // and the open cell above it two distinct regions, and it is needed
        // whether or not a change point remains ahead: a clock resting on its
        // *last* bound still has the point and the cell above it as two regions,
        // and a zone spanning both answers x > b and x = b at once — which is
        // why E(true U(2,∞) p), whose only witness lies strictly above its last
        // constant, could not stop while this was skipped.
        Zone open = Zup;
        for (const Act& a : act) {
            if (a.has_nb) open.add_upper_bound(a.c, a.nb, true);
            if (a.at_pt)  open.add_lower_bound(a.c, a.lv, true);
        }

        if (!any_nb) {
            // Past the last change point of every active clock, so no hyperplane
            // remains and the invariant bounds nothing: (Delay) degenerates to
            // the cell above, a self-loop that keeps time running.  It is
            // emitted even when the extrapolated zone is unchanged — the elapse
            // is unbounded, not zero.  Nor is it Zeno: every active clock is now
            // above its maximum, hence unbounded, so (M1) accepts the cycle.
            if (open.is_empty()) return {};
            open.extrapolate(max_);
            parts.push_back(std::move(open));
            return parts;
        }

        emit(std::move(open));
        if (!upto) return parts;

        // Δ^∂, the parts on the hyperplanes.  Which clocks land on one together
        // is fixed by the zone's diagonals, so this enumeration finds the
        // combinations the zone admits rather than branching over all of them.
        Zone capped = Zup;
        for (const Act& a : act) {
            if (a.has_nb) capped.add_upper_bound(a.c, a.nb, false);
            if (a.at_pt)  capped.add_lower_bound(a.c, a.lv, true);
        }
        std::vector<const Act*> cand;
        for (const Act& a : act) if (a.has_nb) cand.push_back(&a);

        std::function<void(std::size_t, Zone, bool)> rec =
            [&](std::size_t i, Zone z, bool any_at) {
                if (z.is_empty()) return;
                if (i == cand.size()) { if (any_at) emit(std::move(z)); return; }
                const Act& a = *cand[i];
                Zone at = z;                       // c lands on its hyperplane
                at.add_lower_bound(a.c, a.nb, false);
                at.add_upper_bound(a.c, a.nb, false);
                rec(i + 1, std::move(at), true);
                Zone below = std::move(z);         // c is still below it
                below.add_upper_bound(a.c, a.nb, true);
                rec(i + 1, std::move(below), any_at);
            };
        rec(0, std::move(capped), false);
        return parts;
    }

    /// A (Delay) child is a new cell — in the extraction a new location with a
    /// label of its own — so its goals re-impose the demands of the cell rather
    /// than inherit the claims of the last one (§4.2).
    Node make_delay_child(const Node& n, Zone z) const {
        Node d;
        d.X = n.X;
        d.Z = std::move(z);
        d.D = n.D;
        d.pursuits = n.pursuits;
        d.inv = Inv::Unset;
        d.delayed_here = true;

        // A literal is a claim about one configuration and does not cross the
        // cell edge, so Γ' is Γ without its literals …
        FormulaIdVec keep;
        keep.reserve(n.Gamma.elements().size());
        for (FormulaId id : n.Gamma.elements())
            if (!is_literal(id)) keep.push_back(id);
        d.Gamma = FormulaSet::from_sorted(keep);

        for (const Pursuit& p : d.pursuits) {
            const FormulaNode& mn = f_.node(p.mu);
            if (!p.is_until) {
                // … plus the body of every release pursuit whose window the
                // child's zone meets: a release obliges its body at every
                // position of its window, not only at the discrete steps.  This
                // is also what keeps the clock y_μ of any demand that body
                // raises honest across a delay — the re-imposed body re-demands
                // μ, and (Abs) re-zeroes y_μ at every cell it still covers.
                if (window_meets(d.Z, p.x_mu, pursuit_window(p)))
                    d.Gamma.insert(mn.children[1]);
            } else if (p.stage != Pursuit::Stage::Here) {
                // … plus the first argument of every deferred until pursuit,
                // owed at every position before its stop.
                d.Gamma.insert(mn.children[0]);
            }
        }
        return d;
    }

    // ── (EX) ────────────────────────────────────────────────────────────

    /// One child per demanded @f$EX\psi@f$, each carrying @f$\psi@f$ under the
    /// context of its parent; a single stutter child when no step is demanded.
    ///
    /// The context is consumed by the step rather than inherited: a universal
    /// obligation persists because unfolding it puts it back, and a discharged
    /// one disappears because nothing does.
    std::vector<Node> ex_children(const Node& n) const {
        PooledVec<Pursuit> ex, ax;
        for (const Pursuit& p : n.pursuits) {
            if (p.stage == Pursuit::Stage::DeferEX)      ex.push_back(p);
            else if (p.stage == Pursuit::Stage::DeferAX) ax.push_back(p);
        }
        auto make = [&](const Pursuit* one) {
            Node c;
            c.Gamma = n.X;                    // {ψ} ∪ Ctx
            c.Z = n.Z;
            c.D = n.D;
            c.inv = Inv::Unset;
            if (one) {
                Pursuit q = *one;
                q.stage = Pursuit::Stage::Here;
                c.pursuits.push_back(q);
            }
            for (const Pursuit& q0 : ax) {
                Pursuit q = q0;
                q.stage = Pursuit::Stage::Here;
                c.pursuits.push_back(q);
            }
            return c;
        };
        std::vector<Node> out;
        if (ex.empty()) out.push_back(make(nullptr));
        else for (const Pursuit& p : ex) out.push_back(make(&p));
        return out;
    }

    /// The children of a saturated node with a fixed invariant: its (Delay)-
    /// and (EX)-children together, conjunctively, since a witness must admit
    /// every elapse its invariant permits and supply every step its goals
    /// demand.
    Expansion successors(const Node& n) {
        Expansion e;
        e.kind = Expansion::Kind::And;
        for (Zone& z : delay_parts(n))
            e.children.push_back(make_delay_child(n, std::move(z)));
        for (Node& c : ex_children(n))
            e.children.push_back(std::move(c));
        if (e.children.empty()) return {Expansion::Kind::Closed, {}};
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
        // The reset set as a bitmask rather than a counted list: the tableau
        // has few clocks, so one or two words cover it however many were reset.
        for (std::size_t w = 0; w < rw32_; ++w) put(k, 0);
        const std::size_t base = k.size() - rw32_;
        for (std::uint32_t c : scratch32_) k[base + (c >> 5)] |= 1u << (c & 31);
        put(k, static_cast<std::uint32_t>(n.discharges_until));
        // Whether (Delay) produced this node is what \ref M1 reads, so it must
        // tell two nodes apart: the same goals and zone are reachable both by
        // elapsing time and by a discrete step or an expansion step, and
        // merging the two would let a cycle built from expansion steps alone
        // inherit the delay that only the other arrival carried.
        (void)base;
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
        /// Children and active until pursuits live in the flat arenas
        /// #charena_ / #uarena_, not in a vector apiece.  Both are written once
        /// and read on every acceptance pass, and at two or three entries each a
        /// std::vector spent a 24-byte header plus a malloc rounding on what
        /// fits in a dozen bytes -- some hundred bytes per node, against a graph
        /// that runs to hundreds of thousands of them.
        std::uint32_t ch_off = 0, u_off = 0;
        std::uint32_t ch_len = 0, u_len = 0;
        FormulaId     discharges = kInvalidId; ///< (U•) stop taken here
        std::uint32_t index = 0, low = 0;      ///< Tarjan
        Expansion::Kind kind = Expansion::Kind::Closed;
        bool delayed = false;               ///< reached by (Delay)
        bool visited = false, onstack = false;
        bool done = false, val = false;     ///< final once its SCC is evaluated
    };

    /// A read-only run of node ids (or formula ids) inside one of the arenas.
    struct Span {
        const std::uint32_t* p = nullptr;
        std::uint32_t        n = 0;
        const std::uint32_t* begin() const noexcept { return p; }
        const std::uint32_t* end()   const noexcept { return p + n; }
        std::size_t          size()  const noexcept { return n; }
        bool                 empty() const noexcept { return n == 0; }
        std::uint32_t operator[](std::size_t i) const noexcept { return p[i]; }
    };
    Span ch_of(std::uint32_t v) const {
        return {charena_.data() + g_[v].ch_off, g_[v].ch_len};
    }
    Span us_of(std::uint32_t v) const {
        return {uarena_.data() + g_[v].u_off, g_[v].u_len};
    }

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
        // Children live in charena_ now; there is no per-node buffer to free.
        (void)v;
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
        auto it = atom_memo_.find(id);
        if (it != atom_memo_.end()) return it->second;
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
        atom_memo_.emplace(id, out);
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
        if (it != clock_memo_.end()) return it->second;
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
        struct Item { FormulaId id; bool in_ctx; };
        std::vector<Item> items;
        for (FormulaId id : n.Gamma.elements()) items.push_back({id, false});
        for (FormulaId id : n.X.elements())     items.push_back({id, true});
        std::vector<FormulaId> pmu;
        for (const Pursuit& p : n.pursuits) pmu.push_back(p.mu);
        if (items.size() + pmu.size() < 2) return {};

        // Whether a node splits depends only on which formulas it carries, not
        // on its zone, so a shape that did not split never will.  Shapes repeat
        // heavily -- a nested tower has roughly half as many shapes as nodes --
        // and without this the union-find below runs again at each of them,
        // which is pure loss on any formula that never decomposes.
        std::uint64_t sig = 1469598103934665603ull;
        {
            sigbuf_.clear();
            for (const Item& it : items) sigbuf_.push_back(it.id);
            for (FormulaId mu : pmu) sigbuf_.push_back(mu);
            std::sort(sigbuf_.begin(), sigbuf_.end());
            for (FormulaId id : sigbuf_) {
                sig ^= static_cast<std::uint64_t>(id);
                sig *= 1099511628211ull;
            }
            if (nosplit_.count(sig)) return {};
        }
        auto remember_nosplit = [&] { nosplit_.insert(sig); };

        std::vector<std::uint64_t> at;
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
        for (std::size_t i = 0; i < m; ++i)
            for (std::size_t j = i + 1; j < m; ++j) {
                const bool share = (at[i] & at[j]) != 0 || (at[i] == 0 && at[j] == 0);
                if (share) up[find(i)] = find(j);
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
            c.Z = n.Z; c.D = n.D; c.inv = n.inv;
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
        const std::uint64_t h = key_hash(k.data(), k.size());
        std::size_t slot = 0;
        if (const std::uint32_t hit = klookup(k.data(), k.size(), h, slot);
            hit != kNoRegion)
            return hit;

        const auto id = static_cast<std::uint32_t>(g_.size());
        // Grow the parallel per-node arrays in fixed steps rather than by
        // doubling: the same reason as the arena, one buffer instead of two.
        if ((id & 0xFFFFu) == 0) {
            const std::size_t want = id + 0x10000u;
            koff_.reserve(want); klen_.reserve(want); khash_.reserve(want);
            cap_.reserve(want * words_); res_.reserve(want * words_);
            unb_.reserve(want * words_);
        }
        klen_.push_back(static_cast<std::uint32_t>(k.size()));
        khash_.push_back(h);
        koff_.push_back(karena_put(k.data(), static_cast<std::uint32_t>(k.size())));
        ktab_[slot] = id + 1;
        // Keep the load factor under 0.7; the grow rehashes the entry just
        // written along with the rest, so writing it first is safe.
        if ((id + 1) * 10 >= ktab_.size() * 7) ktab_grow();
        g_.emplace_back();
        cap_.resize(cap_.size() + words_, 0);
        res_.resize(res_.size() + words_, 0);
        unb_.resize(unb_.size() + words_, 0);

        GNode& gn = g_.back();
        gn.n          = std::make_unique<Node>(std::move(n));
        gn.delayed    = gn.n->delayed_here;
        gn.discharges = gn.n->discharges_until;
        gn.u_off      = static_cast<std::uint32_t>(uarena_.size());
        // (M2) is stated for existential untils, but a *bounded* existential
        // release needs the same treatment and nothing else supplies it.  Its
        // branch must outlive its window -- on a time-divergent run x_mu always
        // passes sup I and (Rlapse) fires -- so if no path carrying the pursuit
        // ever drops it, that branch is Zeno and the release is not really
        // witnessed.  Without this a doomed onset survives by stalling inside
        // a cell for ever: every node on the stall cycle satisfies (M1) through
        // its (Cov) launch sibling, which starts a *fresh, safe* onset, so (M1)
        // is met by another configuration's future while the doomed pursuit's
        // own branch never progresses.  That is how AG(EG[2,4] p) & AG[6,7] !p
        // came back SAT.
        for (const Pursuit& p : gn.n->pursuits) {
            if (p.is_until) { uarena_.push_back(p.mu); continue; }
            const NodeKind mk = f_.node(p.mu).kind;
            if (is_universal(mk)) continue;
            if (!window_of(p.mu, f_).hi_inf) uarena_.push_back(p.mu);
        }
        gn.u_len = static_cast<std::uint32_t>(uarena_.size()) - gn.u_off;

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
        // Distinct children of one expansion often intern to the same node —
        // (Delay) parts that extrapolate together, and (EX) children that agree
        // once the context is consumed.  A repeat says nothing new under either
        // kind (a conjunction demands it once, a disjunction offers it once) but
        // is re-scanned by every acceptance loop and every reverse-edge build,
        // all of which are linear in the child list.  Order is preserved so the
        // extraction still walks children in rule order.
        {
            std::vector<std::uint32_t> seen;
            seen.reserve(kids.size());
            for (std::uint32_t k : kids)
                if (std::find(seen.begin(), seen.end(), k) == seen.end())
                    seen.push_back(k);
            kids.swap(seen);
        }
        if (debug_) {                       // temporary: edge dump for figures
            std::ostringstream os;
            os << "EDGE " << v << " ["
               << (e.kind == Expansion::Kind::And ? "AND" : "OR") << "]";
            for (std::uint32_t k : kids) os << ' ' << k;
            os << '\n';
            std::fputs(os.str().c_str(), stderr);
        }
        g_[v].kind = e.kind;
        g_[v].ch_off = static_cast<std::uint32_t>(charena_.size());
        g_[v].ch_len = static_cast<std::uint32_t>(kids.size());
        charena_.insert(charena_.end(), kids.begin(), kids.end());
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
                        for (std::uint32_t c : ch_of(S[i]))
                            if (!child_alive(c)) { ok = false; break; }
                    } else {
                        ok = false;
                        for (std::uint32_t c : ch_of(S[i]))
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
            for (std::uint32_t c : ch_of(S[i])) {
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
            for (std::uint32_t c : ch_of(S[i])) {
                if (pos.count(c)) continue;
                if (g_[c].done && g_[c].val) { reaches[i] = 1; break; }
            }
        }
        for (const std::vector<std::size_t>& T : sub_sccs(S, pos, alive)) {
            bool cyclic = T.size() > 1;
            if (!cyclic)
                for (std::uint32_t c : ch_of(S[T[0]]))
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
                for (FormulaId mu : us_of(S[i])) mus.push_back(mu);
        std::sort(mus.begin(), mus.end());
        mus.erase(std::unique(mus.begin(), mus.end()), mus.end());
        if (mus.empty()) return false;

        const std::vector<std::vector<std::size_t>> rev = reverse_edges(S, pos, alive);
        auto pursues = [&](std::uint32_t id, FormulaId mu) {
            const Span u = us_of(id);
            return std::find(u.begin(), u.end(), mu) != u.end();
        };

        bool removed = false;
        for (FormulaId mu : mus) {
            // \ref M2 asks for a path that carries mu throughout *with x_mu
            // unreset along the way*, which is what ties the stop to the onset
            // the pursuit measures.  Without that clause a doomed pursuit is
            // laundered: (Cov)'s launch replaces the live pursuit of mu with a
            // fresh one on a re-zeroed x_mu, and `pursues` matches on the
            // modality alone, so the exit clause below credits the doomed
            // obligation with a stop that in fact belongs to a later, servable
            // onset.  On AG(EF[3,4] p) & AG[4,5] !p the onset at t = 1 is
            // doomed -- its whole window [4,5] is banned -- and it was being
            // discharged by the stop of an onset past 5.
            //
            // The clause is existential-only, as in the paper: a universal
            // until is governed by \ref M3, and (Ustopcarry) legitimately
            // re-zeroes x_mu while discharging.
            const bool e_until = !is_universal(f_.node(mu).kind);
            const ClockId x_mu = clock_of(cmap_, mu);
            auto reset_on_entry = [&](std::uint32_t id) {
                if (!m2_unreset_ || !e_until || x_mu == kNoClock || x_mu >= nc_)
                    return false;
                return ((res_of(id)[x_mu >> 6] >> (x_mu & 63)) & 1ULL) != 0;
            };

            std::vector<char> live(m, 0), ok(m, 0);
            for (std::size_t i = 0; i < m; ++i)
                live[i] = alive[i] && pursues(S[i], mu);

            for (std::size_t i = 0; i < m; ++i) {
                if (!live[i]) continue;
                bool stop = false, exit_keep = false, exit_reset = false,
                     unreset_cont = false;
                for (std::uint32_t c : ch_of(S[i])) {
                    const bool in_S = pos.count(c) != 0;
                    const bool ca   = in_S ? alive[pos.at(c)] != 0 : (g_[c].done && g_[c].val);
                    if (!ca) continue;
                    if (g_[c].discharges == mu) { stop = true; break; }
                    if (!pursues(c, mu)) continue;
                    if (!reset_on_entry(c)) unreset_cont = true;
                    // a surviving exit that carries the pursuit onward and so
                    // must discharge it in turn
                    if (!in_S) {
                        if (reset_on_entry(c)) exit_reset = true;
                        else                   exit_keep  = true;
                    }
                }
                // A (Cov) launch re-zeroes x_mu and *replaces* the pursuit, so
                // it continues a later onset, not this one — crediting it is
                // what laundered the doomed obligation.  The obligation rides
                // the launch's AND-sibling, the discharge, which keeps the
                // pursuit untouched; so the launch is discounted exactly when
                // such a sibling is there to carry it.  Where no unreset
                // continuation exists at all, the reset child is the only
                // continuation and discounting it would reject a witness.
                ok[i] = stop || exit_keep || (exit_reset && !unreset_cont);
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
                const Span ch = ch_of(S[v]);
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
            if (st.back().ci < g_[v].ch_len) {
                const std::uint32_t w = ch_of(v)[st.back().ci++];
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
    mutable std::map<FormulaId, std::uint64_t> atom_memo_;
    std::map<std::string, std::size_t> atom_bit_;
    mutable std::map<FormulaId, std::vector<ClockId>> clock_memo_;
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
    /// The onset clock y_mu of every modality that can become persistent.
    ClockMap ymap_;
    /// Zones that straddled a release window: the cell discipline says none can.
    mutable std::uint64_t straddle_ = 0;
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
    /// (M2)'s "x_mu unreset along the way" clause.  On by default;
    /// TCTL_M2_UNRESET=0 drops it, for the ablation.  Without it the
    /// E-until/E-release re-demand families come back wrongly SAT.
    bool m2_unreset_ = [] {
        const char* v = std::getenv("TCTL_M2_UNRESET");
        return !(v && std::string(v) == "0");
    }();
    /// Partition an existential launch into onset cells (see onset_cells()).
    /// Off by default: measured, it changes no verdict and no node count,
    /// because (Delay) already leaves every zone region-uniform per clock.
    /// TCTL_ONSET_CELLS=1 turns it back on.
    bool onset_cells_ = std::getenv("TCTL_ONSET_CELLS") != nullptr;
    /// Which rolled deadline (Ustopcarry)/(Ustopabut) install.
    ///
    /// The paper's D* is the strict x_mu < (b-a)+1, which is what makes the
    /// abutting cell reachable and (Ustopabut) fire at all.  Measured over the
    /// self-test suite it is *unsound*: it admits a recurrence one cell slower
    /// than the window allows, and AG(AF[1,2] q) & AG(q -> AG(0,1] !q) — whose
    /// witnesses must be at most 1 apart by the rate and more than 1 apart by
    /// the ban, hence UNSAT — comes back SAT.  The closed x_mu <= b-a is right
    /// on every such family and is the default here; it makes the abutting cell
    /// unreachable, so (Ustopabut) becomes dead code.
    ///
    /// TCTL_ROLLED_DEADLINE=strict selects the paper's bound, for measuring the
    /// difference.  See rolled_deadline() and not_track/PAPER_PORT.md.
    bool rolled_strict_ = [] {
        const char* v = std::getenv("TCTL_ROLLED_DEADLINE");
        return v && std::string(v) == "strict";
    }();
    std::uint32_t root_id_ = static_cast<std::uint32_t>(-1);
    std::chrono::steady_clock::time_point deadline_{};

    // ── SCC acceptance state (unused under TCTL_LEGACY_LOOP) ────────────
    /// The explored graph.  A deque, not a vector: it grows by one node per
    /// intern for the whole search, and a vector's doubling copies every GNode
    /// built so far while holding both buffers -- the peak that costs, on the
    /// run that is already the largest.  A deque grows in blocks, never copies,
    /// and keeps references stable across growth.
    std::deque<GNode>                              g_;     // the explored graph
    // ── Key store: one arena plus one open-addressed table ──────────────
    //
    // A key is a run of words in karena_; a node id indexes koff_/klen_/khash_.
    // The unordered_map<vector<uint32_t>, uint32_t> this replaces cost, per
    // node, a map node, a separate heap buffer for the vector *and* a bucket
    // slot -- and `emplace(std::move(k))` moved the build buffer out on every
    // miss, so the hot path malloc'd once per new node just to re-grow it.
    // Here a new key is an append and a lookup is an index.
    std::vector<std::uint32_t> charena_;  // every node's children, back to back
    std::vector<std::uint32_t> uarena_;   // every node's until pursuits
    // The key arena is chunked, not one growing vector.  A vector doubling at
    // 8 MB holds the old and the new buffer at once, so the *peak* is three
    // times the live size for the length of one memcpy -- and peak is what a
    // solver is judged on.  Fixed blocks never copy, and the pointers they hand
    // out stay valid for the life of the search.
    static constexpr std::uint32_t kBlkShift = 16;                  // 64 Ki words
    static constexpr std::uint32_t kBlkWords = 1u << kBlkShift;
    static constexpr std::uint32_t kBlkMask  = kBlkWords - 1;
    std::vector<std::unique_ptr<std::uint32_t[]>> kblocks_;
    std::uint32_t kfill_ = kBlkWords;    // words used in the newest block
    std::vector<std::uint32_t> koff_;     // node id → offset into karena_
    std::vector<std::uint32_t> klen_;     // node id → length in words
    std::vector<std::uint64_t> khash_;    // node id → its hash, kept for rehash
    std::vector<std::uint32_t> ktab_;     // slot → node id + 1; 0 is empty
    std::size_t                kmask_ = 0;
    std::size_t words_ = 1;                                // clock-bitmap width (64-bit)
    std::size_t rw32_  = 1;                                // reset-mask width (32-bit)
    // key-building scratch, reused so the hot path allocates nothing
    mutable std::vector<std::array<std::uint32_t, 2>> pursuit_scratch_;
    mutable std::vector<std::array<std::uint32_t, 2>> deadline_scratch_;
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

// Peak resident size of this process, in bytes.
//
// The field existed and nothing ever wrote it, so --stats never printed a
// memory figure and every harness that read one recorded zero. getrusage
// reports the high-water mark for the whole process, which is what a
// single-formula run wants; the unit differs by platform, bytes on macOS and
// kilobytes on Linux.
static std::uint64_t peak_resident_bytes() {
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) != 0) return 0;
#if defined(__APPLE__)
    return static_cast<std::uint64_t>(ru.ru_maxrss);
#else
    return static_cast<std::uint64_t>(ru.ru_maxrss) * 1024ull;
#endif
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
    if (straddles)         os << " straddles=" << straddles;
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
    const bool v2 = false;                  // v1 branch: never decompose
    if (false) {
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
    stats_.straddles = engine.straddles();
    stats_.peak_memory_bytes = peak_resident_bytes();

    const auto t1 = std::chrono::steady_clock::now();
    return Result(verdict, std::chrono::duration<double>(t1 - t0).count());
}

}  // namespace tctl
