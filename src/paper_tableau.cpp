// ============================================================================
// paper_tableau.cpp — ETAPS2026 cover-rule / launch-pursuit tableau
// ============================================================================
// Full construction: saturation, cover (S_X), pursuit (U•/R^split/R•), delay +
// EX successors, and a DFS AND–OR search with loop detection whose acceptance
// requires (i) every active until-pursuit discharged around a loop and (ii) the
// loop time-progressing (non-Zeno).  Verdict-first (no witness TA yet).
// ============================================================================

#include "tctl/paper_tableau.hpp"
#include "tctl/satisfaction_set.hpp"
#include "tctl/z3_solver.hpp"
#include "tctl/zoneset.hpp"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <sstream>
#include <string>
#include <unordered_map>
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
    FormulaSet out;
    for (FormulaId id : g.elements())
        if (id != drop) out.insert(id);
    return out;
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
void apply_inv(Zone& z, const std::vector<Deadline>& D) {
    for (const Deadline& d : D)
        z.add_upper_bound(d.x_mu, static_cast<std::int32_t>(d.bound), d.strict);
}
// Remove a deadline on clock x from D.
std::vector<Deadline> drop_deadline(const std::vector<Deadline>& D, ClockId x) {
    std::vector<Deadline> out;
    for (const Deadline& d : D) if (d.x_mu != x) out.push_back(d);
    return out;
}

}  // namespace

// ── Cover rule (paper §4.2) ─────────────────────────────────────────────────

CoverResult apply_cover(const Node& n, FormulaId mu,
                        const std::map<FormulaId, ClockId>& cmap,
                        std::size_t num_clocks,
                        const std::vector<std::int32_t>& max, FormulaFactory& f,
                        SatCache& sx_cache) {
    // A persistent context (e.g. AG μ) re-demands μ at every onset.  Per the
    // paper (Remark 1 / Fig. 2) a single formula-clock x_μ serves all onsets:
    // if μ is already being pursued, do NOT launch a second pursuit — that makes
    // the pursuits set (and thus the node key) grow without bound, so nothing
    // ever memo-collides.  The active pursuit already witnesses μ; just discharge.
    for (const Pursuit& p : n.pursuits) {
        if (p.mu == mu) {
            CoverResult only;
            only.kind = CoverResult::Kind::Cover;
            Node discharge;
            discharge.Gamma = gamma_without(n.Gamma, mu);
            discharge.X = n.X; discharge.Z = n.Z; discharge.O = n.O;
            discharge.D = n.D; discharge.pursuits = n.pursuits; discharge.phase = n.phase;
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
    base.pursuits = n.pursuits; base.phase = n.phase;

    if (SX.contains(Zc)) {
        res.kind = CoverResult::Kind::Cover;
        Node discharge = base;
        Node launch = base;
        if (x_mu != kNoClock) {
            launch.Z.reset(x_mu);
            launch.just_reset.push_back(x_mu);
            launch.O[mu] = x_mu;
        }
        Pursuit p; p.mu = mu; p.x_mu = x_mu;
        p.stage = Pursuit::Stage::Here; p.part = Pursuit::Part::Whole;
        p.is_until = until_kind;
        launch.pursuits.push_back(p);
        if (is_universal(kind) && until_kind) {
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
    Engine(FormulaFactory& f, FormulaId root, double timeout_s)
        : f_(f) {
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

    // Memoisation + boundary-region abstraction keep the search shallow.  The
    // process runs with an enlarged main-thread stack (set via a linker option,
    // see CMakeLists.txt) so deep-but-finite runs do not overflow — no per-check
    // thread and no artificial depth limit.
    bool decide(FormulaId root) {
        Node n;
        n.Gamma.insert(root);
        n.Z = Zone::zero(nc_);
        n.phase = Phase::Elapse;
        return decide_iter(n);
    }

    std::uint64_t nodes() const { return expansions_; }
    bool budget_hit() const { return budget_hit_; }

private:
    // ── Canonical key for loop detection ────────────────────────────────
    // Everything about a node EXCEPT its zone.  Two nodes with the same struct
    // key differ only in their zone, so narrowing-monotonicity (paper §4.1)
    // applies between them: a realisable zone subsumes its sub-zones.
    std::string struct_key(const Node& n) const {
        std::ostringstream os;
        os << 'G';
        for (FormulaId id : n.Gamma.elements()) os << id << ',';
        os << 'X';
        for (FormulaId id : n.X.elements()) os << id << ',';
        os << 'P';
        std::vector<std::string> ps;
        for (const Pursuit& p : n.pursuits) {
            std::ostringstream q;
            q << p.mu << ':' << p.x_mu << ':' << int(p.stage) << ':'
              << int(p.part) << ':' << p.is_until;
            ps.push_back(q.str());
        }
        std::sort(ps.begin(), ps.end());
        for (auto& s : ps) os << s << ';';
        os << 'D';
        std::vector<std::string> ds;
        for (const Deadline& d : n.D) {
            std::ostringstream q; q << d.x_mu << ':' << d.bound << ':' << d.strict;
            ds.push_back(q.str());
        }
        std::sort(ds.begin(), ds.end());
        for (auto& s : ds) os << s << ';';
        os << 'F' << int(n.phase);
        return os.str();
    }

    // The ~=_M-canonical zone used for memo/loop comparison.
    Zone canon_zone(const Node& n) const {
        Zone z = n.Z; z.extrapolate(max_); return z;
    }

    // Full key (struct + canonical zone) for exact loop detection.
    std::string key(const Node& n) const {
        return struct_key(n) + "Z" + canon_zone(n).to_string();
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
                CoverResult cr = apply_cover(n, id, cmap_, nc_, max_, f_, sx_cache_);
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
                    stop.pursuits.erase(stop.pursuits.begin() + static_cast<long>(i));
                    stop.D = drop_deadline(n.D, p.x_mu);
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

    Expansion successors(const Node& n) {
        if (n.phase == Phase::Elapse) {
            // (Delay): single time-successor, capped by Inv(N).  Boundary vs open
            // distinctions are made where a modality's truth is pinned (the U•
            // stop / R^split), via integer_regions, not here.
            Node d = n;
            d.Z.up();
            apply_inv(d.Z, n.D);
            d.Z.extrapolate(max_);
            d.phase = Phase::Discrete;
            d.just_reset.clear();
            if (d.Z.is_empty()) return {Expansion::Kind::Closed, {}};
            return {Expansion::Kind::And, {d}};
        }
        // (EX): one child per DeferEX pursuit; DeferAX carried to all; stutter.
        std::vector<Pursuit> ex, ax;
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
        std::string sk;        // struct key (zone-independent)
        std::string fk;        // full key (struct + canonical zone)
        Zone        ez;        // canonical zone (for memo store)
        Expansion   e;
        std::size_t ci = 0;
        std::size_t depth = 0;
        std::size_t submin = kInf;
        bool        res = false;
        bool        expanded = false;
    };

    // ── Loop acceptance (reads the explicit stack) ──────────────────────
    bool loop_accepting(const std::vector<Frame>& st, std::size_t a) const {
        const Node& rep = st[a].n;
        // (i) every until-pursuit pending on the loop must be discharged on the
        // segment (its (U•) stop taken somewhere): a persistent eventuality is
        // re-launched each cycle, fine as long as it is fulfilled within the loop.
        for (const Pursuit& p : rep.pursuits) {
            if (!p.is_until) continue;
            bool discharged = false;
            for (std::size_t k = a; k < st.size(); ++k)
                if (st[k].n.discharges_until == p.mu) { discharged = true; break; }
            if (!discharged) return false;
        }
        // (ii) time-progressing (non-Zeno): positive elapse and every
        // deadline-bounded clock reset on the segment.
        bool has_delay = false;
        std::vector<char> reset(nc_, 0);
        for (std::size_t k = a; k < st.size(); ++k) {
            if (st[k].n.phase == Phase::Discrete) has_delay = true;
            for (ClockId c : st[k].n.just_reset) if (c < nc_) reset[c] = 1;
        }
        if (!has_delay) return false;
        for (const Deadline& d : rep.D)
            if (d.x_mu < nc_ && !reset[d.x_mu]) return false;
        return true;
    }

    // ── Zone-subsumption memo (narrowing-monotonicity, paper §4.1) ──────
    // Keyed by struct key; a realisable zone subsumes its sub-zones, and an
    // unrealisable zone subsumes its super-zones — so many distinct zones share
    // one stored verdict.  Only self-contained (path-independent) verdicts cached.
    bool memo_lookup(const std::string& sk, const Zone& ez, bool& out) const {
        auto it = memo_.find(sk);
        if (it == memo_.end()) return false;
        for (const auto& e : it->second) {
            if (e.second) { if (ez.is_subset_of(e.first)) { out = true;  return true; } }
            else          { if (e.first.is_subset_of(ez)) { out = false; return true; } }
        }
        return false;
    }
    void memo_store(const std::string& sk, const Zone& ez, bool verdict) {
        memo_[sk].emplace_back(ez, verdict);
    }

    void push_frame(std::vector<Frame>& st, const Node& n) {
        Frame fr;
        fr.n = n;
        fr.sk = struct_key(n);
        fr.ez = canon_zone(n);
        fr.fk = fr.sk + "Z" + fr.ez.to_string();
        st.push_back(std::move(fr));
    }

    // ── Iterative on-the-fly DFS with short-circuiting + memoisation ────
    bool decide_iter(const Node& root) {
        std::vector<Frame> st;
        std::unordered_map<std::string, std::size_t> onpath;  // fk → depth
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
                    pend_res = false; pend_lm = kInf; st.pop_back(); continue;
                }
                if (auto it = onpath.find(fr.fk); it != onpath.end()) {
                    std::size_t a = it->second;
                    pend_res = loop_accepting(st, a); pend_lm = a; st.pop_back(); continue;
                }
                bool cached;
                if (memo_lookup(fr.sk, fr.ez, cached)) {
                    pend_res = cached; pend_lm = kInf; st.pop_back(); continue;
                }
                fr.e = expand(fr.n);
                if (fr.e.kind == Expansion::Kind::Closed) {
                    memo_store(fr.sk, fr.ez, false);
                    pend_res = false; pend_lm = kInf; st.pop_back(); continue;
                }
                fr.expanded = true;
                fr.ci = 0;
                fr.res = (fr.e.kind == Expansion::Kind::And);
                fr.submin = kInf;
                fr.depth = st.size() - 1;
                onpath.emplace(fr.fk, fr.depth);
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
            if (self_contained) memo_store(fr.sk, fr.ez, fr.res);
            onpath.erase(fr.fk);
            pend_res = fr.res;
            pend_lm  = self_contained ? kInf : fr.submin;
            st.pop_back();
        }
        return pend_res;
    }

    FormulaFactory& f_;
    ClockMap cmap_;
    std::size_t nc_ = 1;
    std::vector<std::int32_t> max_;
    std::vector<std::int32_t> bounds_;   // sorted formula interval endpoints (+0)

    // struct key → list of (canonical zone, verdict) for subsumption lookup
    std::unordered_map<std::string, std::vector<std::pair<Zone, bool>>> memo_;
    SatCache sx_cache_;                  // persistent S_X(mu,X) memo
    std::uint64_t expansions_ = 0;
    bool budget_hit_ = false;
    bool has_deadline_ = false;
    std::chrono::steady_clock::time_point deadline_{};
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

std::string PaperStats::to_string() const {
    std::ostringstream os;
    os << "nodes=" << nodes_created << " distinct_zones=" << distinct_zones
       << " loop_checks=" << loop_checks
       << " peak_mem_kb=" << (peak_memory_bytes + 1023) / 1024;
    return os.str();
}

PaperTableau::PaperTableau(FormulaFactory& factory) : factory_(factory) {}

Result PaperTableau::check(FormulaId normalized_formula) {
    stats_.reset();
    const auto t0 = std::chrono::steady_clock::now();

    Engine engine(factory_, normalized_formula,
                  static_cast<double>(timeout_.count()));
    bool sat = engine.decide(normalized_formula);

    Result::Value verdict;
    if (engine.budget_hit())      verdict = Result::Value::Timeout;
    else if (sat)                 verdict = Result::Value::Satisfiable;
    else                          verdict = Result::Value::Unsatisfiable;

    stats_.nodes_created = engine.nodes();

    const auto t1 = std::chrono::steady_clock::now();
    return Result(verdict, std::chrono::duration<double>(t1 - t0).count());
}

}  // namespace tctl
