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
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <string>
#include <unordered_map>

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

// Z ∩ (x_mu ∈ I), in place.
void constrain_in_window(Zone& z, ClockId x, const Window& w) {
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
                        const std::vector<std::int32_t>& max, FormulaFactory& f) {
    ZoneSet SX = satisfaction_set(mu, n.X, cmap, num_clocks, max, f);
    const ClockId x_mu = cmap.at(mu);

    // Onset: the launch resets x_mu, so start measuring the window now by
    // *resetting* x_mu (not intersecting with x_mu=0 — the clock may already
    // carry a value from an earlier, discharged launch of the same mu).
    Zone Zc = n.Z;
    Zc.reset(x_mu);

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
        launch.Z.reset(x_mu);
        launch.just_reset.push_back(x_mu);
        launch.O[mu] = x_mu;
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
    Engine(FormulaFactory& f, FormulaId root)
        : f_(f) {
        cmap_ = assign_clocks(root, f);
        nc_ = 1 + cmap_.size();
        std::int32_t M = max_constant(root, f);
        max_.assign(nc_, M);
        max_[0] = 0;
        debug_ = std::getenv("TCTL_DEBUG") != nullptr;
    }

    bool decide(FormulaId root) {
        Node n;
        n.Gamma.insert(root);
        n.Z = Zone::zero(nc_);
        n.phase = Phase::Elapse;
        return dfs(n);
    }

    std::uint64_t nodes() const { return nodes_; }
    bool budget_hit() const { return budget_hit_; }

private:
    // ── Canonical key for loop detection ────────────────────────────────
    std::string key(const Node& n) const {
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
        os << 'F' << int(n.phase) << 'Z';
        Zone z = n.Z; z.extrapolate(max_);
        os << z.to_string();
        return os.str();
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
                CoverResult cr = apply_cover(n, id, cmap_, nc_, max_, f_);
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
            // (U•): stop ⊕ go.
            Node stop = n;
            stop.Gamma.insert(psi);
            constrain_in_window(stop.Z, p.x_mu, w);
            stop.pursuits.erase(stop.pursuits.begin() + static_cast<long>(i));
            stop.D = drop_deadline(n.D, p.x_mu);
            stop.discharges_until = p.mu;   // until eventuality fulfilled here

            Node go = n;
            go.Gamma.insert(phi);
            go.pursuits[i].stage = defer;
            return {Expansion::Kind::Or, {stop, go}};
        }

        // Release.
        if (p.part == Pursuit::Part::Whole) {
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

    Expansion successors(const Node& n) {
        if (n.phase == Phase::Elapse) {
            // (Delay): single time-successor, capped by Inv(N).
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
        auto make_child = [&](const Pursuit* ex_one) {
            Node c;
            c.X = n.X;
            c.Gamma = n.X;             // {ψ} ∪ X base
            c.Z = n.Z; c.O = n.O; c.D = n.D; c.phase = Phase::Elapse;
            if (ex_one) { Pursuit q = *ex_one; q.stage = Pursuit::Stage::Here;
                          c.pursuits.push_back(q); }
            for (Pursuit q : ax) { q.stage = Pursuit::Stage::Here; c.pursuits.push_back(q); }
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

    // ── Loop acceptance ─────────────────────────────────────────────────
    bool loop_accepting(std::size_t a) const {
        const Node& rep = path_[a].node;
        // (i) every until-pursuit pending on the loop must be *discharged*
        // somewhere on the segment (its (U•) stop taken).  A persistent
        // eventuality is re-launched each cycle, so "pending at the repeat" is
        // fine as long as it is fulfilled within the loop.
        for (const Pursuit& p : rep.pursuits) {
            if (!p.is_until) continue;
            bool discharged = false;
            for (std::size_t k = a; k < path_.size(); ++k)
                if (path_[k].node.discharges_until == p.mu) { discharged = true; break; }
            if (!discharged) return false;
        }
        // (ii) time-progressing (non-Zeno)
        return time_progressing(a);
    }

    bool time_progressing(std::size_t a) const {
        // A delay step must occur on the segment.
        bool has_delay = false;
        std::vector<char> reset(nc_, 0);
        for (std::size_t k = a; k < path_.size(); ++k) {
            if (path_[k].node.phase == Phase::Discrete) has_delay = true;
            for (ClockId c : path_[k].node.just_reset)
                if (c < nc_) reset[c] = 1;
        }
        if (nc_ == 1) return has_delay || true;  // no clocks ⇒ time diverges freely
        // Every clock with a finite upper bound in rep.Z must be reset on segment.
        const Node& rep = path_[a].node;
        for (ClockId c = 1; c < nc_; ++c) {
            Bound b = rep.Z.get_bound(c, kReferenceClock);  // c - 0 ≤ b
            if (!b.is_infinity() && !reset[c]) return false;  // bounded & never reset
        }
        return has_delay;
    }

    // ── DFS ─────────────────────────────────────────────────────────────
    bool dfs(const Node& n) {
        if (++nodes_ > kBudget) { budget_hit_ = true; return false; }
        if (node_closed(n.Gamma, f_) || n.Z.is_empty()) {
            trace(n, "CLOSED");
            return false;
        }

        std::string k = key(n);
        for (std::size_t a = 0; a < path_.size(); ++a)
            if (path_[a].key == k) {
                bool acc = loop_accepting(a);
                trace(n, acc ? "LOOP+" : "LOOP-");
                return acc;
            }

        Expansion e = expand(n);
        if (e.kind == Expansion::Kind::Closed) { trace(n, "close"); return false; }

        trace(n, e.kind == Expansion::Kind::And ? "AND" : "OR");
        path_.push_back({k, n});
        ++depth_;
        bool res;
        if (e.kind == Expansion::Kind::And) {
            res = true;
            for (const Node& c : e.children) if (!dfs(c)) { res = false; break; }
        } else {  // Or
            res = false;
            for (const Node& c : e.children) if (dfs(c)) { res = true; break; }
        }
        --depth_;
        path_.pop_back();
        return res;
    }

    void trace(const Node& n, const char* tag) const {
        if (!debug_) return;
        std::ostringstream os;
        for (int i = 0; i < depth_; ++i) os << ' ';
        os << tag << " G{";
        for (FormulaId id : n.Gamma.elements()) os << f_.to_string(id) << ',';
        os << "} P{";
        for (const Pursuit& p : n.pursuits)
            os << f_.to_string(p.mu) << "/x" << p.x_mu << "/s" << int(p.stage)
               << "/pt" << int(p.part) << (p.is_until ? "U" : "R") << ' ';
        os << "} ph" << int(n.phase) << " Z=" << n.Z.to_string() << '\n';
        std::fputs(os.str().c_str(), stderr);
    }

    static constexpr std::uint64_t kBudget = 300000;

    FormulaFactory& f_;
    ClockMap cmap_;
    std::size_t nc_ = 1;
    std::vector<std::int32_t> max_;

    struct Frame { std::string key; Node node; };
    std::vector<Frame> path_;
    std::uint64_t nodes_ = 0;
    bool budget_hit_ = false;
    bool debug_ = false;
    int depth_ = 0;
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

    Engine engine(factory_, normalized_formula);
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
