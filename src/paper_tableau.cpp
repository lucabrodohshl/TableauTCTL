// ============================================================================
// paper_tableau.cpp — ETAPS2026 cover-rule / launch-pursuit tableau
// ============================================================================
// Scaffolding stage: decides modality-free state predicates via Z3 and returns
// Unsatisfiable for anything temporal.  The full construction (node model,
// saturation, S_X cover, pursuit, successors, marking) is added task-by-task.
// ============================================================================

#include "tctl/paper_tableau.hpp"
#include "tctl/satisfaction_set.hpp"
#include "tctl/z3_solver.hpp"
#include "tctl/zoneset.hpp"

#include <sstream>

namespace tctl {

namespace {

bool is_until_modality(NodeKind k) noexcept {
    return k == NodeKind::EU || k == NodeKind::AU ||
           k == NodeKind::TimedEU || k == NodeKind::TimedAU;
}
bool is_universal_until(NodeKind k) noexcept {
    return k == NodeKind::AU || k == NodeKind::TimedAU;
}

// Build Gamma without a specific formula id.
FormulaSet gamma_without(const FormulaSet& g, FormulaId drop) {
    FormulaSet out;
    for (FormulaId id : g.elements())
        if (id != drop) out.insert(id);
    return out;
}

}  // namespace

CoverResult apply_cover(const Node& n, FormulaId mu, FormulaFactory& f) {
    ClockId x_mu = 0; std::size_t nc = 0;
    ZoneSet SX = satisfaction_set(mu, n.X, f, &x_mu, &nc);

    // Demand at the onset: the node's zone with x_mu pinned to 0.
    Zone Zc = n.Z;
    Zc.add_lower_bound(x_mu, 0, false);
    Zc.add_upper_bound(x_mu, 0, false);

    CoverResult res;
    if (Zc.is_empty()) { res.kind = CoverResult::Kind::Close; return res; }

    // Common base of both children: Gamma without mu.
    const NodeKind kind = f.node(mu).kind;
    const bool until_kind = is_until_modality(kind);
    Node base;
    base.Gamma    = gamma_without(n.Gamma, mu);
    base.X        = n.X;
    base.Z        = n.Z;
    base.O        = n.O;
    base.D        = n.D;
    base.pursuits = n.pursuits;

    if (SX.contains(Zc)) {
        // ── Full cover: AND of discharge and launch ──────────────────────
        res.kind = CoverResult::Kind::Cover;
        Node discharge = base;                    // drop mu, continue
        Node launch    = base;                    // launch mu•
        launch.Z.reset(x_mu);                     // x_mu := 0
        launch.O[mu] = x_mu;
        Pursuit p;
        p.mu = mu; p.x_mu = x_mu;
        p.stage = Pursuit::Stage::Here;
        p.part  = Pursuit::Part::Whole;
        p.is_until = until_kind;
        launch.pursuits.push_back(p);
        // Deadline D_mu = {(x_mu, sup I)} iff mu is a universal until.
        if (is_universal_until(kind)) {
            const FormulaNode& mn = f.node(mu);
            if (!mn.time_upper.is_infinity) {
                launch.D.push_back(Deadline{x_mu, mn.time_upper.value,
                                            mn.time_upper.is_strict});
            }
        }
        res.children.push_back(std::move(discharge));
        res.children.push_back(std::move(launch));
        return res;
    }

    // Partial or close: examine Z ∩ S_X(mu).
    ZoneSet inter = ZoneSet::of(Zc);
    inter.intersect(SX);
    if (inter.is_empty()) { res.kind = CoverResult::Kind::Close; return res; }

    // ── Partial cover: one OR-child per convex component ─────────────────
    res.kind = CoverResult::Kind::PartialCover;
    for (const Zone& comp : inter.components()) {
        Node child = base;
        child.Gamma = n.Gamma;   // keep mu; re-demand on the narrowed zone
        child.Z     = comp;
        res.children.push_back(std::move(child));
    }
    return res;
}

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

    Result::Value verdict = Result::Value::Unsatisfiable;

    // A modality-free state predicate is satisfiable iff its leaves are
    // Z3-consistent.  add_state_formula() returns false when the formula
    // contains temporal operators, in which case we cannot yet decide it.
    Z3Checker z3(factory_);
    if (z3.add_state_formula(normalized_formula)) {
        verdict = (z3.check() == Z3Result::SAT) ? Result::Value::Satisfiable
                                                : Result::Value::Unsatisfiable;
    }
    // else: temporal formula — full construction not yet implemented.

    const auto t1 = std::chrono::steady_clock::now();
    const double elapsed =
        std::chrono::duration<double>(t1 - t0).count();
    return Result(verdict, elapsed);
}

}  // namespace tctl
