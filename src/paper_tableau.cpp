// ============================================================================
// paper_tableau.cpp — ETAPS2026 cover-rule / launch-pursuit tableau
// ============================================================================
// Scaffolding stage: decides modality-free state predicates via Z3 and returns
// Unsatisfiable for anything temporal.  The full construction (node model,
// saturation, S_X cover, pursuit, successors, marking) is added task-by-task.
// ============================================================================

#include "tctl/paper_tableau.hpp"
#include "tctl/z3_solver.hpp"

#include <sstream>

namespace tctl {

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
