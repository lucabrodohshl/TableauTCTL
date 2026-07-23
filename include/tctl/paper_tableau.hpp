// ============================================================================
// tctl/paper_tableau.hpp — ETAPS2026 cover-rule / launch-pursuit tableau
// ============================================================================
//
// Decision procedure of Brodo, Scalora, Henkler, "A Tableau for TCTL"
// (ETAPS 2026, ../../ETAPS2026.pdf).  On-the-fly AND–OR graph over symbolic
// nodes N = <Gamma, X, Z, O, D>; a cover rule discharges each timed modality mu
// against its satisfaction set S_X(mu); acceptance is a marking computed by node
// elimination.  Verdict-first: this returns SAT/UNSAT; witness timed-automaton
// extraction (paper Theorem 2) is a separate, later deliverable.
//
// Fragment (paper §3): TCTL in NNF over  T | F | p | !p | & | | |
//   E(phi U_I psi) | E(phi R_I psi) | A(phi U_I psi) | A(phi R_I psi).
// There is no object-level next; EX/AX arise only as internal pursuit markers.
//
// Z3 is used only as the node closure oracle (arithmetic/propositional leaves);
// it never encodes temporal operators, clocks, or fixpoints.  All clock
// reasoning stays in the DBM / ZoneSet layer.
//
// The public Result / result_to_string API is preserved from the retired engine
// so the self-test (src/test.cpp) and benchmark (src/benchmark.cpp) harnesses
// re-point at this engine with minimal churn.
//
// See docs/superpowers/specs/2026-07-23-tctl-paper-tableau-design.md.
// ============================================================================

#ifndef TCTL_PAPER_TABLEAU_HPP
#define TCTL_PAPER_TABLEAU_HPP

#include "tctl/ast.hpp"

#include <chrono>
#include <cstdint>
#include <string>

namespace tctl {

// ── Result ───────────────────────────────────────────────────────────────────
// Verdict + wall-clock time.  Same public shape as the retired engine's Result
// (Value enum, verdict, elapsed_s, operator==, static aliases) so existing
// call-sites `r == Result::Satisfiable` and `r.elapsed_s` compile unchanged.
struct Result {
    enum class Value { Satisfiable, Unsatisfiable, Timeout };

    Value  verdict   = Value::Unsatisfiable;
    double elapsed_s = 0.0;

    Result() = default;
    Result(Value v, double t = 0.0) : verdict(v), elapsed_s(t) {}

    bool operator==(Value v) const noexcept { return verdict == v; }
    bool operator!=(Value v) const noexcept { return verdict != v; }

    static constexpr Value Satisfiable   = Value::Satisfiable;
    static constexpr Value Unsatisfiable = Value::Unsatisfiable;
    static constexpr Value Timeout       = Value::Timeout;
};

/// "SATISFIABLE" / "UNSATISFIABLE" / "TIMEOUT".
const char* result_to_string(const Result& r) noexcept;

// ── PaperStats ───────────────────────────────────────────────────────────────
// Deterministic, machine-independent counters (search-space proxy).  Fleshed
// out in the graph/acceptance tasks; zero at the scaffolding stage.
struct PaperStats {
    std::uint64_t nodes_created     = 0;
    std::uint64_t distinct_zones    = 0;
    std::uint64_t loop_checks       = 0;
    std::uint64_t peak_memory_bytes = 0;

    void reset() noexcept { *this = PaperStats{}; }
    std::string to_string() const;
};

// ── PaperTableau ─────────────────────────────────────────────────────────────
// The satisfiability engine.  Grows task-by-task; at scaffolding stage it
// decides only modality-free state predicates (via Z3) and returns
// Unsatisfiable for anything temporal.
class PaperTableau {
public:
    explicit PaperTableau(FormulaFactory& factory);

    /// Decide satisfiability of a normalised TCTL formula (measures elapsed_s).
    Result check(FormulaId normalized_formula);

    /// Timeout for the next check() (0 = none).
    void set_timeout(std::chrono::seconds timeout) { timeout_ = timeout; }

    /// Enable/disable ~=_M zone extrapolation.  (No-op until the graph task.)
    void set_extrapolation(bool enable) { extrapolation_ = enable; }

    /// Thread hint.  The paper engine is single-threaded for now; kept so the
    /// benchmark harness compiles.  (No-op.)
    void set_num_threads(int) {}

    const PaperStats& get_stats() const { return stats_; }
    std::string stats() const { return stats_.to_string(); }

private:
    FormulaFactory&      factory_;
    std::chrono::seconds timeout_{0};
    bool                 extrapolation_ = true;
    PaperStats           stats_;
};

}  // namespace tctl

#endif  // TCTL_PAPER_TABLEAU_HPP
