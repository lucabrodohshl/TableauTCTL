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
#include "tctl/zone.hpp"

#include <chrono>
#include <cstdint>
#include <map>
#include <string>
#include <vector>

namespace tctl {

// ── Node model (paper §4.1) ──────────────────────────────────────────────────
// N = <Gamma, X, Z, O, D> plus the pursuit state.

// A deadline (x_mu, bound, strict) contributes  x_mu <= bound  (strict: <) to
// Inv(N) = AND over D.  Applied only for a universal until (paper §4.2 p.6).
struct Deadline {
    ClockId       x_mu;
    std::int64_t  bound;
    bool          strict;

    bool operator==(const Deadline& o) const noexcept {
        return x_mu == o.x_mu && bound == o.bound && strict == o.strict;
    }
    bool operator<(const Deadline& o) const noexcept {
        if (x_mu != o.x_mu)   return x_mu < o.x_mu;
        if (bound != o.bound) return bound < o.bound;
        return strict < o.strict;
    }
};

// A launched pursuit mu•.  `stage` is the current proof-theoretic marker
// (mu• here / EXmu• / AXmu•); `part` is the R^split region being pursued
// (Whole for an until).  Condition (i) of acceptance applies to until pursuits.
struct Pursuit {
    FormulaId mu;           // launched modality Q(phi o_I psi)
    ClockId   x_mu;         // its formula-clock (also a key in O)
    enum class Stage : std::uint8_t { Here, DeferEX, DeferAX } stage = Stage::Here;
    enum class Part  : std::uint8_t { Whole, BeforeI, InI }   part  = Part::Whole;
    bool      is_until = true;   // true → until (acceptance condition (i) applies)

    bool operator==(const Pursuit& o) const noexcept {
        return mu == o.mu && x_mu == o.x_mu && stage == o.stage &&
               part == o.part && is_until == o.is_until;
    }
    bool operator<(const Pursuit& o) const noexcept {
        if (mu != o.mu)       return mu < o.mu;
        if (x_mu != o.x_mu)   return x_mu < o.x_mu;
        if (stage != o.stage) return stage < o.stage;
        if (part != o.part)   return part < o.part;
        return is_until < o.is_until;
    }
};

// Successor phase: an Elapse node lets time pass (Delay rule), a Discrete node
// takes the discrete step (EX rule).  Alternating them lets a launched clock
// x_mu grow into its window before the pursuit's stop is tested.
enum class Phase : std::uint8_t { Elapse, Discrete };

// A tableau node.  Pursuit markers live in `pursuits` (not as synthetic AST
// nodes in Gamma) so the EX/AX residual and R-region stay explicit.
struct Node {
    FormulaSet                    Gamma;     // goal formulas + literals
    FormulaSet                    X;         // universal context (AX obligations)
    Zone                          Z;         // canonical ~=_M-extrapolated DBM
    std::map<FormulaId, ClockId>  O;         // launched mu ↦ x_mu
    std::vector<Deadline>         D;         // ⇒ Inv(N) = AND x_mu </<= bound
    std::vector<Pursuit>          pursuits;  // active mu• (stage / part)
    Phase                         phase = Phase::Elapse;
    std::vector<ClockId>          just_reset;  // clocks reset creating this node
                                               // (metadata; excluded from node key)
    FormulaId                     discharges_until = kInvalidId;
                                  // set on a (U•) stop child: the until mu it
                                  // discharges here (metadata; excluded from key)
};

// ── Cover rule result (paper §4.2) ──────────────────────────────────────────
// Classifying a demanded modality mu against S_X(mu):
//   Cover        — Z ⊆ S_X(mu): children = {discharge, launch} (an AND).
//   PartialCover — Z ∩ S_X(mu) ≠ ∅ but ⊄: children = one narrowed OR-child per
//                  convex component of Z ∩ S_X(mu).
//   Close        — Z ∩ S_X(mu) = ∅: no children.
struct CoverResult {
    enum class Kind { Cover, PartialCover, Close };
    Kind              kind = Kind::Close;
    std::vector<Node> children;
};

// Apply the cover rule to node `n` for the demanded modality `mu`, using the
// engine's global clock map / dimension / extrapolation vector (so `n.Z` and
// S_X(mu) share one clock space).  The onset is taken at x_mu = 0.
CoverResult apply_cover(const Node& n, FormulaId mu,
                        const std::map<FormulaId, ClockId>& cmap,
                        std::size_t num_clocks,
                        const std::vector<std::int32_t>& max, FormulaFactory& f);

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
