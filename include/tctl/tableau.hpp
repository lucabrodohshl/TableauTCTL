/// @file tableau.hpp
/// @brief Tableau decision procedure for TCTL satisfiability.
///
/// Implements the calculus of L. Brodo, G. Scalora and S. Henkler,
/// *A Tableau for TCTL*: an on-the-fly, zone-based proof search that explores
/// only the demanded part of the symbolic state space.
///
/// The search builds an AND–OR graph over symbolic nodes
/// @f$N = \langle \Gamma, X, Z, O, D \rangle@f$ (§4.1) and looks for a
/// successful marking.  Four groups of rules drive it (§4.2):
///
/// - **saturation** decomposes the goals in @f$\Gamma@f$;
/// - the **cover rule** discharges a demanded timed modality @f$\mu@f$ against
///   its satisfaction set @f$S_X(\mu)@f$ (see satisfaction_set.hpp);
/// - the **pursuit rules** unfold a launched modality one step at a time;
/// - **successor generation** expands a saturated node in time (Delay) and
///   across edges (EX).
///
/// A marking is successful when it contains no closed node and every candidate
/// loop in it is accepting: every until pursuit active at the loop head is
/// discharged on the segment, and the loop is time-progressing, which excludes
/// Zeno witnesses (§4.3).
///
/// **Fragment.** TCTL in negation normal form (§3):
/// @f$\top \mid \bot \mid p \mid \neg p \mid \varphi \wedge \varphi \mid
/// \varphi \vee \varphi \mid E(\varphi U_I \varphi) \mid E(\varphi R_I \varphi)
/// \mid A(\varphi U_I \varphi) \mid A(\varphi R_I \varphi)@f$.
/// The logic has no object-level next operator; the @c EX and @c AX markers used
/// below are proof-theoretic and internal to the construction.
///
/// **Guarantees.** Sound and terminating for all of TCTL; complete over the
/// non-punctual fragment, where the procedure runs in ExpTime (§5).
///
/// **Division of labour.** All clock reasoning stays in the DBM and ZoneSet
/// layer (zone.hpp, zoneset.hpp).  An SMT solver is consulted only as the node
/// closure oracle for propositional and arithmetic leaves; it never encodes
/// temporal operators, clocks or fixpoints.
///
/// The procedure is verdict-first: it decides SAT/UNSAT.  Extraction of the
/// witness timed automaton (§5, Theorem 2) is not part of this interface.

#ifndef TCTL_TABLEAU_HPP
#define TCTL_TABLEAU_HPP

#include "tctl/ast.hpp"
#include "tctl/satisfaction_set.hpp"
#include "tctl/timed_automaton.hpp"
#include "tctl/zone.hpp"

#include <chrono>
#include <cstdlib>
#include <cstdint>
#include <map>
#include <utility>
#include <string>
#include <vector>

namespace tctl {

// ─── Node model (§4.1) ──────────────────────────────────────────────────────

/// @brief A deadline @f$(x_\mu, \sup I)@f$ contributing to the node invariant.
///
/// Every deadline in a node's set @f$D@f$ contributes one conjunct
/// @f$x_\mu \leq b@f$ (strictly @f$<@f$ when #strict) to
/// @f$Inv(N) = \bigwedge_{(x_\mu,b) \in D} x_\mu \leq b@f$, which bounds how
/// long time may elapse in the node.
///
/// A deadline is issued only for a universal until: that modality obliges every
/// run to satisfy its target within the window, so time must be forced forward
/// or a run could idle past the window with the eventuality unmet.  An
/// existential until is discharged by a single witnessing run, and a release of
/// either quantifier is discharged by lapsing past its window rather than by
/// acting within it, so neither needs one (§4.2).
struct Deadline {
    ClockId      x_mu;    ///< The formula-clock the deadline bounds.
    std::int64_t bound;   ///< The bound @f$\sup I@f$.
    bool         strict;  ///< @c true for @f$x_\mu < b@f$, @c false for @f$\leq@f$.

    bool operator==(const Deadline& o) const noexcept {
        return x_mu == o.x_mu && bound == o.bound && strict == o.strict;
    }
    bool operator<(const Deadline& o) const noexcept {
        if (x_mu != o.x_mu)   return x_mu < o.x_mu;
        if (bound != o.bound) return bound < o.bound;
        return strict < o.strict;
    }
};

/// @brief A launched pursuit @f$\mu^\bullet@f$ of a timed modality.
///
/// The cover rule launches a pursuit to unfold @f$\mu@f$ in search of a witness,
/// measuring its window from the demanding configuration via the dedicated
/// formula-clock #x_mu.  Pursuits are held in a node's own list rather than as
/// synthetic formulas in @f$\Gamma@f$, which keeps the EX/AX residual and the
/// release region explicit.
struct Pursuit {
    /// Where the pursuit stands relative to the current node.
    enum class Stage : std::uint8_t {
        Here,      ///< @f$\mu^\bullet@f$ — to be unfolded at this node.
        DeferEX,   ///< @f$EX\,\mu^\bullet@f$ — residual carried to one successor.
        DeferAX    ///< @f$AX\,\mu^\bullet@f$ — residual carried to all successors.
    };
    FormulaId mu;                    ///< The launched modality @f$Q(\varphi \circ_I \psi)@f$.
    ClockId   x_mu;                  ///< Its formula-clock; also a key in @f$O@f$.
    /// @brief The onset clock @f$y_\mu@f$: time since the demand was last raised.
    ///
    /// Reset at launch and again by every absorbed re-demand, so it measures the
    /// age of the newest onset the pursuit owes an answer to.  A witness answers
    /// every onset at or before @f$w - \inf I@f$, so a persistent pursuit may
    /// stop at a witness exactly when @f$y_\mu \geq \inf I@f$ -- nothing has been
    /// demanded since.  Without it the recurrence would be eternal, and
    /// @f$AG_{[0,5]}AF_{[1,2]}q \wedge AG_{[8,\infty)}\neg q@f$, which is
    /// satisfiable, would be rejected.  #kNoClock for an existential modality,
    /// which is never absorbed.
    ClockId   y_mu = kNoClock;
    Stage     stage = Stage::Here;   ///< Current proof-theoretic marker.
    bool      is_until = true;       ///< Until pursuits are subject to loop condition (i).
    /// @brief The demand is *persistent*: it is re-issued at every configuration.
    ///
    /// Set when the duplicate-pursuit guard discharges a re-demand of @f$\mu@f$
    /// against this live pursuit.  A persistent demand is not one deadline but a
    /// **recurrence rate** -- a witness at least every @f$\sup I - \inf I@f$ --
    /// which a clock measuring a single onset cannot express.  So a persistent
    /// until is not retired by its (U-stop): the clock is reset, the deadline
    /// kept, and the pursuit continues, turning @f$x_\mu@f$ into "time since the
    /// last witness".  Only set when @f$\inf I = 0@f$, where that bound
    /// coincides with @f$\sup I@f$; see not_track/SATISFACTION_SET_X.md.
    bool      persistent = false;
    /// @brief The pursuit has rolled over at least once.
    ///
    /// After a rollover @f$x_\mu@f$ measures time since the *last witness*, not
    /// since an onset, so the guard it is tested against is the recurrence
    /// window @f$[0,\sup I-\inf I]@f$ rather than @f$I@f$ itself.  Restarting on
    /// @f$I@f$ would admit gaps up to @f$\sup I@f$ where the semantics allows
    /// only @f$\sup I-\inf I@f$.
    bool      rolled = false;

    bool operator==(const Pursuit& o) const noexcept {
        return mu == o.mu && x_mu == o.x_mu && y_mu == o.y_mu &&
               stage == o.stage &&
               is_until == o.is_until &&
               persistent == o.persistent && rolled == o.rolled;
    }
    bool operator<(const Pursuit& o) const noexcept {
        if (mu != o.mu)       return mu < o.mu;
        if (x_mu != o.x_mu)   return x_mu < o.x_mu;
        if (y_mu != o.y_mu)   return y_mu < o.y_mu;
        if (stage != o.stage) return stage < o.stage;
        if (persistent != o.persistent) return persistent < o.persistent;
        if (rolled != o.rolled) return rolled < o.rolled;
        return is_until < o.is_until;
    }
};

/// @brief The invariant a saturated node's location will carry (Inv).
///
/// A saturated node first chooses how long its location may be occupied, then
/// expands.  The choice is disjunctive and the two alternatives are the cell
/// below the next integer hyperplane and the cell up to and including it; an
/// invariant only bounds occupancy, so a run leaving the location at once, or
/// mid-cell, is admitted by either.  Recording the choice on the node is what
/// gives the extracted automaton a well-defined invariant per location.
enum class Inv : std::uint8_t {
    Unset,   ///< Not yet chosen: (Inv) is due.
    Below,   ///< @f$x < k@f$ — the location is left before the hyperplane.
    Upto,    ///< @f$x \le k@f$ — the hyperplane may be reached.
    /// @brief @f$x \le \nu(x)@f$ — the location is occupied only at this instant.
    ///
    /// Offered only where the zone already pins an active clock on one of its
    /// own change points, so the bound is an integer and the invariant is a
    /// legitimate clock constraint.  Both other branches measure @f$k@f$ from
    /// the *next* change point and so admit a positive elapse; neither can say
    /// "the run leaves at once".  A witness that must be produced at a specific
    /// instant needs exactly that: @f$E(true\,U_{[2,2]}\,p)@f$ reaches
    /// @f$x = 2@f$, and since (Delay) is conjunctive the node must admit every
    /// elapse its invariant permits — but the window closes at 2, so any elapse
    /// past it closes the delay child and takes the instant down with it.
    Stay
};

/// @brief A tableau node @f$\langle \Gamma, \Ctx, Z, D, Inv \rangle@f$ (§4.1).
///
/// A node carries the formulas to be realised at a configuration.  It is
/// *closed* when its propositional part is inconsistent or its zone is empty,
/// and *saturated* when no saturation or cover rule applies; only saturated
/// nodes generate successors.
struct Node {
    FormulaSet                   Gamma;      ///< @f$\Gamma@f$: goal formulas and literals.
    FormulaSet                   X;          ///< @f$X@f$: context holding at every successor.
    Zone                         Z;          ///< @f$Z@f$: the node's clock valuations, canonical modulo @f$\cong_M@f$.
    PooledVec<Deadline>          D;          ///< @f$D@f$: deadlines inducing @f$Inv(N)@f$.
    PooledVec<Pursuit>           pursuits;   ///< Active pursuits @f$\mu^\bullet@f$.
    Inv                          inv = Inv::Unset;  ///< Invariant chosen for this location.
    /// @brief The node is an *interval witness*: its zone is a crossing whose
    /// every position carries the asserted goals.
    ///
    /// Set by the abutment stop, whose witness is an interval rather than an
    /// instant.  A release launched at such a node whose window opens at zero
    /// bans within the very crossing that asserts it --- a position later in
    /// the cell lies inside the window of one earlier in it --- so its body is
    /// asserted here rather than deferred.
    bool                         interval_witness = false;
    /// True when this node was produced by (Delay), i.e. time elapsed to reach
    /// it.  Read by the loop test, which needs to know that a cycle crosses a
    /// delay to call it time-progressing.
    bool                         delayed_here = false;

    /// Clocks reset on the edge that created this node.
    /// Diagnostic metadata for the loop test; excluded from the node key.
    PooledVec<ClockId> just_reset;


    /// On a (U•) stop child, the until it discharges here.
    /// Diagnostic metadata; excluded from the node key.
    FormulaId discharges_until = kInvalidId;
};

// ─── Cover rule (§4.2) ──────────────────────────────────────────────────────

/// @brief Outcome of testing a demanded modality against its satisfaction set.
///
/// A node that demands @f$\mu@f$ must show that @f$\mu@f$ holds at *every*
/// valuation of its zone.  Because the window is measured from the demanding
/// configuration, a persistent context such as @f$AG\,\mu@f$ would issue a
/// demand at uncountably many configurations; the rule instead tests the zone
/// symbolically against @f$S_X(\mu)@f$.
struct CoverResult {
    /// How the zone sits relative to @f$S_X(\mu)@f$.
    enum class Kind {
        /// @f$Z \subseteq S_X(\mu)@f$ — rule (Cov) applies.  Children
        /// are an AND of the *discharge*, which drops @f$\mu@f$ so the node can
        /// continue with the rest of @f$\Gamma@f$, and the *launch*, which
        /// starts a pursuit of @f$\mu@f$ on a fresh formula-clock.
        Cover,
        /// The node is closed.
        Close
    };

    Kind              kind = Kind::Close;  ///< Which of the three cases applies.
    std::vector<Node> children;            ///< Resulting children; empty for #Kind::Close.
};

/// @brief Apply the cover rule to @p n for the demanded modality @p mu.
///
/// @param n           The node demanding @p mu.
/// @param mu          The demanded timed modality.
/// @param cmap        Clock map assigning a formula-clock to each modality; must
///                    be the engine-wide map, so that @c n.Z and
///                    @f$S_X(\mu)@f$ share one clock space.
/// @param num_clocks  Dimension of that clock space, including the reference clock.
/// @param max         Per-clock extrapolation bounds.
/// @param f           Formula factory owning @p mu.
/// @param sx_cache    Memo for satisfaction sets, shared across cover sites.
/// @return The classification and the resulting children.
///
/// The onset is taken at @f$x_\mu = 0@f$: the launch resets the formula-clock,
/// so the window is measured from this configuration onward.
CoverResult apply_cover(const Node& n, FormulaId mu, bool ag_context,
                        const std::map<FormulaId, ClockId>& cmap,
                        const std::map<FormulaId, ClockId>& ymap,
                        std::size_t num_clocks,
                        const std::vector<std::int32_t>& max, FormulaFactory& f,
                        SatCache& sx_cache);

// ─── Result ─────────────────────────────────────────────────────────────────

/// @brief Verdict of a satisfiability check, with the wall-clock time it took.
struct Result {
    /// The three possible outcomes of a check.
    enum class Value {
        Satisfiable,    ///< A witness timed automaton exists.
        Unsatisfiable,  ///< No timed automaton satisfies the formula.
        Timeout         ///< The configured time budget was exhausted first.
    };

    Value  verdict   = Value::Unsatisfiable;  ///< The outcome.
    double elapsed_s = 0.0;                   ///< Wall-clock seconds spent deciding.

    Result() = default;
    Result(Value v, double t = 0.0) : verdict(v), elapsed_s(t) {}

    bool operator==(Value v) const noexcept { return verdict == v; }
    bool operator!=(Value v) const noexcept { return verdict != v; }

    static constexpr Value Satisfiable   = Value::Satisfiable;
    static constexpr Value Unsatisfiable = Value::Unsatisfiable;
    static constexpr Value Timeout       = Value::Timeout;
};

/// @brief Render a verdict as @c "SATISFIABLE", @c "UNSATISFIABLE" or @c "TIMEOUT".
/// @param r The result to render.
/// @return A static, null-terminated string; never @c nullptr.
const char* result_to_string(const Result& r) noexcept;

// ─── Statistics ─────────────────────────────────────────────────────────────

/// @brief Deterministic search counters, usable as a machine-independent proxy
///        for the size of the explored search space.
struct SearchStats {
    std::uint64_t nodes_created     = 0;  ///< Node expansions performed.
    std::uint64_t distinct_zones    = 0;  ///< Distinct @f$\cong_M@f$-zones encountered.
    std::uint64_t loop_checks       = 0;  ///< Candidate loops tested for acceptance.
    std::uint64_t peak_memory_bytes = 0;  ///< Peak resident size observed.
    /// @brief Zones that straddled a release window.
    ///
    /// Delay cuts each clock at the constants the rules read, and a release's
    /// endpoints are among them, so a zone should lie wholly before, wholly
    /// inside or wholly beyond its window.  This counts the times that failed
    /// and the partition rule had to fire; it should stay at zero.
    std::uint64_t straddles = 0;

    /// Reset every counter to zero.
    void reset() noexcept { *this = SearchStats{}; }

    /// @brief Format the counters as a single @c key=value line.
    std::string to_string() const;
};

// ─── Engine ─────────────────────────────────────────────────────────────────

/// @brief The TCTL satisfiability engine.
///
/// Typical use:
/// @code
/// tctl::Tableau engine(factory);
/// engine.set_timeout(std::chrono::seconds{30});
/// const tctl::Result r = engine.check(normalise(phi, factory));
/// if (r == tctl::Result::Satisfiable) { /* ... */ }
/// @endcode
///
/// The formula passed to #check must already be in negation normal form over the
/// fragment of §3; see normalization.hpp.
class Tableau {
public:
    /// @brief Construct an engine over @p factory.
    /// @param factory Owns every formula the engine will see, including those it
    ///                builds while unfolding.  Must outlive the engine.
    explicit Tableau(FormulaFactory& factory);

    /// @brief Decide satisfiability of a normalised TCTL formula.
    /// @param normalized_formula The formula, in negation normal form.
    /// @return The verdict, together with the elapsed wall-clock time.  A
    ///         Result::Timeout verdict means the budget set by #set_timeout ran
    ///         out; it is not a claim about satisfiability.
    Result check(FormulaId normalized_formula);

    /// @brief Which set of search optimisations to run.
    ///
    /// @c V1 is the search as it stood before the decomposition work: every
    /// optional optimisation off.  It is the baseline a comparison is made
    /// against, not a different calculus --- both versions decide the same
    /// language and, on every instance measured, return the same verdicts.
    ///
    /// @c V2 adds the two forms of component decomposition and goal
    /// subsumption.  It is not available on this branch: the CLI rejects
    /// @c --version @c v2, and the search always runs @c V1.  V2 lives on the
    /// @c v2 branch.
    enum class Version { V1, V2 };

    /// @brief Select the optimisation set.  See #Version.
    void set_version(Version v) { version_ = v; }

    /// @brief The optimisation set in force.
    Version version() const { return version_; }

    /// @brief Set the time budget for subsequent calls to #check.
    /// @param timeout The budget; zero disables the limit.
    void set_timeout(std::chrono::seconds timeout) { timeout_ = timeout; }

    /// @brief Enable or disable @f$\cong_M@f$ zone extrapolation.
    /// @param enable Whether to extrapolate.
    ///
    /// Extrapolation is what keeps the set of reachable zones finite, so
    /// disabling it forfeits the termination guarantee.  Provided for the
    /// ablation runs of the benchmark harness.
    void set_extrapolation(bool enable) { extrapolation_ = enable; }

    /// @brief Accepted for interface compatibility with the benchmark harness.
    ///
    /// The search is single-threaded, so this is a no-op.
    void set_num_threads(int) {}

    /// @brief Ask #check to read a witness automaton off the successful
    ///        marking (paper Theorem 2).
    ///
    /// Off by default: extraction walks the finished graph and decodes the
    /// nodes it needs, which costs nothing when it is not wanted.
    void set_extract_witness(bool enable) { extract_witness_ = enable; }

    /// @brief Whether the last #check produced a witness.
    bool has_witness() const { return has_witness_; }

    /// @brief The witness automaton of the last satisfiable #check.
    /// @pre #has_witness returns @c true.
    const TimedAutomaton& witness() const { return witness_; }

    /// @brief Counters gathered during the most recent #check.
    const SearchStats& get_stats() const { return stats_; }

    /// @brief Those counters, formatted as one line.
    std::string stats() const { return stats_.to_string(); }

private:
    FormulaFactory&      factory_;
    std::chrono::seconds timeout_{0};
    bool                 extrapolation_ = true;
    bool                 extract_witness_ = false;
    bool                 has_witness_ = false;
    TimedAutomaton       witness_;
    SearchStats          stats_;
    /// TCTL_VERSION=2 selects v2 without the CLI, so the self-test can be run
    /// end to end under it.
    Version              version_ = [] {
        const char* v = std::getenv("TCTL_VERSION");
        return (v && std::string(v) == "2") ? Version::V2 : Version::V1;
    }();
    /// Split a top-level conjunction into atom-disjoint groups and solve each.
    bool                 decompose_ = std::getenv("TCTL_DECOMPOSE") != nullptr;
    /// CEGAR over the onset-shift cut points, under v2.  TCTL_CEGAR=0 disables.
    /// CEGAR over the onset-shift cut points, under v2.  **Off by default**:
    /// measured, the abstraction is only ~2x cheaper on the unsatisfiable
    /// instances it decides, while costing a whole extra search on every
    /// satisfiable one, so it is a net loss on the current mix.  See
    /// docs/CEGAR.md.  TCTL_CEGAR=1 enables it.
    bool                 cegar_ = [] {
        const char* v = std::getenv("TCTL_CEGAR");
        return v && std::string(v) != "0";
    }();
    /// Node budget for the CEGAR abstraction; 0 disables the cap.
    std::uint64_t        cegar_cap_ = [] {
        const char* v = std::getenv("TCTL_CEGAR_CAP");
        return v ? std::strtoull(v, nullptr, 10) : 4000ull;
    }();
};

}  // namespace tctl

#endif  // TCTL_TABLEAU_HPP
