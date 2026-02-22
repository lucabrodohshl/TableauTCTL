// ============================================================================
// tctl/tableau.hpp — One-Pass Context-Based tctl Tableau Engine
// ============================================================================
//
// Implementation of the tctl tableau satisfiability algorithm based on
// Abuin et al., TIME 2020 one-pass context-based tableaux for tctl.
//
// Architecture Overview:
// ─────────────────────
// - Each tableau node represents a sequent Γ with an associated Context.
// - The Context carries universal obligations (AX formulas) that must hold
//   in all successor states.
// - Nodes are memoized by their canonical (Γ, contextKey) pair.
// - The search is depth-first with backtracking over OR nodes.
// - Loop detection ensures termination; eventuality checking validates loops.
//
// Allowed Operators (after NNF):
// ─────────────────────────────
//   Literals: p, !p (atoms only)
//   Boolean:  &, |
//   Temporal: EX φ, AX φ, E(φ U ψ), A(φ U ψ)
//
// Z3 Usage (RESTRICTED):
// ─────────────────────
// Z3 may ONLY be used to check propositional consistency of literals in Γ.
// Z3 must NOT encode tctl semantics, temporal operators, or fixpoints.
//
// ============================================================================

#ifndef CTL_TABLEAU_HPP
#define CTL_TABLEAU_HPP

#include "tctl/ast.hpp"
#include "tctl/z3_solver.hpp"
#include "tctl/zone.hpp"

#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace tctl {

// ── Result ──────────────────────────────────────────────────────────────────
//
// A Result captures both the satisfiability verdict and the wall-clock time
// (in seconds) taken by the tableau engine for that check.

struct Result {
    /// The satisfiability verdict.
    enum class Value { Satisfiable, Unsatisfiable, Timeout };

    Value  verdict   = Value::Unsatisfiable;
    double elapsed_s = 0.0;

    // Construction.
    Result() = default;
    Result(Value v, double t = 0.0) : verdict(v), elapsed_s(t) {}

    // Comparison against a bare Value so existing `r == Result::Satisfiable`
    // call-sites compile without modification.
    bool operator==(Value v) const noexcept { return verdict == v; }
    bool operator!=(Value v) const noexcept { return verdict != v; }

    // Static aliases that replicate the old enum-value names.
    static constexpr Value Satisfiable   = Value::Satisfiable;
    static constexpr Value Unsatisfiable = Value::Unsatisfiable;
    static constexpr Value Timeout       = Value::Timeout;
};

/// Convert a Result to a display string ("SATISFIABLE" / "UNSATISFIABLE" / "TIMEOUT").
const char* result_to_string(const Result& r) noexcept;

// ── NodeStatus ──────────────────────────────────────────────────────────────
// Status of a tableau node during the search.

enum class NodeStatus : std::uint8_t {
    Unknown,    // Not yet fully explored
    Open,       // Successfully expanded; branch is satisfiable
    Closed      // Contradiction or all children closed
};

// ── NodeKind ────────────────────────────────────────────────────────────────
// Whether a node requires ALL children to be open (AND) or ANY child (OR).

enum class TableauNodeKind : std::uint8_t {
    AND,        // All children must be Open for this node to be Open
    OR          // At least one child must be Open for this node to be Open
};

// ── Context ─────────────────────────────────────────────────────────────────
// Carries the universal obligations that must be propagated to all successors.
// "nextAll" is a sorted vector of FormulaIds representing the formulas that
// must hold in every successor state (derived from AX obligations).

struct Context {
    std::vector<FormulaId> nextAll;  // Sorted, unique

    bool operator==(const Context& o) const noexcept {
        return nextAll == o.nextAll;
    }

    bool operator<(const Context& o) const noexcept {
        return nextAll < o.nextAll;
    }

    // Add a formula to nextAll (maintains sorted order).
    void add_next_all(FormulaId id);

    // Merge another context's nextAll into this one.
    void merge(const Context& other);
};

// ── ContextHash ─────────────────────────────────────────────────────────────

struct ContextHash {
    std::size_t operator()(const Context& ctx) const noexcept;
};

// ── TableauNode ─────────────────────────────────────────────────────────────
// A node in the tableau tree.
//
// Fields:
//   gamma    - The canonical sorted set of formula IDs at this node.
//   ctx      - The context carrying AX obligations.
//   kind     - AND or OR (determines how children affect this node's status).
//   status   - Current status of this node.
//   children - Pointers to child nodes.
//   parent   - Pointer to parent node (for ancestor tracking).
//   depth    - Depth in the tree (for statistics and loop detection).
//   id       - Unique identifier for this node.

struct TableauNode {
    FormulaSet              gamma;
    Context                 ctx;
    TableauNodeKind         kind = TableauNodeKind::AND;
    NodeStatus              status = NodeStatus::Unknown;
    std::vector<TableauNode*> children;
    TableauNode*            parent = nullptr;
    std::uint32_t           depth = 0;
    std::uint32_t           id = 0;

    // ── Active eventualities tracking ───────────────────────────────────
    // For loop detection: track which E(φ U ψ) and A(φ U ψ) are "active"
    // (i.e., the GO branch was taken and the eventuality not yet fulfilled).
    std::set<FormulaId> active_eventualities;

    // ── TCTL zone and timed-until tracking ──────────────────────────────
    Zone                    zone;            // DBM over clocks
    std::set<FormulaId>     active_timed;    // active timed-until formula ids
    std::set<FormulaId>     committed_timed; // timed release formulas whose ψ
                                             // has been checked via IN-FORBID

    // ── Edge metadata for TA extraction ─────────────────────────────────
    bool                    is_delay_successor = false;  // true if created by delay rule
    std::vector<ClockId>    clock_resets;                 // clocks reset when creating this node

    // Check if this node is an ancestor of another (for loop detection).
    bool is_ancestor_of(const TableauNode* other) const;
};

// ── NodeKey ─────────────────────────────────────────────────────────────────
// Key for memoization: (Γ, context).

struct NodeKey {
    FormulaSet gamma;
    Context    ctx;
    std::string zone_canonical;  // canonical zone string for TCTL

    bool operator==(const NodeKey& o) const noexcept {
        return gamma == o.gamma && ctx == o.ctx && zone_canonical == o.zone_canonical;
    }

    bool operator<(const NodeKey& o) const noexcept {
        if (gamma < o.gamma) return true;
        if (o.gamma < gamma) return false;
        if (ctx < o.ctx) return true;
        if (o.ctx < ctx) return false;
        return zone_canonical < o.zone_canonical;
    }
};

struct NodeKeyHash {
    std::size_t operator()(const NodeKey& key) const noexcept;
};

// ── KripkeState ─────────────────────────────────────────────────────────────
// A state in the extracted Kripke model.

struct KripkeState {
    std::uint32_t             id;
    std::set<std::string>     atoms;       // Positive atoms in this state
    std::vector<std::uint32_t> successors;
};

// ── KripkeModel ─────────────────────────────────────────────────────────────
// The finite Kripke structure extracted from a satisfying branch.

struct KripkeModel {
    std::vector<KripkeState> states;
    std::uint32_t            initial_state = 0;

    std::string to_string() const;
    std::string to_json()   const;
    std::string to_dot()    const;
};

// ── Statistics ──────────────────────────────────────────────────────────────
// Counters are std::atomic so that concurrent DFS threads can safely
// increment them without external locking.

struct TableauStats {
    std::atomic<std::uint32_t> nodes_created{0};
    std::atomic<std::uint32_t> nodes_closed{0};
    std::atomic<std::uint32_t> nodes_open{0};
    std::atomic<std::uint32_t> max_depth{0};
    std::atomic<std::uint32_t> memo_hits{0};
    std::atomic<std::uint32_t> loop_checks{0};
    std::atomic<std::uint32_t> eventualities_checked{0};

    /// Reset all counters to zero.
    void reset() noexcept {
        nodes_created = 0; nodes_closed = 0; nodes_open = 0;
        max_depth = 0; memo_hits = 0; loop_checks = 0;
        eventualities_checked = 0;
    }

    /// Atomically update max_depth if d is larger.
    void update_max_depth(std::uint32_t d) noexcept {
        std::uint32_t cur = max_depth.load(std::memory_order_relaxed);
        while (d > cur && !max_depth.compare_exchange_weak(
                              cur, d, std::memory_order_relaxed)) {}
    }

    std::string to_string() const;
};

// ── BranchState ─────────────────────────────────────────────────────────────
// Thread-local / branch-local DFS state that must NOT be shared across
// threads.  Each child task gets its own copy so that loop detection
// (ancestor matching) remains correct.

struct BranchState {
    std::vector<TableauNode*>          stack;   // ancestor stack (DFS path)
    std::unordered_set<TableauNode*>   set;     // O(1) membership check

    void push(TableauNode* n) { stack.push_back(n); set.insert(n); }
    void pop(TableauNode* n)  { stack.pop_back();    set.erase(n); }
    bool contains(TableauNode* n) const { return set.count(n) > 0; }
};

// ── MemoEntry ───────────────────────────────────────────────────────────────
// Value stored in the memo table.  The atomic status lets concurrent
// readers fast-return without holding a lock.
//    0 = Unknown  (exploration in progress by some thread)
//    1 = Open     (SAT)
//    2 = Closed   (UNSAT)

struct MemoEntry {
    std::atomic<int> status{0};   // 0=Unknown, 1=Open, 2=Closed

    static constexpr int kUnknown = 0;
    static constexpr int kOpen    = 1;
    static constexpr int kClosed  = 2;
};

// ── TableauEngine ───────────────────────────────────────────────────────────
// The main tctl tableau satisfiability engine.
//
// Algorithm:
//   1. Start with initial node containing the input formula.
//   2. Apply expansion rules (∧, ∨, EU, AU, AX) until saturated.
//   3. Generate successors using EX formulas and context.
//   4. Use DFS with backtracking; memoize nodes.
//   5. Detect loops via ancestor tracking.
//   6. Validate loops by checking eventuality coverage.
//   7. Close nodes that have contradictions or unfulfilled eventualities.

class TableauEngine {
public:
    explicit TableauEngine(FormulaFactory& factory);
    ~TableauEngine();

    // Non-copyable, non-movable (owns node memory).
    TableauEngine(const TableauEngine&) = delete;
    TableauEngine& operator=(const TableauEngine&) = delete;

    /// Check satisfiability of a normalised tctl formula.
    Result check(FormulaId normalized_formula);

    /// Set a timeout for the next check() call.
    /// A value of 0 means no timeout (default).
    void set_timeout(std::chrono::seconds timeout) {
        timeout_ = timeout;
    }

    /// Set the maximum number of OpenMP threads (0 = OMP default).
    void set_num_threads(int n) { num_threads_ = n; }

    /// Set the minimum depth at which parallelism is allowed.
    /// Below this depth tasks are spawned; above, sequential.
    void set_par_depth_limit(int d) { par_depth_limit_ = d; }

    // ── TCTL clock allocation ───────────────────────────────────────────
    std::unordered_map<FormulaId, ClockId> clock_of_;
    std::size_t num_clocks_ = 1;  // including reference clock 0
    std::vector<std::int32_t> max_constants_;

    /// If the last check() returned Satisfiable, return the model.
    std::string model_description() const;

    /// Return statistics about the last run.
    std::string stats() const;

    /// Enable/disable model extraction.
    void set_extract_model(bool enable) { extract_model_ = enable; }

    /// Expose the extracted model (if any) for serialisation.
    const std::optional<KripkeModel>& get_model() const { return model_; }

    /// Expose internal data for TA extraction (read-only).
    const std::vector<std::unique_ptr<TableauNode>>& nodes() const { return nodes_; }
    FormulaFactory& factory() const { return factory_; }

private:
    // ── Node allocation (thread-safe) ───────────────────────────────────
    TableauNode* alloc_node();

    // ── Core expansion ──────────────────────────────────────────────────
    bool expand_node(TableauNode* node);

    // ── Contradiction checking ──────────────────────────────────────────
    bool has_contradiction(TableauNode* node);

    // ── Successor generation ────────────────────────────────────────────
    void generate_successors(TableauNode* node);

    // ── DFS search (branch-local state) ─────────────────────────────────
    // BranchState holds the ancestor stack/set for loop detection.
    // Each OpenMP task gets its own copy, ensuring correctness.
    bool dfs(TableauNode* node, BranchState& bs);

    // ── Loop detection and eventuality checking ─────────────────────────
    TableauNode* find_loop_ancestor(TableauNode* node, const BranchState& bs);

    bool check_eventuality_coverage(TableauNode* loop_start,
                                    TableauNode* loop_end);

    void collect_eventualities(const FormulaSet& gamma,
                               std::set<FormulaId>& eventualities) const;

    bool eventuality_fulfilled(FormulaId eventuality,
                               const FormulaSet& gamma) const;

    // ── TCTL helpers ────────────────────────────────────────────────────
    void allocate_clocks(FormulaId formula);

    bool apply_interval(Zone& zone, ClockId clock,
                        const TimeBound& lower, const TimeBound& upper);

    bool timed_eventuality_fulfilled(FormulaId eventuality,
                                     const TableauNode* node) const;

    bool check_deadline_feasibility(const Zone& zone,
                                    const std::set<FormulaId>& active_timed);

    static std::string zone_canonical_string(const Zone& zone);

    // ── Compute the normalized zone key for memo / loop detection ───────
    std::string compute_zone_key(const TableauNode* node) const;

    // ── Model extraction (thread-safe) ──────────────────────────────────
    void extract_model_from_branch(TableauNode* leaf);

    // ── Helpers ─────────────────────────────────────────────────────────
    FormulaId get_negation(FormulaId id);
    bool is_literal(FormulaId id) const;
    bool is_atom(FormulaId id) const;

    // ── Data members ────────────────────────────────────────────────────
    FormulaFactory& factory_;

    // All allocated nodes (for cleanup).  Protected by alloc_mutex_.
    std::vector<std::unique_ptr<TableauNode>> nodes_;
    std::mutex alloc_mutex_;

    // ── Concurrent memo table ───────────────────────────────────────────
    // Maps (Γ, ctx, zone_key) → MemoEntry with atomic status.
    // Protected by a striped-lock scheme: 64 mutexes, selected by
    // hash(key) % 64.  Locks are held only for find/insert, never
    // during DFS recursion.
    static constexpr std::size_t kMemoStripes = 64;
    std::array<std::mutex, kMemoStripes> memo_locks_;
    std::map<NodeKey, std::shared_ptr<MemoEntry>> memo_;

    std::size_t memo_stripe(const NodeKey& key) const {
        return NodeKeyHash{}(key) % kMemoStripes;
    }

    // ── Early termination ───────────────────────────────────────────────
    // Set to true when any OR child finds SAT.  Checked by other threads
    // to short-circuit remaining work.
    std::atomic<bool> stop_{false};

    // Statistics (atomic counters — thread-safe).
    TableauStats stats_;

    // Extracted model (if satisfiable).
    std::optional<KripkeModel> model_;
    std::mutex model_mutex_;
    std::atomic<bool> model_set_{false};

    // Configuration.
    bool extract_model_ = false;

    // Timeout.
    std::chrono::seconds timeout_{0};
    std::chrono::steady_clock::time_point deadline_;
    std::atomic<bool> timed_out_{false};

    // Next node ID (atomic for thread safety).
    std::atomic<std::uint32_t> next_node_id_{0};

    // OpenMP configuration.
    int num_threads_ = 0;        // 0 = OMP default
    int par_depth_limit_ = 64;   // only spawn tasks at depth < limit
};

}  // namespace tctl

#endif  // CTL_TABLEAU_HPP
