// ============================================================================
// tctl/ast.hpp — Abstract Syntax Tree for tctl formulas
// ============================================================================
//
// Design notes:
//
//   Every tctl formula is represented as a node in an interned DAG.  Two
//   formulas that are structurally identical share the same FormulaId.
//   This allows O(1) equality checks and provides a canonical
//   representation.
//
//   Node types:
//     - Atom      : propositional variable (string label)
//     - True/False: boolean constants
//     - Not       : negation, child[0]
//     - And       : conjunction, child[0] & child[1]
//     - Or        : disjunction, child[0] | child[1]
//     - Implies   : implication child[0] -> child[1]   (pre-NNF only)
//     - Iff       : biconditional child[0] <-> child[1] (pre-NNF only)
//     - EX        : exists-next, child[0]
//     - AX        : forall-next, child[0]
//     - EU        : exists-until, child[0] U child[1]
//     - AU        : forall-until, child[0] U child[1]
//     - ER        : exists-release, child[0] R child[1]
//     - AR        : forall-release, child[0] R child[1]
//     - EF        : exists-finally (sugar, pre-desugar only)
//     - AF        : forall-finally (sugar, pre-desugar only)
//     - EG        : exists-globally (sugar, pre-desugar only)
//     - AG        : forall-globally (sugar, pre-desugar only)
//
//   FormulaFactory owns all nodes and provides the interning mechanism
//   via structural hashing.  Clients receive FormulaId handles.
//
// ============================================================================

#ifndef CTL_AST_HPP
#define CTL_AST_HPP

#include "ptctlmc/dbm_pool.hpp"

#include <cstddef>
#include <cstdint>
#include <deque>
#include <functional>
#include <memory>
#include <shared_mutex>
#include <string>
#include <unordered_map>
#include <vector>
#include <mutex>
namespace tctl {

// ── FormulaId ───────────────────────────────────────────────────────────────
// A lightweight handle into the formula interning table.  The id is an index
// into the FormulaFactory's internal node vector.  The special value
// kInvalidId signals "no formula".
// ─────────────────────────────────────────────────────────────────────────────

using FormulaId = std::uint32_t;
inline constexpr FormulaId kInvalidId = static_cast<FormulaId>(-1);

// ── TimeBound ───────────────────────────────────────────────────────────────
// Represents a time bound with value and strictness.
// strict=false means <= (closed), strict=true means < (open).

struct TimeBound {
    std::int64_t value = 0;
    bool is_strict = false;    // true for < or >, false for <= or >=
    bool is_infinity = false;  // true for unbounded (upper only)
    
    static TimeBound closed(std::int64_t v) { return TimeBound{v, false, false}; }
    static TimeBound open(std::int64_t v) { return TimeBound{v, true, false}; }
    static TimeBound infinity() { return TimeBound{0, false, true}; }
    
    bool operator==(const TimeBound& o) const noexcept {
        if (is_infinity && o.is_infinity) return true;
        if (is_infinity != o.is_infinity) return false;
        return value == o.value && is_strict == o.is_strict;
    }
    
    // For display: returns "(a" or "[a" for lower, "b)" or "b]" for upper
    std::string to_string_lower() const {
        std::string bracket = is_strict ? "(" : "[";
        return bracket + std::to_string(value);
    }
    
    std::string to_string_upper() const {
        if (is_infinity) return "inf)";  // infinity is always open
        std::string bracket = is_strict ? ")" : "]";
        return std::to_string(value) + bracket;
    }
};

// ── UpperBound (legacy, kept for compatibility) ─────────────────────────────
// Represents either a finite integer bound or infinity for TCTL intervals.

struct UpperBound {
    bool is_infinity = false;
    std::int64_t value = 0;  // Only meaningful when is_infinity == false
    
    static UpperBound finite(std::int64_t v) { return UpperBound{false, v}; }
    static UpperBound infinity() { return UpperBound{true, 0}; }
    
    bool operator==(const UpperBound& o) const noexcept {
        if (is_infinity && o.is_infinity) return true;
        if (is_infinity != o.is_infinity) return false;
        return value == o.value;
    }
    
    std::string to_string() const {
        if (is_infinity) return "inf";
        return std::to_string(value);
    }
};

// ── NodeKind ────────────────────────────────────────────────────────────────

enum class NodeKind : std::uint8_t {
    // Constants
    True,
    False,

    // Atoms
    Atom,

    // Boolean connectives
    Not,
    And,
    Or,
    Implies,   // only before implication elimination
    Iff,       // only before biconditional elimination

    // Temporal operators (primitives)
    EX,
    AX,
    EU,
    AU,

    // Temporal operators (sugar — removed by desugaring)
    EF,
    AF,
    EG,
    AG,

    // Release operator (dual of Until — greatest fixpoint)
    ER,         // E(φ R ψ)  — existential release
    AR,         // A(φ R ψ)  — universal release

    // TCTL: Timed temporal operators (canonical — interval form only)
    TimedEU,    // E(φ U[a,b] ψ) with interval [lower, upper]
    TimedAU,    // A(φ U[a,b] ψ) with interval [lower, upper]
    TimedER,    // E(φ R[a,b] ψ) with interval [lower, upper]
    TimedAR,    // A(φ R[a,b] ψ) with interval [lower, upper]

    // TCTL: Timed temporal operators (sugar — desugared to TimedEU/TimedAU)
    TimedEF,    // EF[a,b] φ  →  E(true U[a,b] φ)
    TimedAF,    // AF[a,b] φ  →  A(true U[a,b] φ)
    TimedEG,    // EG[a,b] φ  →  ¬A(true U[a,b] ¬φ)
    TimedAG,    // AG[a,b] φ  →  ¬E(true U[a,b] ¬φ)

    // Integer expressions
    IntVar,     // integer variable
    IntConst,   // integer constant
    IntPlus,    // e1 + e2
    IntMinus,   // e1 - e2
    IntTimes,   // e1 * e2

    // Arithmetic constraints
    IntLessEq,    // e1 <= e2
    IntLess,      // e1 < e2
    IntGreaterEq, // e1 >= e2
    IntGreater,   // e1 > e2
    IntEqual      // e1 = e2
};

/// Human-readable string for a NodeKind.
const char* node_kind_name(NodeKind k) noexcept;

// ── FormulaNode ─────────────────────────────────────────────────────────────
// Immutable stored node.  All data is value-semantics; the FormulaFactory is
// the sole owner.

struct FormulaNode {
    NodeKind    kind{};
    std::string atom_name;       // non-empty for Atom/IntVar nodes
    std::int64_t int_value{0};   // value for IntConst nodes
    FormulaId   children[2]{kInvalidId, kInvalidId};
    
    // TCTL: time interval for timed operators with strictness
    // [a,b] closed-closed, (a,b) open-open, [a,b) closed-open, etc.
    TimeBound   time_lower{};      // lower bound with strictness
    TimeBound   time_upper{};      // upper bound (can be infinity) with strictness

    // Structural-equality (used by the interning table).
    bool operator==(const FormulaNode& o) const noexcept;
};

// ── FormulaNodeHash ─────────────────────────────────────────────────────────
// Hash functor for FormulaNode, combining kind + atom_name + children.

struct FormulaNodeHash {
    std::size_t operator()(const FormulaNode& n) const noexcept;
};

// ── FormulaFactory ──────────────────────────────────────────────────────────
// Thread-safe.  Owns the node storage (std::deque for pointer stability)
// and the interning map.  Every make_*() method returns the canonical
// FormulaId for that structure.  A shared_mutex allows concurrent reads
// (node(), to_string()) while serialising writes (intern/make_*).

class FormulaFactory {
public:
    FormulaFactory();

    /// Identity of this factory, unique for the life of the process.
    ///
    /// FormulaIds are per-factory indices, so anything caching them must be
    /// able to tell two factories apart.  A pointer cannot do that: a factory
    /// is typically a short-lived local, and the next one is very likely to be
    /// allocated at the same address, which would silently validate a stale
    /// cache keyed by the previous factory's ids.
    std::uint64_t serial() const noexcept { return serial_; }

    // ── Constructors ────────────────────────────────────────────────────
    FormulaId make_true();
    FormulaId make_false();
    FormulaId make_atom(const std::string& name);
    FormulaId make_not(FormulaId child);
    FormulaId make_and(FormulaId lhs, FormulaId rhs);
    FormulaId make_or(FormulaId lhs, FormulaId rhs);
    FormulaId make_implies(FormulaId lhs, FormulaId rhs);
    FormulaId make_iff(FormulaId lhs, FormulaId rhs);
    FormulaId make_ex(FormulaId child);
    FormulaId make_ax(FormulaId child);
    FormulaId make_eu(FormulaId lhs, FormulaId rhs);
    FormulaId make_au(FormulaId lhs, FormulaId rhs);
    FormulaId make_er(FormulaId lhs, FormulaId rhs);
    FormulaId make_ar(FormulaId lhs, FormulaId rhs);
    FormulaId make_ef(FormulaId child);
    FormulaId make_af(FormulaId child);
    FormulaId make_eg(FormulaId child);
    FormulaId make_ag(FormulaId child);

    // ── TCTL: Timed temporal operators (canonical) ──────────────────────
    // TimedEU/AU are canonical; TimedEF/AF/EG/AG are sugar.
    // Uses new TimeBound with strictness support.
    FormulaId make_timed_eu(FormulaId lhs, FormulaId rhs, 
                            TimeBound lower, TimeBound upper);
    FormulaId make_timed_au(FormulaId lhs, FormulaId rhs,
                            TimeBound lower, TimeBound upper);
    FormulaId make_timed_er(FormulaId lhs, FormulaId rhs,
                            TimeBound lower, TimeBound upper);
    FormulaId make_timed_ar(FormulaId lhs, FormulaId rhs,
                            TimeBound lower, TimeBound upper);
    
    // ── TCTL: Timed sugar (desugared to timed-until forms) ──────────────
    FormulaId make_timed_ef(FormulaId child, TimeBound lower, TimeBound upper);
    FormulaId make_timed_af(FormulaId child, TimeBound lower, TimeBound upper);
    FormulaId make_timed_eg(FormulaId child, TimeBound lower, TimeBound upper);
    FormulaId make_timed_ag(FormulaId child, TimeBound lower, TimeBound upper);

    // ── Integer expressions ─────────────────────────────────────────────
    FormulaId make_int_var(const std::string& name);
    FormulaId make_int_const(std::int64_t value);
    FormulaId make_int_plus(FormulaId lhs, FormulaId rhs);
    FormulaId make_int_minus(FormulaId lhs, FormulaId rhs);
    FormulaId make_int_times(FormulaId lhs, FormulaId rhs);

    // ── Arithmetic constraints ──────────────────────────────────────────
    FormulaId make_int_less_eq(FormulaId lhs, FormulaId rhs);
    FormulaId make_int_less(FormulaId lhs, FormulaId rhs);
    FormulaId make_int_greater_eq(FormulaId lhs, FormulaId rhs);
    FormulaId make_int_greater(FormulaId lhs, FormulaId rhs);
    FormulaId make_int_equal(FormulaId lhs, FormulaId rhs);

    // ── Accessors ───────────────────────────────────────────────────────
    const FormulaNode& node(FormulaId id) const;
    std::size_t        size() const noexcept;

    // ── Pretty-print ────────────────────────────────────────────────────
    // Returns a fully parenthesised string representation of a formula.
    std::string to_string(FormulaId id) const;

private:
    std::uint64_t serial_;
    // Intern a node: return existing id when structurally equal, otherwise
    // allocate a new slot.  Takes exclusive lock internally.
    FormulaId intern(FormulaNode node);

    // Unlocked accessors — caller must already hold mutex_ (shared or exclusive).
    const FormulaNode& node_unlocked(FormulaId id) const;
    std::string to_string_unlocked(FormulaId id) const;

    mutable std::shared_mutex                                   mutex_;
    std::deque<FormulaNode>                                     nodes_;
    std::unordered_map<FormulaNode, FormulaId, FormulaNodeHash> intern_;
};

// ── FormulaSet ──────────────────────────────────────────────────────────────
// Canonical sorted vector of FormulaIds.  Provides deterministic iteration
// and O(log n) membership.

/// Vector drawn from HDBM's per-thread free list.
///
/// The tableau copies a node on every rule application, and each copy would
/// otherwise cost one malloc per member vector on the process-global allocator
/// lock.  Recycling a pooled buffer is a lock-free pop/push instead.  (The pool
/// is a generic utility that happens to live in the DBM layer.)
template <class T>
using PooledVec = std::vector<T, ptctlmc::PoolAllocator<T>>;

/// Sorted, unique sequence of formula ids.
using FormulaIdVec = PooledVec<FormulaId>;

/// Discard every interned formula set on this thread.
///
/// **Invalidates every existing FormulaSet**: handles are indices into the
/// table this clears, so a FormulaSet built before the call denotes a different
/// set (or none) after it.  Call it only where no FormulaSet is live --- the
/// engine calls it when entering Tableau::check, which is such a point because
/// a set never escapes the check that built it.
///
/// Offered for embedders that check many formulas in one process and want the
/// table bounded.  The engine does not call it: measured on a 480-formula run
/// it cost 40% of the runtime to reclaim 2% of peak RSS, the peak being
/// dominated by the search graph rather than by interned sets.
void reset_formula_sets() noexcept;

/// Generation counter of this thread's interning table, bumped by
/// reset_formula_sets().  Anything caching a FormulaSet::handle() must also
/// record the epoch it cached under and discard its entries when the epoch
/// moves, since handles are reused after a reset.
std::uint64_t formula_set_epoch() noexcept;

class FormulaSet {
public:
    FormulaSet() = default;                      // the empty set

    void insert(FormulaId id);
    bool contains(FormulaId id) const noexcept;
    bool empty() const noexcept;
    std::size_t size() const noexcept;

    const FormulaIdVec& elements() const noexcept;

    /// Build the set from an already sorted, duplicate-free sequence.
    /// One interning step instead of one per element.
    static FormulaSet from_sorted(const FormulaIdVec& sorted);

    /// Rebuild the set denoted by an interned handle.
    ///
    /// Handles are stable for as long as the interning table lives, so a node
    /// key that stores one can be decoded back into the set it came from --
    /// which is what lets the witness extractor recover a node the search has
    /// already discarded.  The handle must come from this thread and predate
    /// any reset_formula_sets().
    static FormulaSet from_handle(std::uint32_t h) noexcept;

    /// The interned identity of this set: equal handles iff equal sets.
    /// Usable directly as a hash-map key, and as a node key's contribution.
    std::uint32_t handle() const noexcept { return h_; }

    bool operator==(const FormulaSet& o) const noexcept { return h_ == o.h_; }
    bool operator!=(const FormulaSet& o) const noexcept { return h_ != o.h_; }
    bool operator<(const FormulaSet& o) const noexcept;

private:
    /// Index into the per-thread interning table; 0 is always the empty set.
    ///
    /// The tableau copies a node -- and hence its three formula sets -- on every
    /// rule application, hashes each node once, and compares sets constantly.
    /// A handle makes the copy a word, the comparison an integer test, and the
    /// set's share of a node key one word instead of |S|.
    ///
    /// A handle is meaningful only on the thread that interned it.  The search
    /// is single-threaded (Tableau::set_num_threads is a documented no-op) and a
    /// FormulaSet never escapes the check() that built it, so none ever crosses
    /// a thread.
    std::uint32_t h_ = 0;
};

}  // namespace tctl

#endif  // CTL_AST_HPP
