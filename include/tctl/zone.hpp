// ============================================================================
// tctl/zone.hpp — Zone wrapper over HDBM
// ============================================================================
//
// This module provides a C++ wrapper around HDBM (HDBM/include/ptctlmc) for
// handling Difference Bound Matrices (zones) in TCTL model checking.
//
// Zones represent sets of clock valuations satisfying conjunctions of
// constraints of the form:
//   - x <= c      (upper bound on clock x)
//   - x >= c      (lower bound on clock x)
//   - x - y <= c  (difference constraint between clocks x and y)
//
// HDBM is header-only, so every DBM primitive inlines into the call site; at
// the dimensions this engine uses (one clock per timed subformula, so typically
// three to six) that matters more than the asymptotics.
//
// ============================================================================

#ifndef CTL_ZONE_HPP
#define CTL_ZONE_HPP

#include "ptctlmc/dbm_ops.hpp"
#include "ptctlmc/dbm_pool.hpp"

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace tctl {

// ── ClockId ─────────────────────────────────────────────────────────────────
// Identifier for a clock. Clock 0 is reserved as the reference clock (always 0).

using ClockId = std::uint32_t;
inline constexpr ClockId kReferenceClock = 0;

/// DBM entry, encoded as HDBM encodes it: @c (value<<1)|weak, weak=1 for @c <=.
using raw_t = ptctlmc::raw_t;

/// The raw entry standing for an absent upper bound.
inline constexpr raw_t kRawInfinity = ptctlmc::kInf;
/// The bound value @c Bound::infinity() carries; any @c value at or above it is
/// treated as unbounded, so arithmetic never has to special-case the sentinel.
inline constexpr std::int32_t kInfinityBound = ptctlmc::kInf >> 1;

// ── RelOp ───────────────────────────────────────────────────────────────────
// Relational operator for constraints.

enum class RelOp : std::uint8_t {
    LessEq,    // <=
    Less,      // <
    GreaterEq, // >=
    Greater    // >
};

// ── Bound ───────────────────────────────────────────────────────────────────
// Represents a bound value with strictness (for DBM entries).
// Compatible with HDBM's raw_t encoding.

struct Bound {
    std::int32_t value;
    bool is_strict;  // true for <, false for <=
    
    static Bound less_eq(std::int32_t v) { return Bound{v, false}; }
    static Bound less(std::int32_t v) { return Bound{v, true}; }
    static Bound infinity() { return Bound{kInfinityBound, false}; }
    
    bool is_infinity() const { return value >= kInfinityBound; }
    
    bool operator==(const Bound& o) const {
        return value == o.value && is_strict == o.is_strict;
    }
    
    // Convert to HDBM's raw_t encoding
    raw_t to_raw() const {
        if (is_infinity()) return kRawInfinity;
        return is_strict ? ptctlmc::lt(value) : ptctlmc::le(value);
    }
    
    // Create from HDBM's raw_t encoding
    static Bound from_raw(raw_t raw) {
        if (raw >= kRawInfinity) return infinity();
        return Bound{ptctlmc::raw_bound(raw), ptctlmc::raw_is_strict(raw)};
    }
    
    std::string to_string() const;
};

// ── Zone ────────────────────────────────────────────────────────────────────
// Represents a zone (set of clock valuations) using a Difference Bound Matrix.
// Uses HDBM directly for all DBM operations.
//
// The zone maintains a canonical form after each operation.
// The number of clocks is fixed at construction time.

class Zone {
public:
    // ── Factory methods ─────────────────────────────────────────────────
    
    /// Create a universe zone (all non-negative clock valuations).
    /// All clocks >= 0, no upper bounds.
    static Zone universe(std::size_t num_clocks);
    
    /// Create an empty zone (no valuations satisfy the constraints).
    static Zone empty(std::size_t num_clocks);
    
    /// Create a zone where all clocks are zero.
    static Zone zero(std::size_t num_clocks);
    
    // ── Constructors / assignment ───────────────────────────────────────
    
    Zone();
    Zone(const Zone& other);
    Zone(Zone&& other) noexcept;
    Zone& operator=(const Zone& other);
    Zone& operator=(Zone&& other) noexcept;
    ~Zone();
    
    // ── Zone operations ─────────────────────────────────────────────────
    
    /// Return the intersection of this zone with another.
    /// Requires same number of clocks.
    Zone intersect(const Zone& other) const;
    
    /// Check if the zone is empty (no satisfying valuations).
    bool is_empty() const;
    
    /// Check if this zone is a subset of another.
    bool is_subset_of(const Zone& other) const;
    
    /// Add a constraint: clock <= bound (modifies in place)
    void add_upper_bound(ClockId clock, std::int32_t bound, bool strict = false);
    
    /// Add a constraint: clock >= bound (modifies in place)
    void add_lower_bound(ClockId clock, std::int32_t bound, bool strict = false);
    
    /// Add a constraint: clock_x - clock_y <= bound (modifies in place)
    void add_difference_constraint(ClockId clock_x, ClockId clock_y, 
                                   std::int32_t bound, bool strict = false);
    
    /// Reset a clock to zero (modifies in place)
    void reset(ClockId clock);
    
    /// Delay operation: time elapse (modifies in place)
    void delay();
    
    /// Alias for delay()
    void up() { delay(); }
    
    /// Down operation: inverse delay (modifies in place)
    void down();
    
    /// Free a clock (remove all constraints involving it except clock >= 0)
    void free(ClockId clock);
    
    /// Extrapolate using max bounds per clock. Abstracts away clock values
    /// beyond the maximum constant they are compared against, ensuring
    /// finitely many distinct zones. Uses HDBM's dbm_extrapolate (Extra_M).
    /// @param max: array of size num_clocks(), max[0]=0, max[i]=max constant for clock i.
    void extrapolate(const std::vector<std::int32_t>& max);

    /// Extra_LU widening (Behrmann et al.), separating the maximum lower-bound
    /// constant of each clock from its maximum upper-bound one.
    ///
    /// Strictly coarser than #extrapolate, hence fewer distinct zones. Sound
    /// for reachability over the diagonal-free constraints this construction
    /// emits; it does *not* preserve which clocks keep a finite upper bound, so
    /// a caller that needs that must take it from #extrapolate instead.
    /// @param L Per-clock maximum lower-bound constant, @c L[0]==0.
    /// @param U Per-clock maximum upper-bound constant, @c U[0]==0.
    void extrapolate_lu(const std::vector<std::int32_t>& L,
                        const std::vector<std::int32_t>& U);
    
    // ── Accessors ───────────────────────────────────────────────────────
    
    /// Number of clocks (including reference clock 0).
    std::size_t num_clocks() const { return dim_; }

    /// Raw DBM matrix (row-major, dim*dim raw_t entries). Valid only when
    /// !is_empty(); used to bridge to HDBM's Federation / Dbm (see ZoneSet).
    const raw_t* raw_data() const { return dbm_.data(); }

    /// Build a zone from a raw DBM matrix (copies dim*dim entries).
    static Zone from_raw(std::size_t dim, const raw_t* m);

    /// Get the bound for clock_x - clock_y.
    Bound get_bound(ClockId clock_x, ClockId clock_y) const;
    
    /// Pretty-print the zone as a conjunction of constraints.
    std::string to_string() const;
    
    // ── Comparison ──────────────────────────────────────────────────────
    
    bool operator==(const Zone& other) const;
    bool operator!=(const Zone& other) const { return !(*this == other); }
    
private:
    // Dimension (number of clocks including reference)
    std::uint32_t dim_;
    
    // The DBM using HDBM's raw_t format.
    // Size is dim_ * dim_, accessed as dbm_[i * dim_ + j].
    //
    // Zones are copied on every rule application and discarded in the millions,
    // so the buffer is drawn from HDBM's per-thread free list: recycling one is
    // a lock-free pop/push instead of a malloc/free pair on the process-global
    // allocator lock.
    std::vector<raw_t, ptctlmc::PoolAllocator<raw_t>> dbm_;
    
    // Flag indicating if this is the empty zone
    bool empty_;
    
    // Private constructor for internal use
    Zone(std::uint32_t dim, bool is_empty);
};

// ── Zone utilities ──────────────────────────────────────────────────────────

/// Smoke test: verify basic zone operations work correctly.
/// Returns true if all basic operations pass.
bool zone_smoke_test();

}  // namespace tctl

#endif  // CTL_ZONE_HPP
