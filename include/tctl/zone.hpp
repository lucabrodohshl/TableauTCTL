// ============================================================================
// tctl/zone.hpp — Zone wrapper for UPPAAL UDBM
// ============================================================================
//
// This module provides a C++ wrapper around the UPPAAL UDBM library
// for handling Difference Bound Matrices (zones) in TCTL model checking.
//
// Zones represent sets of clock valuations satisfying conjunctions of
// constraints of the form:
//   - x <= c      (upper bound on clock x)
//   - x >= c      (lower bound on clock x)
//   - x - y <= c  (difference constraint between clocks x and y)
//
// This implementation uses the UDBM library directly.
//
// ============================================================================

#ifndef CTL_ZONE_HPP
#define CTL_ZONE_HPP

#include <dbm/dbm.h>
#include <dbm/constraints.h>

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace tctl {

// ── ClockId ─────────────────────────────────────────────────────────────────
// Identifier for a clock. Clock 0 is reserved as the reference clock (always 0).

using ClockId = cindex_t;
inline constexpr ClockId kReferenceClock = 0;

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
// Compatible with UDBM's raw_t encoding.

struct Bound {
    std::int32_t value;
    bool is_strict;  // true for <, false for <=
    
    static Bound less_eq(std::int32_t v) { return Bound{v, false}; }
    static Bound less(std::int32_t v) { return Bound{v, true}; }
    static Bound infinity() { return Bound{dbm_INFINITY, false}; }
    
    bool is_infinity() const { return value == dbm_INFINITY; }
    
    bool operator==(const Bound& o) const {
        return value == o.value && is_strict == o.is_strict;
    }
    
    // Convert to UDBM's raw_t encoding
    raw_t to_raw() const {
        if (is_infinity()) return dbm_LS_INFINITY;
        return dbm_boundbool2raw(value, is_strict);
    }
    
    // Create from UDBM's raw_t encoding
    static Bound from_raw(raw_t raw) {
        if (raw >= dbm_LS_INFINITY) return infinity();
        return Bound{dbm_raw2bound(raw), (raw & 1) == dbm_STRICT};
    }
    
    std::string to_string() const;
};

// ── Zone ────────────────────────────────────────────────────────────────────
// Represents a zone (set of clock valuations) using a Difference Bound Matrix.
// Uses UDBM library directly for all DBM operations.
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
    /// finitely many distinct zones. Uses UDBM's dbm_extrapolateMaxBounds.
    /// @param max: array of size num_clocks(), max[0]=0, max[i]=max constant for clock i.
    void extrapolate(const std::vector<std::int32_t>& max);
    
    // ── Accessors ───────────────────────────────────────────────────────
    
    /// Number of clocks (including reference clock 0).
    std::size_t num_clocks() const { return dim_; }
    
    /// Get the bound for clock_x - clock_y.
    Bound get_bound(ClockId clock_x, ClockId clock_y) const;
    
    /// Pretty-print the zone as a conjunction of constraints.
    std::string to_string() const;
    
    // ── Comparison ──────────────────────────────────────────────────────
    
    bool operator==(const Zone& other) const;
    bool operator!=(const Zone& other) const { return !(*this == other); }
    
private:
    // Dimension (number of clocks including reference)
    cindex_t dim_;
    
    // The DBM using UDBM's raw_t format
    // Size is dim_ * dim_, accessed as dbm_[i * dim_ + j]
    std::vector<raw_t> dbm_;
    
    // Flag indicating if this is the empty zone
    bool empty_;
    
    // Private constructor for internal use
    Zone(cindex_t dim, bool is_empty);
};

// ── Zone utilities ──────────────────────────────────────────────────────────

/// Smoke test: verify basic zone operations work correctly.
/// Returns true if all basic operations pass.
bool zone_smoke_test();

}  // namespace tctl

#endif  // CTL_ZONE_HPP
