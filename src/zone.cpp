// ============================================================================
// zone.cpp — Zone implementation using UPPAAL UDBM
// ============================================================================
//
// This file provides the Zone class implementation using the UPPAAL UDBM
// library for Difference Bound Matrix operations.
//
// ============================================================================

#include "tctl/zone.hpp"

#include <dbm/dbm.h>
#include <dbm/constraints.h>

#include <algorithm>
#include <cassert>
#include <sstream>

namespace tctl {

// ── Bound ───────────────────────────────────────────────────────────────────

std::string Bound::to_string() const {
    if (is_infinity()) {
        return "∞";
    }
    std::string op = is_strict ? "<" : "<=";
    return op + std::to_string(value);
}

// ── Zone: Constructors ──────────────────────────────────────────────────────

Zone::Zone() : dim_(0), empty_(true) {}

Zone::Zone(cindex_t dim, bool is_empty) 
    : dim_(dim), dbm_(static_cast<size_t>(dim) * dim), empty_(is_empty) {}

Zone::Zone(const Zone& other)
    : dim_(other.dim_), dbm_(other.dbm_), empty_(other.empty_) {}

Zone::Zone(Zone&& other) noexcept
    : dim_(other.dim_), dbm_(std::move(other.dbm_)), empty_(other.empty_) {
    other.dim_ = 0;
    other.empty_ = true;
}

Zone& Zone::operator=(const Zone& other) {
    if (this != &other) {
        dim_ = other.dim_;
        dbm_ = other.dbm_;
        empty_ = other.empty_;
    }
    return *this;
}

Zone& Zone::operator=(Zone&& other) noexcept {
    if (this != &other) {
        dim_ = other.dim_;
        dbm_ = std::move(other.dbm_);
        empty_ = other.empty_;
        other.dim_ = 0;
        other.empty_ = true;
    }
    return *this;
}

Zone::~Zone() = default;

// ── Zone: Factory methods ───────────────────────────────────────────────────

Zone Zone::universe(std::size_t num_clocks) {
    assert(num_clocks > 0);
    Zone z(static_cast<cindex_t>(num_clocks), false);
    
    // Use UDBM's dbm_init to create a universe DBM
    // dbm_init sets: diagonal to <= 0, first row to <= 0 (if CLOCKS_POSITIVE),
    // everything else to < infinity
    dbm_init(z.dbm_.data(), z.dim_);
    
    return z;
}

Zone Zone::empty(std::size_t num_clocks) {
    assert(num_clocks > 0);
    Zone z(static_cast<cindex_t>(num_clocks), true);
    // DBM content doesn't matter for empty zones
    return z;
}

Zone Zone::zero(std::size_t num_clocks) {
    assert(num_clocks > 0);
    Zone z(static_cast<cindex_t>(num_clocks), false);
    
    // Use UDBM's dbm_zero to create a zone with all clocks = 0
    dbm_zero(z.dbm_.data(), z.dim_);
    
    return z;
}

// ── Zone: Operations ────────────────────────────────────────────────────────

Zone Zone::intersect(const Zone& other) const {
    assert(dim_ == other.dim_);
    
    if (empty_ || other.empty_) {
        return Zone::empty(dim_);
    }
    
    Zone result = *this;
    
    // Use UDBM's dbm_intersection
    // Returns true if result is non-empty
    bool non_empty = dbm_intersection(result.dbm_.data(), other.dbm_.data(), dim_);
    
    if (!non_empty) {
        return Zone::empty(dim_);
    }
    
    return result;
}

bool Zone::is_empty() const {
    if (empty_) return true;
    
    // Check diagonal for negative values (inconsistent zone)
    for (cindex_t i = 0; i < dim_; ++i) {
        raw_t diag = dbm_[i * dim_ + i];
        // If diagonal entry is negative or strict-zero, zone is empty
        if (diag < dbm_LE_ZERO) {
            return true;
        }
    }
    
    return false;
}

bool Zone::is_subset_of(const Zone& other) const {
    assert(dim_ == other.dim_);
    
    if (empty_) return true;
    if (other.empty_) return false;
    
    // This <= other iff for all entries, this.dbm[i][j] <= other.dbm[i][j]
    // In UDBM encoding, smaller raw values are tighter bounds
    for (std::size_t i = 0; i < static_cast<std::size_t>(dim_) * dim_; ++i) {
        if (dbm_[i] > other.dbm_[i]) {
            return false;
        }
    }
    
    return true;
}

void Zone::add_upper_bound(ClockId clock, std::int32_t bound, bool strict) {
    if (empty_) return;
    assert(clock < dim_);
    
    // Constraint: x_clock - x_0 <= bound (or <)
    // This means clock <= bound since x_0 = 0
    raw_t constraint = dbm_boundbool2raw(bound, strict);
    
    bool non_empty = dbm_constrain1(dbm_.data(), dim_, clock, 0, constraint);
    if (!non_empty) {
        empty_ = true;
    }
}

void Zone::add_lower_bound(ClockId clock, std::int32_t bound, bool strict) {
    if (empty_) return;
    assert(clock < dim_);
    
    // Constraint: x_0 - x_clock <= -bound (or <)
    // This means clock >= bound since x_0 = 0
    raw_t constraint = dbm_boundbool2raw(-bound, strict);
    
    bool non_empty = dbm_constrain1(dbm_.data(), dim_, 0, clock, constraint);
    if (!non_empty) {
        empty_ = true;
    }
}

void Zone::add_difference_constraint(ClockId clock_x, ClockId clock_y,
                                      std::int32_t bound, bool strict) {
    if (empty_) return;
    assert(clock_x < dim_ && clock_y < dim_);
    
    // Constraint: x_clock_x - x_clock_y <= bound (or <)
    raw_t constraint = dbm_boundbool2raw(bound, strict);
    
    bool non_empty = dbm_constrain1(dbm_.data(), dim_, clock_x, clock_y, constraint);
    if (!non_empty) {
        empty_ = true;
    }
}

void Zone::reset(ClockId clock) {
    if (empty_) return;
    assert(clock > 0 && clock < dim_);  // Can't reset reference clock
    
    // Use UDBM's dbm_updateValue to reset clock to 0
    dbm_updateValue(dbm_.data(), dim_, clock, 0);
}

void Zone::delay() {
    if (empty_) return;
    
    // Use UDBM's dbm_up for delay operation
    dbm_up(dbm_.data(), dim_);
}

void Zone::down() {
    if (empty_) return;
    
    // Use UDBM's dbm_down for inverse delay
    dbm_down(dbm_.data(), dim_);
}

void Zone::free(ClockId clock) {
    if (empty_) return;
    assert(clock > 0 && clock < dim_);  // Can't free reference clock
    
    // Use UDBM's dbm_freeClock to free the clock
    dbm_freeClock(dbm_.data(), dim_, clock);
}

void Zone::extrapolate(const std::vector<std::int32_t>& max) {
    if (empty_) return;
    assert(max.size() == static_cast<std::size_t>(dim_));
    dbm_extrapolateMaxBounds(dbm_.data(), dim_, max.data());
}

// ── Zone: Accessors ─────────────────────────────────────────────────────────

Bound Zone::get_bound(ClockId clock_x, ClockId clock_y) const {
    assert(clock_x < dim_ && clock_y < dim_);
    
    if (empty_) {
        // Return some default for empty zone
        return Bound::less(0);
    }
    
    raw_t raw = dbm_[clock_x * dim_ + clock_y];
    return Bound::from_raw(raw);
}

std::string Zone::to_string() const {
    if (empty_) {
        return "⊥ (empty zone)";
    }
    
    std::ostringstream oss;
    bool first = true;
    
    for (cindex_t i = 0; i < dim_; ++i) {
        for (cindex_t j = 0; j < dim_; ++j) {
            if (i == j) continue;
            
            raw_t raw = dbm_[i * dim_ + j];
            if (raw >= dbm_LS_INFINITY) continue;
            
            Bound b = Bound::from_raw(raw);
            
            if (!first) oss << " ∧ ";
            first = false;
            
            // x_i - x_j <= b
            if (j == 0) {
                // x_i - x_0 <= b means x_i <= b
                oss << "x" << i << " " << b.to_string();
            } else if (i == 0) {
                // x_0 - x_j <= b means x_j >= -b
                std::string op = b.is_strict ? ">" : ">=";
                oss << "x" << j << " " << op << " " << (-b.value);
            } else {
                oss << "x" << i << " - x" << j << " " << b.to_string();
            }
        }
    }
    
    if (first) {
        return "⊤ (universe)";
    }
    
    return oss.str();
}

bool Zone::operator==(const Zone& other) const {
    if (dim_ != other.dim_) return false;
    if (empty_ && other.empty_) return true;
    if (empty_ != other.empty_) return false;
    return dbm_ == other.dbm_;
}

// ── Zone utilities ──────────────────────────────────────────────────────────

bool zone_smoke_test() {
    bool all_passed = true;
    
    // Test 1: Create universe zone
    Zone univ = Zone::universe(3);
    if (univ.is_empty()) {
        all_passed = false;
    }
    
    // Test 2: Create empty zone
    Zone emp = Zone::empty(3);
    if (!emp.is_empty()) {
        all_passed = false;
    }
    
    // Test 3: Create zero zone
    Zone z = Zone::zero(3);
    if (z.is_empty()) {
        all_passed = false;
    }
    
    // Test 4: Add upper bound
    Zone bounded = Zone::universe(3);
    bounded.add_upper_bound(1, 5);
    if (bounded.is_empty()) {
        all_passed = false;
    }
    
    // Test 5: Add conflicting constraints (should be empty)
    // x >= 10 and x <= 5
    Zone conflict = Zone::universe(3);
    conflict.add_lower_bound(1, 10);
    conflict.add_upper_bound(1, 5);
    if (!conflict.is_empty()) {
        all_passed = false;
    }
    
    // Test 6: Reset
    Zone after_reset = Zone::universe(3);
    after_reset.add_upper_bound(1, 5);
    after_reset.reset(1);
    if (after_reset.is_empty()) {
        all_passed = false;
    }
    
    // Test 7: Delay
    Zone delayed = Zone::universe(3);
    delayed.add_upper_bound(1, 5);
    delayed.delay();
    if (delayed.is_empty()) {
        all_passed = false;
    }
    
    // Test 8: Intersection
    Zone z1 = Zone::universe(3);
    z1.add_upper_bound(1, 10);
    Zone z2 = Zone::universe(3);
    z2.add_lower_bound(1, 5);
    Zone inter = z1.intersect(z2);
    if (inter.is_empty()) {
        all_passed = false;
    }
    
    // Test 9: Subset
    Zone small = Zone::universe(3);
    small.add_upper_bound(1, 3);
    Zone big = Zone::universe(3);
    big.add_upper_bound(1, 10);
    if (!small.is_subset_of(big)) {
        all_passed = false;
    }
    
    return all_passed;
}

}  // namespace tctl
