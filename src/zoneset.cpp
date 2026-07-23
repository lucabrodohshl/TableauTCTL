// ============================================================================
// zoneset.cpp — ZoneSet implementation over UDBM's dbm::fed_t
// ============================================================================

#include "tctl/zoneset.hpp"

#include <dbm/fed.h>

#include <sstream>
#include <utility>

namespace tctl {

namespace {

// Zone (single DBM, raw_t matrix) → UDBM dbm_t.
dbm::dbm_t to_dbm(const Zone& z) {
    const cindex_t dim = static_cast<cindex_t>(z.num_clocks());
    if (z.is_empty()) return dbm::dbm_t(dim);          // empty dbm_t
    return dbm::dbm_t(z.raw_data(), dim);              // copies the matrix
}

// UDBM dbm_t → Zone.
Zone from_dbm(const dbm::dbm_t& d) {
    const cindex_t dim = d.getDimension();
    if (d.isEmpty()) return Zone::empty(dim);
    return Zone::from_raw(dim, d());                   // d() = const raw_t*
}

}  // namespace

// ── Factory methods ─────────────────────────────────────────────────────────

ZoneSet ZoneSet::empty(std::size_t num_clocks) {
    return ZoneSet(dbm::fed_t(static_cast<cindex_t>(num_clocks)));   // ∅
}

ZoneSet ZoneSet::universe(std::size_t num_clocks) {
    dbm::fed_t f(static_cast<cindex_t>(num_clocks));
    f.setInit();                                        // {universe DBM}
    return ZoneSet(std::move(f));
}

ZoneSet ZoneSet::of(const Zone& z) {
    dbm::fed_t f(static_cast<cindex_t>(z.num_clocks()));
    if (!z.is_empty()) f |= to_dbm(z);
    return ZoneSet(std::move(f));
}

// ── Construction ────────────────────────────────────────────────────────────

ZoneSet::ZoneSet() : fed_(1) {}

// ── Accessors ────────────────────────────────────────────────────────────────

std::size_t ZoneSet::num_clocks() const { return fed_.getDimension(); }
bool        ZoneSet::is_empty()   const { return fed_.isEmpty(); }
std::size_t ZoneSet::size()       const { return fed_.size(); }

// ── Relations ────────────────────────────────────────────────────────────────

bool ZoneSet::contains(const Zone& z) const {
    if (z.is_empty()) return true;                     // ∅ ⊆ this
    return fed_.ge(to_dbm(z));                          // this ⊇ z
}

bool ZoneSet::is_subset_of(const ZoneSet& other) const { return fed_.le(other.fed_); }
bool ZoneSet::equals(const ZoneSet& other)       const { return fed_.eq(other.fed_); }

// ── Set algebra ──────────────────────────────────────────────────────────────

ZoneSet& ZoneSet::unite(const ZoneSet& other) { fed_ |= other.fed_; return *this; }

ZoneSet& ZoneSet::unite(const Zone& z) {
    if (!z.is_empty()) fed_ |= to_dbm(z);
    return *this;
}

ZoneSet& ZoneSet::intersect(const ZoneSet& other) { fed_ &= other.fed_; return *this; }

ZoneSet& ZoneSet::intersect(const Zone& z) {
    if (z.is_empty()) { fed_.setEmpty(); return *this; }
    fed_ &= to_dbm(z);
    return *this;
}

ZoneSet& ZoneSet::subtract(const ZoneSet& other) { fed_ -= other.fed_; return *this; }

// ── Timed operations ─────────────────────────────────────────────────────────

ZoneSet& ZoneSet::up()   { fed_.up();   return *this; }
ZoneSet& ZoneSet::down() { fed_.down(); return *this; }

ZoneSet& ZoneSet::reset(ClockId clock) { fed_.updateValue(clock, 0); return *this; }

ZoneSet& ZoneSet::constrain_upper(ClockId clock, std::int32_t bound, bool strict) {
    // x_clock - x_0 (< | <=) bound   ⇒  x_clock (< | <=) bound
    fed_.constrain(clock, 0, bound, strict);
    return *this;
}

ZoneSet& ZoneSet::constrain_lower(ClockId clock, std::int32_t bound, bool strict) {
    // x_0 - x_clock (< | <=) -bound  ⇒  x_clock (> | >=) bound
    fed_.constrain(0, clock, -bound, strict);
    return *this;
}

ZoneSet& ZoneSet::extrapolate(const std::vector<std::int32_t>& max) {
    fed_.extrapolateMaxBounds(max.data());
    return *this;
}

ZoneSet& ZoneSet::reduce() { fed_.reduce(); return *this; }

// ── Decomposition ────────────────────────────────────────────────────────────

std::vector<Zone> ZoneSet::components() const {
    std::vector<Zone> out;
    for (auto it = fed_.begin(); it != fed_.end(); ++it) {
        const dbm::dbm_t& d = *it;
        if (d.isEmpty()) continue;
        out.push_back(from_dbm(d));
    }
    return out;
}

std::string ZoneSet::to_string() const {
    if (fed_.isEmpty()) return "∅";
    std::ostringstream oss;
    bool first = true;
    for (const Zone& comp : components()) {
        if (!first) oss << " ∪ ";
        first = false;
        oss << "(" << comp.to_string() << ")";
    }
    return oss.str();
}

}  // namespace tctl
