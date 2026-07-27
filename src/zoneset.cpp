// ============================================================================
// zoneset.cpp — ZoneSet implementation over HDBM's ptctlmc::Federation
// ============================================================================

#include "tctl/zoneset.hpp"

#include <sstream>
#include <utility>

namespace tctl {

namespace {

// tctl::Zone (dim = num_clocks, reference clock included) → ptctlmc::Dbm
// (constructed from a *clock count*, so dim = nclocks + 1).
ptctlmc::Dbm to_dbm(const Zone& z) {
    const int nclocks = static_cast<int>(z.num_clocks()) - 1;
    ptctlmc::Dbm d(nclocks);
    if (z.is_empty()) {
        // Any inconsistent matrix denotes ∅; a negative diagonal is the
        // canonical one and is what Dbm::empty() tests for.
        d.set(0, 0, ptctlmc::lt(0));
        return d;
    }
    const raw_t* m = z.raw_data();
    std::copy(m, m + z.num_clocks() * z.num_clocks(), d.data().begin());
    return d;
}

Zone from_dbm(const ptctlmc::Dbm& d) {
    const std::size_t dim = static_cast<std::size_t>(d.dim());
    if (d.empty()) return Zone::empty(dim);
    return Zone::from_raw(dim, d.data().data());
}

// A federation with no members denotes ∅; members are kept non-empty by every
// operation below, so membership emptiness and set emptiness coincide.
void drop_empty(ptctlmc::Federation& f) {
    ptctlmc::Federation kept;
    kept.reserve(f.size());
    for (ptctlmc::Dbm& d : f)
        if (!d.empty()) kept.push_back(std::move(d));
    f.swap(kept);
}

}  // namespace

// ── Factory methods ─────────────────────────────────────────────────────────

ZoneSet ZoneSet::empty(std::size_t num_clocks) {
    return ZoneSet(ptctlmc::Federation{}, num_clocks);          // ∅
}

ZoneSet ZoneSet::universe(std::size_t num_clocks) {
    ptctlmc::Federation f;
    f.push_back(ptctlmc::Dbm::universe(static_cast<int>(num_clocks) - 1));
    return ZoneSet(std::move(f), num_clocks);
}

ZoneSet ZoneSet::of(const Zone& z) {
    ptctlmc::Federation f;
    if (!z.is_empty()) f.push_back(to_dbm(z));
    return ZoneSet(std::move(f), z.num_clocks());
}

// ── Construction ────────────────────────────────────────────────────────────

ZoneSet::ZoneSet() : fed_(), nclk_(1) {}

// ── Accessors ────────────────────────────────────────────────────────────────

std::size_t ZoneSet::num_clocks() const { return nclk_; }
bool        ZoneSet::is_empty()   const { return fed_.empty(); }
std::size_t ZoneSet::size()       const { return fed_.size(); }

// ── Relations ────────────────────────────────────────────────────────────────

bool ZoneSet::contains(const Zone& z) const {
    if (z.is_empty()) return true;                     // ∅ ⊆ this
    // Exact: z may be covered jointly by several members, so this is decided by
    // emptiness of the set difference, not by pairwise inclusion.
    return ptctlmc::fed_covers(fed_, to_dbm(z));
}

bool ZoneSet::is_subset_of(const ZoneSet& other) const {
    return ptctlmc::fed_included_in(fed_, other.fed_);
}
bool ZoneSet::equals(const ZoneSet& other) const {
    return ptctlmc::fed_equal(fed_, other.fed_);
}

// ── Set algebra ──────────────────────────────────────────────────────────────

ZoneSet& ZoneSet::unite(const ZoneSet& other) {
    for (const ptctlmc::Dbm& d : other.fed_) ptctlmc::fed_add(fed_, d);
    return *this;
}

ZoneSet& ZoneSet::unite(const Zone& z) {
    if (!z.is_empty()) ptctlmc::fed_add(fed_, to_dbm(z));
    return *this;
}

ZoneSet& ZoneSet::intersect(const ZoneSet& other) {
    fed_ = ptctlmc::fed_intersect(fed_, other.fed_);
    drop_empty(fed_);
    return *this;
}

ZoneSet& ZoneSet::intersect(const Zone& z) {
    if (z.is_empty()) { fed_.clear(); return *this; }
    fed_ = ptctlmc::fed_intersect(fed_, to_dbm(z));
    drop_empty(fed_);
    return *this;
}

ZoneSet& ZoneSet::subtract(const ZoneSet& other) {
    fed_ = ptctlmc::fed_difference(fed_, other.fed_);
    drop_empty(fed_);
    return *this;
}

// ── Timed operations ─────────────────────────────────────────────────────────

ZoneSet& ZoneSet::up() {
    for (ptctlmc::Dbm& d : fed_) d.delay();
    return *this;
}

ZoneSet& ZoneSet::down() {
    for (ptctlmc::Dbm& d : fed_) d.down();
    return *this;
}

ZoneSet& ZoneSet::reset(ClockId clock) {
    for (ptctlmc::Dbm& d : fed_) d.reset(static_cast<int>(clock));
    return *this;
}

ZoneSet& ZoneSet::constrain_upper(ClockId clock, std::int32_t bound, bool strict) {
    // x_clock - x_0 (< | <=) bound   ⇒  x_clock (< | <=) bound
    const raw_t r = Bound{bound, strict}.to_raw();
    for (ptctlmc::Dbm& d : fed_) d.constrain(static_cast<int>(clock), 0, r);
    drop_empty(fed_);
    return *this;
}

ZoneSet& ZoneSet::constrain_lower(ClockId clock, std::int32_t bound, bool strict) {
    // x_0 - x_clock (< | <=) -bound  ⇒  x_clock (> | >=) bound
    const raw_t r = Bound{-bound, strict}.to_raw();
    for (ptctlmc::Dbm& d : fed_) d.constrain(0, static_cast<int>(clock), r);
    drop_empty(fed_);
    return *this;
}

ZoneSet& ZoneSet::extrapolate(const std::vector<std::int32_t>& max) {
    for (ptctlmc::Dbm& d : fed_) d.extrapolate(max);
    return *this;
}

ZoneSet& ZoneSet::reduce() { ptctlmc::fed_reduce(fed_); return *this; }

// ── Decomposition ────────────────────────────────────────────────────────────

std::vector<Zone> ZoneSet::components() const {
    std::vector<Zone> out;
    out.reserve(fed_.size());
    for (const ptctlmc::Dbm& d : fed_) {
        if (d.empty()) continue;
        out.push_back(from_dbm(d));
    }
    return out;
}

std::string ZoneSet::to_string() const {
    if (is_empty()) return "∅";
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
