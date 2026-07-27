// ============================================================================
// tctl/zoneset.hpp — ZoneSet: a finite union of zones (HDBM federation wrapper)
// ============================================================================
//
// The tableau reasons about satisfaction sets S_X(μ) that are, in
// general, finite unions of ≅_M-zones (Knaster–Tarski fixpoints over unions of
// DBMs).  A single `Zone` (one DBM) cannot represent such a union, nor the
// convex decomposition cvx(·) demanded by the partial-cover rule (Cov*).
//
// `ZoneSet` wraps HDBM's `ptctlmc::Federation` (a finite set of DBMs) to
// provide exactly the operations the construction needs:
//
//   * set algebra           : ∪ (unite), ∩ (intersect), \ (subtract)
//   * relations             : ⊆ (is_subset_of / contains), = (equals)
//   * timed operations      : time-successor (up), reset x:=0, single-clock
//                             guards, max-constant extrapolation (≅_M)
//   * convex decomposition  : components() = cvx(·), the member zones
//   * canonicalisation      : reduce() (removes subsumed / merges mergeable DBMs)
//
// It interoperates with `Zone` via `Zone::raw_data()` / `Zone::from_raw()`.
// ============================================================================

#ifndef CTL_ZONESET_HPP
#define CTL_ZONESET_HPP

#include "tctl/zone.hpp"

#include "ptctlmc/fed.hpp"

#include <cstdint>
#include <string>
#include <vector>

namespace tctl {

class ZoneSet {
public:
    // ── Factory methods ─────────────────────────────────────────────────
    /// The empty set ∅ over `num_clocks` clocks (including reference clock 0).
    static ZoneSet empty(std::size_t num_clocks);
    /// The universe ⊤ (all non-negative valuations) over `num_clocks` clocks.
    static ZoneSet universe(std::size_t num_clocks);
    /// The singleton set {z}.  An empty Zone yields ∅.
    static ZoneSet of(const Zone& z);

    // ── Construction ────────────────────────────────────────────────────
    ZoneSet();                                   // 1 clock, empty
    ZoneSet(const ZoneSet&) = default;
    ZoneSet(ZoneSet&&) noexcept = default;
    ZoneSet& operator=(const ZoneSet&) = default;
    ZoneSet& operator=(ZoneSet&&) noexcept = default;
    ~ZoneSet() = default;

    // ── Accessors ───────────────────────────────────────────────────────
    std::size_t num_clocks() const;
    bool        is_empty() const;
    /// Number of member DBMs (after any reduce()).  Representation-dependent;
    /// use only for diagnostics/tests, not for semantic equality.
    std::size_t size() const;

    // ── Relations ───────────────────────────────────────────────────────
    /// z ⊆ this  (every valuation of z lies in this set).
    bool contains(const Zone& z) const;
    /// this ⊆ other.
    bool is_subset_of(const ZoneSet& other) const;
    /// this = other  (exact set equality).
    bool equals(const ZoneSet& other) const;

    // ── Set algebra (in place, chainable) ───────────────────────────────
    ZoneSet& unite(const ZoneSet& other);
    ZoneSet& unite(const Zone& z);
    ZoneSet& intersect(const ZoneSet& other);
    ZoneSet& intersect(const Zone& z);
    ZoneSet& subtract(const ZoneSet& other);

    // ── Timed operations (in place, chainable) ──────────────────────────
    ZoneSet& up();                                              // time-successor  ↑Z
    /// Inverse delay ↓Z = time-predecessors { v | ∃ t≥0. v+t ∈ Z }.
    /// This is the primitive behind the least-fixpoint for timed until:
    /// a valuation can delay into the base window x_μ∈I exactly when it lies
    /// in down(x_μ∈I).
    ZoneSet& down();
    ZoneSet& reset(ClockId clock);                             // clock := 0
    ZoneSet& constrain_upper(ClockId clock, std::int32_t bound, bool strict);
    ZoneSet& constrain_lower(ClockId clock, std::int32_t bound, bool strict);
    ZoneSet& extrapolate(const std::vector<std::int32_t>& max);
    ZoneSet& reduce();                                         // canonical/minimal

    // ── Decomposition ───────────────────────────────────────────────────
    /// cvx(·): the member zones (each convex).  Empty members are dropped.
    std::vector<Zone> components() const;

    std::string to_string() const;

private:
    ZoneSet(ptctlmc::Federation fed, std::size_t nclk)
        : fed_(std::move(fed)), nclk_(nclk) {}

    // A federation carries no dimension of its own once it is empty, so the
    // clock count is tracked alongside it.
    ptctlmc::Federation fed_;
    std::size_t         nclk_ = 1;
};

}  // namespace tctl

#endif  // CTL_ZONESET_HPP
