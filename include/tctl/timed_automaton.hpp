// ============================================================================
// tctl/timed_automaton.hpp — Timed Automaton extracted from tableau graph
// ============================================================================
//
// Extracts a Timed Automaton (TA) in UPPAAL semantics from the fully
// constructed tableau graph.  Each tableau node becomes a TA location;
// discrete successor edges become TA transitions (delay edges are removed
// since time elapse is implicit via invariants).
//
// UPPAAL constraints on guards / invariants:
//   - Location invariants: upper bounds only (x <= c, x < c).
//   - Transition guards:   x <= c, x < c, x >= c, x > c, x - y op c.
//   - Resets:              x := 0.
//
// ============================================================================

#ifndef CTL_TIMED_AUTOMATON_HPP
#define CTL_TIMED_AUTOMATON_HPP

#include "tctl/ast.hpp"
#include "tctl/zone.hpp"

#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace tctl {

// Forward declarations.
class TableauEngine;
struct TableauNode;

// ── TAConstraint ────────────────────────────────────────────────────────────
// A single clock constraint of the form  x op c  or  x - y op c.

struct TAConstraint {
    ClockId     clock_x;        // LHS clock
    ClockId     clock_y;        // RHS clock (kReferenceClock for simple bounds)
    std::int32_t bound;
    bool        is_strict;      // true for < / >, false for <= / >=
    bool        is_upper;       // true for x - y <= c, false for x - y >= c (i.e., y - x <= -c)

    std::string to_string(const std::map<ClockId, std::string>& clock_names) const;
};

// ── TALocation ──────────────────────────────────────────────────────────────

struct TALocation {
    std::uint32_t           id;
    std::set<std::string>   atoms;       // Positive atomic propositions
    std::vector<TAConstraint> invariants; // Upper-bound constraints only
    bool                    is_initial = false;
};

// ── TATransition ────────────────────────────────────────────────────────────

struct TATransition {
    std::uint32_t             source;
    std::uint32_t             target;
    std::vector<TAConstraint> guard;      // Guard constraints
    std::vector<ClockId>      resets;     // Clocks reset to 0
};

// ── TimedAutomaton ──────────────────────────────────────────────────────────

class TimedAutomaton {
public:
    // Clock metadata.
    std::size_t                         num_clocks = 0;
    std::map<ClockId, std::string>      clock_names;  // clock id → "x_<formulaId>"

    // Locations and transitions.
    std::map<std::uint32_t, TALocation> locations;
    std::vector<TATransition>           transitions;

    // Initial location id.
    std::uint32_t                       initial_location = 0;

    // ── Serialisation ───────────────────────────────────────────────────
    std::string to_dot()       const;
    std::string to_json()      const;
    std::string to_uppaal_xml() const;
    std::string to_string()    const;

private:
    // Helpers for serialisation.
    std::string constraint_string(const TAConstraint& c) const;
    std::string guard_string(const std::vector<TAConstraint>& g) const;
    std::string invariant_string(const std::vector<TAConstraint>& inv) const;
    std::string resets_string(const std::vector<ClockId>& r) const;
    static std::string xml_escape(const std::string& s);
};

// ── Builder ─────────────────────────────────────────────────────────────────
// Extract a TA from a fully-explored tableau engine.

TimedAutomaton build_from_tableau(const TableauEngine& engine);

}  // namespace tctl

#endif  // CTL_TIMED_AUTOMATON_HPP
