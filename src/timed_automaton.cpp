/// @file timed_automaton.cpp
/// @brief Witness timed automaton: datatypes, serialisation and validation.
///
/// The extractor itself lives with the engine, which is where the marking is.
/// This file holds what a witness *is* and how it is written out --- Graphviz
/// for viewing, JSON for further processing, UPPAAL XML for model checking ---
/// together with the structural checks a certificate must pass before it is
/// offered as one.

#include "tctl/timed_automaton.hpp"
#include "tctl/tableau.hpp"

#include <algorithm>
#include <functional>
#include <iostream>
#include <limits>
#include <sstream>

namespace tctl {

// ============================================================================
// TAConstraint::to_string
// ============================================================================

std::string TAConstraint::to_string(
        const std::map<ClockId, std::string>& cn) const {
    auto name = [&](ClockId c) -> std::string {
        auto it = cn.find(c);
        return (it != cn.end()) ? it->second : ("x" + std::to_string(c));
    };

    std::ostringstream oss;
    if (clock_y == kReferenceClock) {
        // Simple bound:  x op c
        oss << name(clock_x);
        if (is_upper) {
            oss << (is_strict ? " < " : " <= ");
        } else {
            oss << (is_strict ? " > " : " >= ");
        }
        oss << bound;
    } else {
        // Difference constraint:  x - y op c
        oss << name(clock_x) << " - " << name(clock_y);
        oss << (is_strict ? " < " : " <= ");
        oss << bound;
    }
    return oss.str();
}

// ============================================================================
// TimedAutomaton helpers
// ============================================================================

std::string TimedAutomaton::constraint_string(const TAConstraint& c) const {
    return c.to_string(clock_names);
}

std::string TimedAutomaton::guard_string(
        const std::vector<TAConstraint>& g) const {
    if (g.empty()) return "true";
    std::ostringstream oss;
    for (std::size_t i = 0; i < g.size(); ++i) {
        if (i > 0) oss << " && ";
        oss << constraint_string(g[i]);
    }
    return oss.str();
}

std::string TimedAutomaton::invariant_string(
        const std::vector<TAConstraint>& inv) const {
    if (inv.empty()) return "";
    std::ostringstream oss;
    for (std::size_t i = 0; i < inv.size(); ++i) {
        if (i > 0) oss << " && ";
        oss << constraint_string(inv[i]);
    }
    return oss.str();
}

std::string TimedAutomaton::resets_string(
        const std::vector<ClockId>& r) const {
    if (r.empty()) return "";
    std::ostringstream oss;
    for (std::size_t i = 0; i < r.size(); ++i) {
        if (i > 0) oss << ", ";
        auto it = clock_names.find(r[i]);
        if (it != clock_names.end()) {
            oss << it->second;
        } else {
            oss << "x" << r[i];
        }
        oss << " := 0";
    }
    return oss.str();
}

std::string TimedAutomaton::xml_escape(const std::string& s) {
    std::string out;
    out.reserve(s.size());
    for (char c : s) {
        switch (c) {
            case '&':  out += "&amp;";  break;
            case '<':  out += "&lt;";   break;
            case '>':  out += "&gt;";   break;
            case '"':  out += "&quot;"; break;
            case '\'': out += "&apos;"; break;
            default:   out += c;        break;
        }
    }
    return out;
}

// ============================================================================
// TimedAutomaton::to_string
// ============================================================================

std::string TimedAutomaton::to_string() const {
    std::ostringstream oss;
    oss << "Timed Automaton:\n";
    oss << "  Clocks (" << num_clocks - 1 << "): ";
    bool first = true;
    for (const auto& [cid, name] : clock_names) {
        if (!first) oss << ", ";
        oss << name;
        first = false;
    }
    oss << "\n";

    oss << "  Locations (" << locations.size() << "):\n";
    for (const auto& [lid, loc] : locations) {
        oss << "    L" << lid;
        if (loc.is_initial) oss << " [initial]";
        oss << " atoms={";
        first = true;
        for (const auto& a : loc.atoms) {
            if (!first) oss << ", ";
            oss << a;
            first = false;
        }
        oss << "}";
        std::string inv = invariant_string(loc.invariants);
        if (!inv.empty()) {
            oss << " inv: " << inv;
        }
        oss << "\n";
    }

    oss << "  Transitions (" << transitions.size() << "):\n";
    for (const auto& t : transitions) {
        oss << "    L" << t.source << " -> L" << t.target;
        std::string g = guard_string(t.guard);
        if (g != "true") {
            oss << " [" << g << "]";
        }
        std::string r = resets_string(t.resets);
        if (!r.empty()) {
            oss << " {" << r << "}";
        }
        oss << "\n";
    }

    return oss.str();
}

// ============================================================================
// TimedAutomaton::to_dot
// ============================================================================

std::string TimedAutomaton::to_dot() const {
    std::ostringstream oss;
    oss << "digraph TimedAutomaton {\n";
    oss << "  rankdir=LR;\n";
    oss << "  node [shape=circle fontname=\"Helvetica\" fontsize=10];\n";
    oss << "  edge [fontname=\"Helvetica\" fontsize=9];\n";

    // Invisible entry arrow
    oss << "  __init [shape=none label=\"\"];\n";
    oss << "  __init -> L" << initial_location << ";\n";

    // Locations
    for (const auto& [lid, loc] : locations) {
        std::string shape = loc.is_initial ? "doublecircle" : "circle";
        oss << "  L" << lid << " [shape=" << shape << " label=\"L" << lid << "\\n{";
        bool first = true;
        for (const auto& a : loc.atoms) {
            if (!first) oss << ", ";
            oss << a;
            first = false;
        }
        oss << "}";
        std::string inv = invariant_string(loc.invariants);
        if (!inv.empty()) {
            oss << "\\ninv: " << inv;
        }
        oss << "\"];\n";
    }

    // Transitions
    for (const auto& t : transitions) {
        oss << "  L" << t.source << " -> L" << t.target << " [label=\"";
        std::string g = guard_string(t.guard);
        if (g != "true") {
            oss << g;
        }
        std::string r = resets_string(t.resets);
        if (!r.empty()) {
            if (g != "true") oss << "\\n";
            oss << r;
        }
        oss << "\"];\n";
    }

    oss << "}\n";
    return oss.str();
}

// ============================================================================
// TimedAutomaton::to_json
// ============================================================================

std::string TimedAutomaton::to_json() const {
    std::ostringstream oss;
    oss << "{\n";

    // Clocks
    oss << "  \"clocks\": [";
    {
        bool first = true;
        for (const auto& [cid, name] : clock_names) {
            if (!first) oss << ", ";
            oss << "\"" << name << "\"";
            first = false;
        }
    }
    oss << "],\n";

    // Initial location
    oss << "  \"initial_location\": " << initial_location << ",\n";

    // Locations
    oss << "  \"locations\": [\n";
    {
        bool first_loc = true;
        for (const auto& [lid, loc] : locations) {
            if (!first_loc) oss << ",\n";
            oss << "    {\n";
            oss << "      \"id\": " << lid << ",\n";
            oss << "      \"initial\": " << (loc.is_initial ? "true" : "false") << ",\n";
            oss << "      \"atoms\": [";
            {
                bool first = true;
                for (const auto& a : loc.atoms) {
                    if (!first) oss << ", ";
                    oss << "\"" << a << "\"";
                    first = false;
                }
            }
            oss << "],\n";
            oss << "      \"invariant\": \"" << invariant_string(loc.invariants) << "\"\n";
            oss << "    }";
            first_loc = false;
        }
    }
    oss << "\n  ],\n";

    // Transitions
    oss << "  \"transitions\": [\n";
    {
        bool first_tr = true;
        for (const auto& t : transitions) {
            if (!first_tr) oss << ",\n";
            oss << "    {\n";
            oss << "      \"source\": " << t.source << ",\n";
            oss << "      \"target\": " << t.target << ",\n";
            oss << "      \"guard\": \"" << guard_string(t.guard) << "\",\n";
            oss << "      \"resets\": [";
            {
                bool first = true;
                for (ClockId c : t.resets) {
                    if (!first) oss << ", ";
                    auto it = clock_names.find(c);
                    oss << "\"" << (it != clock_names.end() ? it->second
                                                            : "x" + std::to_string(c))
                        << "\"";
                    first = false;
                }
            }
            oss << "]\n";
            oss << "    }";
            first_tr = false;
        }
    }
    oss << "\n  ]\n";
    oss << "}\n";
    return oss.str();
}

// ============================================================================
// TimedAutomaton::to_uppaal_xml
// ============================================================================

std::string TimedAutomaton::to_uppaal_xml() const {
    std::ostringstream oss;

    oss << "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n";
    oss << "<!DOCTYPE nta PUBLIC '-//Uppaal Team//DTD Flat System 1.6//EN' "
           "'http://www.it.uu.se/research/group/darts/uppaal/flat-1_6.dtd'>\n";
    oss << "<nta>\n";

    // ── Declarations: clocks ────────────────────────────────────────────
    oss << "  <declaration>\n";
    if (!clock_names.empty()) {
        oss << "clock ";
        bool first = true;
        for (const auto& [cid, name] : clock_names) {
            if (!first) oss << ", ";
            oss << name;
            first = false;
        }
        oss << ";\n";
    }
    oss << "  </declaration>\n";

    // ── Template ────────────────────────────────────────────────────────
    oss << "  <template>\n";
    oss << "    <name>Tableau</name>\n";

    // Locations
    int x_pos = 0;
    for (const auto& [lid, loc] : locations) {
        oss << "    <location id=\"id" << lid << "\" "
            << "x=\"" << x_pos << "\" y=\"0\">\n";
        oss << "      <name>L" << lid << "</name>\n";
        std::string inv = invariant_string(loc.invariants);
        if (!inv.empty()) {
            oss << "      <label kind=\"invariant\">"
                << xml_escape(inv) << "</label>\n";
        }
        oss << "    </location>\n";
        x_pos += 150;
    }

    // Initial location
    oss << "    <init ref=\"id" << initial_location << "\"/>\n";

    // Transitions
    for (const auto& t : transitions) {
        oss << "    <transition>\n";
        oss << "      <source ref=\"id" << t.source << "\"/>\n";
        oss << "      <target ref=\"id" << t.target << "\"/>\n";

        std::string g = guard_string(t.guard);
        if (g != "true") {
            oss << "      <label kind=\"guard\">"
                << xml_escape(g) << "</label>\n";
        }

        if (!t.resets.empty()) {
            std::ostringstream assign;
            bool first = true;
            for (ClockId c : t.resets) {
                if (!first) assign << ", ";
                auto it = clock_names.find(c);
                assign << (it != clock_names.end() ? it->second
                                                   : "x" + std::to_string(c))
                       << " = 0";
                first = false;
            }
            oss << "      <label kind=\"assignment\">"
                << xml_escape(assign.str()) << "</label>\n";
        }

        oss << "    </transition>\n";
    }

    oss << "  </template>\n";

    // ── System declaration ──────────────────────────────────────────────
    oss << "  <system>\n";
    oss << "system Tableau;\n";
    oss << "  </system>\n";

    oss << "</nta>\n";
    return oss.str();
}

// ── Structural validation ───────────────────────────────────────────────────

TAValidation validate(const TimedAutomaton& ta) {
    TAValidation v;
    auto fail = [&](const std::string& s) { v.ok = false; v.problems.push_back(s); };

    if (ta.locations.empty()) fail("no locations");
    if (ta.locations.find(ta.initial_location) == ta.locations.end())
        fail("initial location is not among the locations");

    // Non-blocking: every location needs an outgoing transition, or time could
    // reach an invariant's bound with no move available.
    std::map<std::uint32_t, std::size_t> out;
    for (const TATransition& e : ta.transitions) {
        ++out[e.source];
        if (ta.locations.find(e.target) == ta.locations.end())
            fail("transition targets an unknown location");
        for (const TAConstraint& g : e.guard)
            if (g.clock_x >= ta.num_clocks || g.clock_y >= ta.num_clocks)
                fail("guard reads a clock the automaton does not declare");
        for (ClockId r : e.resets)
            if (r == kReferenceClock || r >= ta.num_clocks)
                fail("transition resets an invalid clock");
    }
    for (const auto& [id, loc] : ta.locations) {
        // With no invariant, a location without an outgoing transition is not
        // blocking: time simply diverges there, which is a legitimate witness
        // tail.  It blocks only when an invariant can stop time with no move
        // enabled.
        if (out[id] == 0 && !loc.invariants.empty())
            fail("location " + std::to_string(id) +
                 " has an invariant but no outgoing transition");
        for (const std::string& a : loc.atoms)
            if (!a.empty() && a[0] == '!' && loc.atoms.count(a.substr(1)))
                fail("location " + std::to_string(id) + " asserts both " +
                     a.substr(1) + " and its negation");
        for (const TAConstraint& c : loc.invariants)
            if (!c.is_upper) fail("location invariant is not an upper bound");
    }
    return v;
}

}  // namespace tctl
