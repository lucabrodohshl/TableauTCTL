// ============================================================================
// timed_automaton.cpp — Timed Automaton extraction from tableau graph
// ============================================================================

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

// ============================================================================
// build_from_tableau() — Extract a Timed Automaton from a satisfying tableau
// ============================================================================
//
// Algorithm overview:
//   1. Identify "state" nodes: Open, saturated, non-delay-successor tableau
//      nodes.  Delay-successor nodes are NOT locations — they are traversed
//      as part of the edge-finding walk.
//   2. Canonicalize state nodes by (atom valuation, canonical zone) to
//      produce TA locations.
//   3. Extract location invariants from the time-closure of the zone:
//      apply up(), then take finite upper bounds.
//   4. Walk successor subtrees: starting from each state node u, follow
//      any chain of delay-successor nodes, then expansion children, until
//      reaching the next saturated non-delay Open node v.  Emit edge u→v.
//      Guards come from the zone at the exit point (after delay chain).
//   5. Collect clock resets and timed-until discharge constraints along
//      the traversal path.
//   6. Set initial location from root.
//   7. Prune unreachable locations by BFS from initial.
//   8. Run soundness checks.
// ============================================================================

TimedAutomaton build_from_tableau(const TableauEngine& engine) {
    TimedAutomaton ta;
    FormulaFactory& factory = engine.factory();

    // ── 0. Clock setup ──────────────────────────────────────────────────
    ta.num_clocks = engine.num_clocks_;
    for (const auto& [fid, clk] : engine.clock_of_) {
        if (ta.clock_names.find(clk) == ta.clock_names.end()) {
            ta.clock_names[clk] = "x_" + std::to_string(clk);
        }
    }

    // ── Helpers ─────────────────────────────────────────────────────────

    // Check whether a node is fully saturated (no expandable formulas).
    auto is_saturated = [&](const TableauNode* node) -> bool {
        for (FormulaId id : node->gamma.elements()) {
            const FormulaNode& n = factory.node(id);
            switch (n.kind) {
                case NodeKind::And:
                case NodeKind::Or:
                case NodeKind::EU:
                case NodeKind::AU:
                case NodeKind::AX:
                case NodeKind::TimedEU:
                case NodeKind::TimedAU:
                    return false;
                case NodeKind::Not: {
                    const FormulaNode& inner = factory.node(n.children[0]);
                    if (inner.kind == NodeKind::TimedEU ||
                        inner.kind == NodeKind::TimedAU)
                        return false;
                    break;
                }
                default:
                    break;
            }
        }
        return true;
    };

    // A node qualifies as a TA location iff it is open, saturated,
    // and NOT a delay-successor (delay nodes are traversal waypoints).
    auto is_state_node = [&](const TableauNode* node) -> bool {
        return node->status == NodeStatus::Open
            && is_saturated(node)
            && !node->is_delay_successor;
    };

    // Extract positive atom names from Γ.
    auto extract_atoms = [&](const FormulaSet& gamma) -> std::set<std::string> {
        std::set<std::string> atoms;
        for (FormulaId id : gamma.elements()) {
            const FormulaNode& n = factory.node(id);
            if (n.kind == NodeKind::Atom)
                atoms.insert(n.atom_name);
        }
        return atoms;
    };

    // ── 1. Canonicalize state nodes → TA locations ──────────────────────

    struct LocationKey {
        std::set<std::string> atoms;
        std::string           zone_str;
        bool operator<(const LocationKey& o) const {
            if (atoms < o.atoms) return true;
            if (o.atoms < atoms) return false;
            return zone_str < o.zone_str;
        }
    };

    std::map<LocationKey, std::uint32_t>        key_to_loc;
    std::map<const TableauNode*, std::uint32_t> node_to_loc;
    std::map<std::uint32_t, Zone>               loc_zone;
    std::uint32_t next_loc_id = 0;

    std::vector<const TableauNode*> state_nodes;

    for (const auto& np : engine.nodes()) {
        const TableauNode* node = np.get();
        if (!is_state_node(node)) continue;

        state_nodes.push_back(node);

        LocationKey key;
        key.atoms    = extract_atoms(node->gamma);
        key.zone_str = node->zone.to_string();

        auto it = key_to_loc.find(key);
        if (it == key_to_loc.end()) {
            std::uint32_t lid = next_loc_id++;
            key_to_loc[key]   = lid;
            node_to_loc[node] = lid;
            loc_zone[lid]     = node->zone;

            TALocation loc;
            loc.id         = lid;
            loc.atoms      = key.atoms;
            loc.is_initial = false;
            ta.locations[lid] = std::move(loc);
        } else {
            node_to_loc[node] = it->second;
        }
    }

    if (ta.locations.empty()) {
        throw std::logic_error(
            "build_from_tableau: no state nodes found in tableau");
    }

    // ── 2. Location labels ──────────────────────────────────────────────
    //   Names are L_<id>.  Atoms already stored in TALocation::atoms.

    // ── 3. Build location invariants ────────────────────────────────────
    //   Compute time-closure: zone.up(), then extract finite upper bounds.

    for (auto& [lid, loc] : ta.locations) {
        const Zone& zone = loc_zone[lid];
        if (zone.is_empty() || zone.num_clocks() <= 1) continue;

        // Time-closure: apply delay (up) to get the set of valuations
        // reachable by letting time pass.
        Zone closed_zone = zone;
        closed_zone.up();

        for (ClockId clk = 1;
             clk < static_cast<ClockId>(closed_zone.num_clocks()); ++clk) {
            Bound ub = closed_zone.get_bound(clk, kReferenceClock);
            if (!ub.is_infinity()) {
                TAConstraint c;
                c.clock_x   = clk;
                c.clock_y   = kReferenceClock;
                c.bound     = ub.value;
                c.is_strict = ub.is_strict;
                c.is_upper  = true;
                loc.invariants.push_back(c);
            }
        }
    }

    // ── 4. Build edges ──────────────────────────────────────────────────
    //
    //  For each state node u, explore its subtree:
    //    - follow delay-successor children (they are NOT TA locations)
    //    - follow expansion children of delay / non-delay nodes
    //    - stop at the next saturated, non-delay, Open node v
    //  Emit edge u → v.
    //
    //  The guard zone is taken from the zone at the traversal exit point
    //  (the zone after the delay chain), NOT from u's raw zone.
    //
    //  Along the walk, accumulate:
    //    • clock resets
    //    • timed-until discharge guard constraints
    //    • the "exit zone" (zone of the last node before reaching v,
    //      which captures delay effects)

    struct DescendantInfo {
        const TableauNode*        node;
        std::vector<ClockId>      resets;
        std::vector<TAConstraint> extra_guards;
        Zone                      exit_zone;   // zone after delay chain
    };

    // Recursive walk through the subtree.
    // `cur_zone` tracks the zone we've accumulated through delay edges.
    std::function<void(
        const TableauNode*,
        const TableauNode*,
        std::vector<ClockId>,
        std::vector<TAConstraint>,
        Zone,
        std::vector<DescendantInfo>&)>
    find_descendant_states =
        [&](const TableauNode*        node,
            const TableauNode*        parent,
            std::vector<ClockId>      resets,
            std::vector<TAConstraint> extra_guards,
            Zone                      cur_zone,
            std::vector<DescendantInfo>& result)
    {
        if (node->status != NodeStatus::Open) return;

        // Accumulate resets from this node.
        for (ClockId r : node->clock_resets)
            resets.push_back(r);

        // If this is a delay-successor, update cur_zone to its (delayed) zone.
        if (node->is_delay_successor) {
            cur_zone = node->zone;
        }

        // Detect timed-until discharge: formula in parent->active_timed
        // but NOT in node->active_timed  ⇒  discharged here.
        if (parent) {
            for (FormulaId fid : parent->active_timed) {
                if (node->active_timed.count(fid) != 0) continue;

                const FormulaNode& fn = factory.node(fid);
                if (fn.kind != NodeKind::TimedEU &&
                    fn.kind != NodeKind::TimedAU)
                    continue;

                auto cit = engine.clock_of_.find(fid);
                if (cit == engine.clock_of_.end()) continue;
                ClockId clk = cit->second;

                // Lower bound:  clock >= a
                if (!fn.time_lower.is_infinity &&
                    (fn.time_lower.value > 0 ||
                     fn.time_lower.is_strict)) {
                    TAConstraint c;
                    c.clock_x   = clk;
                    c.clock_y   = kReferenceClock;
                    c.bound     = static_cast<std::int32_t>(
                                      fn.time_lower.value);
                    c.is_strict = fn.time_lower.is_strict;
                    c.is_upper  = false;
                    extra_guards.push_back(c);
                }

                // Upper bound:  clock <= b
                if (!fn.time_upper.is_infinity) {
                    TAConstraint c;
                    c.clock_x   = clk;
                    c.clock_y   = kReferenceClock;
                    c.bound     = static_cast<std::int32_t>(
                                      fn.time_upper.value);
                    c.is_strict = fn.time_upper.is_strict;
                    c.is_upper  = true;
                    extra_guards.push_back(c);
                }
            }
        }

        // If this node is a state node (saturated, non-delay), record it.
        if (is_state_node(node)) {
            result.push_back({node, resets, extra_guards, cur_zone});
            return;
        }

        // Otherwise keep walking children (delay or expansion).
        for (const TableauNode* child : node->children) {
            find_descendant_states(child, node, resets, extra_guards,
                                   cur_zone, result);
        }
    };

    // Deduplication set for edges.
    std::set<std::string> seen_edges;

    for (const TableauNode* state : state_nodes) {
        auto src_it = node_to_loc.find(state);
        if (src_it == node_to_loc.end()) continue;
        std::uint32_t src_loc = src_it->second;

        // Walk ALL children (including delay-successor children).
        for (const TableauNode* child : state->children) {
            if (child->status != NodeStatus::Open) continue;

            std::vector<DescendantInfo> descendants;
            find_descendant_states(
                child, state,
                /*resets=*/{}, /*extra_guards=*/{},
                /*cur_zone=*/state->zone,
                descendants);

            for (const auto& desc : descendants) {
                auto tgt_it = node_to_loc.find(desc.node);
                if (tgt_it == node_to_loc.end()) continue;
                std::uint32_t tgt_loc = tgt_it->second;

                TATransition trans;
                trans.source = src_loc;
                trans.target = tgt_loc;

                // ── 4.1 Guard from exit zone (after delay chain) ────
                const Zone& z = desc.exit_zone;
                if (!z.is_empty() && z.num_clocks() > 1) {
                    for (ClockId clk = 1;
                         clk < static_cast<ClockId>(z.num_clocks());
                         ++clk) {
                        // Upper bound:  x_clk ≤ c
                        Bound ub = z.get_bound(clk, kReferenceClock);
                        if (!ub.is_infinity()) {
                            TAConstraint c;
                            c.clock_x   = clk;
                            c.clock_y   = kReferenceClock;
                            c.bound     = ub.value;
                            c.is_strict = ub.is_strict;
                            c.is_upper  = true;
                            trans.guard.push_back(c);
                        }

                        // Lower bound:  x_0 − x_clk ≤ b  ⇒  x_clk ≥ −b
                        Bound lb = z.get_bound(kReferenceClock, clk);
                        if (!lb.is_infinity()) {
                            std::int32_t actual_lb = -lb.value;
                            if (actual_lb > 0 ||
                                (actual_lb == 0 && lb.is_strict)) {
                                TAConstraint c;
                                c.clock_x   = clk;
                                c.clock_y   = kReferenceClock;
                                c.bound     = actual_lb;
                                c.is_strict = lb.is_strict;
                                c.is_upper  = false;
                                trans.guard.push_back(c);
                            }
                        }
                    }
                }

                // Append timed-until discharge guard constraints.
                for (const auto& eg : desc.extra_guards)
                    trans.guard.push_back(eg);

                // ── 4.2 Resets ──────────────────────────────────────
                // Deduplicate resets.
                {
                    std::set<ClockId> seen_r(desc.resets.begin(),
                                             desc.resets.end());
                    trans.resets.assign(seen_r.begin(), seen_r.end());
                }

                // ── Edge deduplication ──────────────────────────────
                std::ostringstream ek;
                ek << src_loc << "->" << tgt_loc << "[";
                for (const auto& g : trans.guard)
                    ek << g.clock_x
                       << (g.is_upper ? "<=" : ">=")
                       << g.bound << g.is_strict << ",";
                ek << "]{";
                for (ClockId r : trans.resets) ek << r << ",";
                ek << "}";

                if (seen_edges.count(ek.str())) continue;
                seen_edges.insert(ek.str());

                ta.transitions.push_back(std::move(trans));
            }
        }
    }

    // ── 5. Initial location ─────────────────────────────────────────────
    //   Walk from root (depth==0) through expansion/delay to find the
    //   initial state node(s).

    // Helper: walk from a node to find first state-node descendants.
    // Differs from find_descendant_states in that it starts from the
    // root itself (which may already be a state node).
    std::function<void(const TableauNode*, std::set<std::uint32_t>&)>
    find_initial_locs =
        [&](const TableauNode* node, std::set<std::uint32_t>& locs)
    {
        if (node->status != NodeStatus::Open) return;
        if (is_state_node(node)) {
            auto it = node_to_loc.find(node);
            if (it != node_to_loc.end())
                locs.insert(it->second);
            return;
        }
        for (const TableauNode* child : node->children)
            find_initial_locs(child, locs);
    };

    std::set<std::uint32_t> initial_locs;
    for (const auto& np : engine.nodes()) {
        if (np->depth == 0 && np->status == NodeStatus::Open)
            find_initial_locs(np.get(), initial_locs);
    }

    if (initial_locs.size() == 1) {
        std::uint32_t init_id = *initial_locs.begin();
        ta.initial_location = init_id;
        ta.locations[init_id].is_initial = true;
    } else if (initial_locs.size() > 1) {
        // Multiple root states: create synthetic Init location with
        // urgent edges (guard=true, no resets) to each root location.
        std::uint32_t init_id = next_loc_id++;
        TALocation init_loc;
        init_loc.id         = init_id;
        init_loc.is_initial = true;
        ta.locations[init_id] = std::move(init_loc);
        ta.initial_location  = init_id;

        for (std::uint32_t lid : initial_locs) {
            TATransition t;
            t.source = init_id;
            t.target = lid;
            ta.transitions.push_back(std::move(t));
        }
    } else {
        // Fallback: use first location.
        if (!ta.locations.empty()) {
            auto it = ta.locations.begin();
            ta.initial_location = it->first;
            it->second.is_initial = true;
        }
    }

    // ── 6. Timed-until handling ─────────────────────────────────────────
    //   Already projected above:
    //     • Clock resets accumulated along expansion paths  (§4.2)
    //     • Interval discharge constraints in extra_guards  (§4.1)

    // ── 7. Prune unreachable locations by BFS from initial ──────────────

    {
        // Build adjacency from transitions.
        std::map<std::uint32_t, std::vector<std::uint32_t>> adj;
        for (const auto& t : ta.transitions)
            adj[t.source].push_back(t.target);

        std::set<std::uint32_t> reachable;
        std::vector<std::uint32_t> queue;
        reachable.insert(ta.initial_location);
        queue.push_back(ta.initial_location);

        while (!queue.empty()) {
            std::uint32_t cur = queue.back();
            queue.pop_back();
            auto ait = adj.find(cur);
            if (ait == adj.end()) continue;
            for (std::uint32_t nxt : ait->second) {
                if (reachable.insert(nxt).second)
                    queue.push_back(nxt);
            }
        }

        // Remove unreachable locations.
        std::vector<std::uint32_t> to_remove;
        for (const auto& [lid, loc] : ta.locations) {
            if (reachable.count(lid) == 0)
                to_remove.push_back(lid);
        }
        for (std::uint32_t lid : to_remove)
            ta.locations.erase(lid);

        // Remove transitions involving unreachable locations.
        ta.transitions.erase(
            std::remove_if(ta.transitions.begin(),
                           ta.transitions.end(),
                           [&reachable](const TATransition& t) {
                               return reachable.count(t.source) == 0 ||
                                      reachable.count(t.target) == 0;
                           }),
            ta.transitions.end());
    }

    // ── 8. Soundness checks ─────────────────────────────────────────────

    // 8a.  Remove locations backed by empty zones.
    {
        std::vector<std::uint32_t> to_remove;
        for (const auto& [lid, loc] : ta.locations) {
            auto zit = loc_zone.find(lid);
            if (zit != loc_zone.end() && zit->second.is_empty())
                to_remove.push_back(lid);
        }
        for (std::uint32_t lid : to_remove) {
            ta.locations.erase(lid);
            ta.transitions.erase(
                std::remove_if(ta.transitions.begin(),
                               ta.transitions.end(),
                               [lid](const TATransition& t) {
                                   return t.source == lid ||
                                          t.target == lid;
                               }),
                ta.transitions.end());
        }
    }

    // 8b.  Verify edge feasibility:
    //       post(Inv(l) ∧ Guard, Reset) ∩ Inv(l') ≠ ∅
    for (const auto& trans : ta.transitions) {
        auto src_zit = loc_zone.find(trans.source);
        auto tgt_zit = loc_zone.find(trans.target);
        if (src_zit == loc_zone.end() || tgt_zit == loc_zone.end())
            continue;

        Zone post = src_zit->second;
        post.up();  // time-closure for feasibility check
        for (ClockId r : trans.resets)
            post.reset(r);

        Zone inter = post.intersect(tgt_zit->second);
        if (inter.is_empty()) {
            std::cerr << "TA synthesis warning: edge L"
                      << trans.source << " -> L" << trans.target
                      << " infeasible after reset\n";
        }
    }

    // 8c.  Verify all invariants are consistent (zone non-empty).
    for (const auto& [lid, loc] : ta.locations) {
        auto zit = loc_zone.find(lid);
        if (zit != loc_zone.end() && zit->second.is_empty()) {
            std::cerr << "TA synthesis warning: location L"
                      << lid << " has empty invariant zone\n";
        }
    }

    return ta;
}

}  // namespace tctl
